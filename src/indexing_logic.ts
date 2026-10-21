import * as ts from "typescript";
import * as fs from "fs";
import { DatabaseSync } from "node:sqlite";
import SourcetrailDB, {
  FileBuilder,
  ReferenceKind,
  SymbolBuilder,
  SymbolKind
} from "sourcetraildb/dist/builder";

import * as path from "path";
import { normalizePath, combinePaths } from "./util/path";

// The following is only partially written and heavily inspired by https://github.com/Microsoft/TypeScript/wiki/Using-the-Compiler-API#a-minimal-compiler
// and https://github.com/microsoft/TypeScript/blob/38652d4cd7edcdc84580a09dd5e9b304f62a2f2b/scripts/buildProtocol.ts

/** Separates the elements of a Sourcetrail name hierarchy: file path parts, then the declaration's names. */
const NAME_DELIMITER = "/";

/**
 * Sourcetrail reads the project settings it stored in the database and compares them with the `.srctrlprj` file.
 * If they differ, it asks to reindex. The indexer therefore writes the same text to both places.
 */
const DEFAULT_PROJECT_SETTINGS = `<?xml version="1.0" encoding="utf-8" ?>
<config>
    <version>8</version>
</config>
`;

function isStringEnum(declaration: ts.EnumDeclaration) {
  return (
    declaration.members.length &&
    declaration.members.every(
      m => !!m.initializer && m.initializer.kind === ts.SyntaxKind.StringLiteral
    )
  );
}

const diagHost: ts.FormatDiagnosticsHost = {
  getCanonicalFileName(f) {
    return f;
  },
  getCurrentDirectory() {
    return ".";
  },
  getNewLine() {
    return "\r\n";
  }
};

/**
 * Report error and exit
 */
function reportUnrecoverableDiagnostic(diagnostic: ts.Diagnostic) {
  console.error(ts.formatDiagnostic(diagnostic, diagHost));
  ts.sys.exit(ts.ExitStatus.DiagnosticsPresent_OutputsSkipped);
}

/** Parses config file using System interface */
function parseConfigFile(
  configFileName: string,
  optionsToExtend: ts.CompilerOptions = {},
  system: ts.System = ts.sys
) {
  const host: ts.ParseConfigFileHost = <any>system;
  host.onUnRecoverableConfigFileDiagnostic = reportUnrecoverableDiagnostic;
  const result = ts.getParsedCommandLineOfConfigFile(
    configFileName,
    optionsToExtend,
    host
  );
  host.onUnRecoverableConfigFileDiagnostic = undefined!; // TODO: GH#18217
  return result;
}

function toSourceRange(
  file: FileBuilder,
  start: ts.LineAndCharacter,
  end: ts.LineAndCharacter
) {
  return file.at(
    start.line + 1,
    start.character + 1,
    end.line + 1,
    end.character
  );
}

function nodeToSourceRange(node: ts.Node, file: FileBuilder) {
  const start = node
    .getSourceFile()
    .getLineAndCharacterOfPosition(node.getStart());
  const end = node.getSourceFile().getLineAndCharacterOfPosition(node.getEnd());
  return toSourceRange(file, start, end);
}

function getLeadingCommentRangesOfNode(
  node: ts.Node,
  sourceFileOfNode: ts.SourceFile
) {
  return node.kind !== ts.SyntaxKind.JsxText
    ? ts.getLeadingCommentRanges(sourceFileOfNode.text, node.pos)
    : undefined;
}

const regionDelimiterRegExp = /^\s*\/\/\s*#(end)?region(?:\s+(.*))?(?:\r)?$/;
function isRegionDelimiter(lineText: string) {
  return regionDelimiterRegExp.exec(lineText);
}

function recordAtomicSourceRangesForMultilineComments(
  writer: SourcetrailDB,
  fileBuilder: FileBuilder,
  sourceFile: ts.SourceFile,
  n: ts.Node
): void {
  const comments = getLeadingCommentRangesOfNode(n, sourceFile);
  if (!comments) return;
  let firstSingleLineCommentStart = -1;
  let lastSingleLineCommentEnd = -1;
  let singleLineCommentCount = 0;
  const sourceText = sourceFile.getFullText();
  for (const { kind, pos, end } of comments) {
    switch (kind) {
      case ts.SyntaxKind.SingleLineCommentTrivia:
        // never fold region delimiters into single-line comment regions
        const commentText = sourceText.slice(pos, end);
        if (isRegionDelimiter(commentText)) {
          combineAndAddMultipleSingleLineComments();
          singleLineCommentCount = 0;
          break;
        }

        // For single line comments, combine consecutive ones (2 or more) into
        // a single span from the start of the first till the end of the last
        if (singleLineCommentCount === 0) {
          firstSingleLineCommentStart = pos;
        }
        lastSingleLineCommentEnd = end;
        singleLineCommentCount++;
        break;
      case ts.SyntaxKind.MultiLineCommentTrivia:
        combineAndAddMultipleSingleLineComments();
        const startLC = sourceFile.getLineAndCharacterOfPosition(pos);
        const endLC = sourceFile.getLineAndCharacterOfPosition(end);
        writer.recordAtomicSourceRange(
          toSourceRange(fileBuilder, startLC, endLC)
        );
        singleLineCommentCount = 0;
        break;
    }
  }
  combineAndAddMultipleSingleLineComments();

  function combineAndAddMultipleSingleLineComments(): void {
    // Only outline spans of two or more consecutive single line comments
    if (singleLineCommentCount > 1) {
      const startLC = sourceFile.getLineAndCharacterOfPosition(
        firstSingleLineCommentStart
      );
      const endLC = sourceFile.getLineAndCharacterOfPosition(
        lastSingleLineCommentEnd
      );
      writer.recordAtomicSourceRange(
        toSourceRange(fileBuilder, startLC, endLC)
      );
    }
  }
}

/** Declarations that have a name Sourcetrail can index. Anything else is skipped as a name. */
const NAMED_DECLARATION_KINDS = new Set<ts.SyntaxKind>([
  ts.SyntaxKind.ClassDeclaration,
  ts.SyntaxKind.InterfaceDeclaration,
  ts.SyntaxKind.EnumDeclaration,
  ts.SyntaxKind.EnumMember,
  ts.SyntaxKind.FunctionDeclaration,
  ts.SyntaxKind.MethodDeclaration,
  ts.SyntaxKind.MethodSignature,
  ts.SyntaxKind.Constructor,
  ts.SyntaxKind.GetAccessor,
  ts.SyntaxKind.SetAccessor,
  ts.SyntaxKind.PropertyDeclaration,
  ts.SyntaxKind.PropertySignature,
  ts.SyntaxKind.VariableDeclaration,
  ts.SyntaxKind.TypeAliasDeclaration,
  ts.SyntaxKind.ModuleDeclaration,
  ts.SyntaxKind.Parameter,
  ts.SyntaxKind.BindingElement,
  ts.SyntaxKind.TypeParameter
]);

/** The Sourcetrail kind of a declaration, or undefined when the declaration is not indexed as a symbol. */
function symbolKindOf(decl: ts.Node): number | undefined {
  switch (decl.kind) {
    case ts.SyntaxKind.ClassDeclaration:
      return SymbolKind.CLASS;
    case ts.SyntaxKind.InterfaceDeclaration:
      return SymbolKind.INTERFACE;
    case ts.SyntaxKind.TypeAliasDeclaration:
      return SymbolKind.TYPEDEF;
    case ts.SyntaxKind.EnumDeclaration:
      return SymbolKind.ENUM;
    case ts.SyntaxKind.EnumMember:
      return SymbolKind.ENUM_CONSTANT;
    case ts.SyntaxKind.ModuleDeclaration:
      return SymbolKind.NAMESPACE;
    case ts.SyntaxKind.FunctionDeclaration:
      return SymbolKind.FUNCTION;
    case ts.SyntaxKind.MethodDeclaration:
    case ts.SyntaxKind.MethodSignature:
    case ts.SyntaxKind.Constructor:
      return SymbolKind.METHOD;
    case ts.SyntaxKind.GetAccessor:
    case ts.SyntaxKind.SetAccessor:
    case ts.SyntaxKind.PropertySignature:
      return SymbolKind.FIELD;
    case ts.SyntaxKind.PropertyDeclaration:
      return isFunctionValue((decl as ts.PropertyDeclaration).initializer)
        ? SymbolKind.METHOD
        : SymbolKind.FIELD;
    case ts.SyntaxKind.VariableDeclaration:
      return isFunctionValue((decl as ts.VariableDeclaration).initializer)
        ? SymbolKind.FUNCTION
        : SymbolKind.GLOBAL_VARIABLE;
  }
  return undefined;
}

function isFunctionValue(init: ts.Expression | undefined): boolean {
  return (
    !!init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init))
  );
}

/** The name of a declaration as Sourcetrail sees it. Computed and destructuring names have none. */
function declarationName(node: ts.Node): string | undefined {
  if (node.kind === ts.SyntaxKind.Constructor) return "constructor";
  if (!NAMED_DECLARATION_KINDS.has(node.kind)) return undefined;
  const name = ts.getNameOfDeclaration(node as ts.Declaration);
  if (
    name &&
    (ts.isIdentifier(name) ||
      ts.isPrivateIdentifier(name) ||
      ts.isStringLiteral(name) ||
      ts.isNumericLiteral(name))
  ) {
    return name.text;
  }
  return undefined;
}

/** Whether a declaration sits in module or class scope, so it is a symbol other files can refer to. */
function isIndexedDeclaration(decl: ts.Node): boolean {
  if (symbolKindOf(decl) === undefined || declarationName(decl) === undefined) {
    return false;
  }
  if (ts.isVariableDeclaration(decl)) {
    return isIndexedScope(decl.parent.parent.parent);
  }
  return isIndexedScope(decl.parent);
}

function isIndexedScope(container: ts.Node): boolean {
  if (ts.isSourceFile(container)) return true;
  if (ts.isModuleBlock(container)) return isIndexedDeclaration(container.parent);
  if (
    ts.isClassDeclaration(container) ||
    ts.isInterfaceDeclaration(container) ||
    ts.isEnumDeclaration(container)
  ) {
    return isIndexedDeclaration(container);
  }
  return false;
}

/** The names from the outermost declaration down to this one, e.g. ["BudgetTab", "toggleGroup"]. */
function nameChain(decl: ts.Node): string[] {
  const names: string[] = [];
  for (let n: ts.Node | undefined = decl; n && !ts.isSourceFile(n); n = n.parent) {
    const name = declarationName(n);
    if (name !== undefined) names.unshift(name);
  }
  return names;
}

/** Nodes whose body is the context for the references inside them (the "caller" of an edge). */
function ownsContext(node: ts.Node): boolean {
  switch (node.kind) {
    case ts.SyntaxKind.ClassDeclaration:
    case ts.SyntaxKind.FunctionDeclaration:
    case ts.SyntaxKind.MethodDeclaration:
    case ts.SyntaxKind.Constructor:
    case ts.SyntaxKind.GetAccessor:
    case ts.SyntaxKind.SetAccessor:
      return true;
    case ts.SyntaxKind.PropertyDeclaration:
      return !!(node as ts.PropertyDeclaration).initializer;
    case ts.SyntaxKind.VariableDeclaration:
      return isFunctionValue((node as ts.VariableDeclaration).initializer);
  }
  return false;
}

/** Lowercase JSX tags such as `div` are HTML elements, not components. */
function isIntrinsicJsxTag(name: ts.JsxTagNameExpression): boolean {
  return ts.isIdentifier(name) && /^[a-z]/.test(name.text);
}

/** The deepest directory that contains every file, e.g. `/p/src` for `/p/src/a/x.ts` and `/p/src/y.ts`. */
function commonDirectory(files: readonly string[]): string {
  if (files.length === 0) return ts.sys.getCurrentDirectory();
  let common = path.dirname(files[0]).split(path.sep);
  for (const file of files.slice(1)) {
    const dir = path.dirname(file).split(path.sep);
    let i = 0;
    while (i < common.length && i < dir.length && common[i] === dir[i]) i++;
    common = common.slice(0, i);
  }
  return common.join(path.sep) || path.sep;
}

export class Indexing {
  private fileIds = new Map<string, FileBuilder>();
  private program: ts.Program;
  private checker: ts.TypeChecker;
  private host: ts.CompilerHost;
  private diagnostics: readonly ts.Diagnostic[];
  private projectDirectory: string;
  private writer!: SourcetrailDB;
  /** One Sourcetrail symbol per declaration node, so definitions and references share it. */
  private symbols = new Map<ts.Node, SymbolBuilder>();
  /** Enclosing symbols while walking a file. The bottom entry is the file's module symbol. */
  private contextStack: SymbolBuilder[] = [];
  private recordedCommentPositions = new Set<string>();
  public static verbose: boolean;

  private constructor(config: ts.ParsedCommandLine) {
    const { fileNames, options, projectReferences } = config;
    this.host = ts.createCompilerHost(options);
    const programOptions: ts.CreateProgramOptions = {
      rootNames: fileNames,
      options,
      projectReferences,
      host: this.host,
      configFileParsingDiagnostics: ts.getConfigFileParsingDiagnostics(config)
    };
    this.program = ts.createProgram(programOptions);
    this.checker = this.program.getTypeChecker();
    this.diagnostics = ts.getPreEmitDiagnostics(this.program);
    // Names are relative to the indexed files' common directory, so they do not depend on where the index is written.
    this.projectDirectory = commonDirectory(fileNames);
  }

  private addOrGetFile(
    writer: SourcetrailDB,
    file: ts.SourceFile
  ): FileBuilder {
    let fileId = this.fileIds.get(file.fileName);
    if (fileId !== undefined) {
      return fileId;
    }
    // otherwise, we haven't indexed this file yet...
    fileId = writer.createFile(file.fileName).asLanguage("typescript");
    this.fileIds.set(file.fileName, fileId);
    return fileId;
  }

  /** Declaration files and files from node_modules are referenced, but their definitions are not indexed. */
  private isExternal(sf: ts.SourceFile): boolean {
    return (
      sf.isDeclarationFile ||
      this.program.isSourceFileFromExternalLibrary(sf) ||
      sf.fileName.split(path.sep).includes("node_modules")
    );
  }

  private fileNameParts(sf: ts.SourceFile): string[] {
    const parts = path.relative(this.projectDirectory, sf.fileName).split(path.sep);
    // Dependencies outside the indexed directory are named from their node_modules folder, e.g. node_modules/preact/...
    const nodeModulesAt = sf.fileName.split(path.sep).lastIndexOf("node_modules");
    if (parts.includes("..") && nodeModulesAt >= 0) {
      return sf.fileName.split(path.sep).slice(nodeModulesAt).filter(part => part.length > 0);
    }
    return parts.filter(part => part.length > 0);
  }

  private addDiagnostics(writer: SourcetrailDB) {
    this.diagnostics.forEach(diagnostic => {
      const message = ts.flattenDiagnosticMessageText(
        diagnostic.messageText,
        "\n"
      );
      if (!diagnostic.file) {
        console.log(message);
        return;
      }
      const start = diagnostic.file.getLineAndCharacterOfPosition(
        diagnostic.start!
      );
      const end = diagnostic.file.getLineAndCharacterOfPosition(
        diagnostic.start! + diagnostic.length!
      );
      const sourceRange = this.addOrGetFile(writer, diagnostic.file).at(
        start.line + 1,
        start.character + 1,
        end.line + 1,
        end.character + 1
      );
      writer.recordError(message, sourceRange);
    });
  }

  private moduleSymbol(sf: ts.SourceFile, file: FileBuilder): SymbolBuilder {
    return this.writer
      .createSymbol(NAME_DELIMITER, this.fileNameParts(sf))
      .explicitly()
      .ofType(SymbolKind.MODULE)
      .withScope(nodeToSourceRange(sf, file));
  }

  /**
   * The Sourcetrail symbol for a declaration. For a declaration in an indexed file this also records its
   * definition, once. Returns undefined for declarations that are not symbols (locals, parameters).
   */
  private symbolFor(decl: ts.Node): SymbolBuilder | undefined {
    const cached = this.symbols.get(decl);
    if (cached) return cached;

    const sf = decl.getSourceFile();
    const external = this.isExternal(sf);
    if (!external && !isIndexedDeclaration(decl)) return undefined;

    const names = [...this.fileNameParts(sf), ...nameChain(decl)];
    const symbol = this.writer.createSymbol(NAME_DELIMITER, names);
    this.symbols.set(decl, symbol);

    const kind = symbolKindOf(decl);
    if (kind !== undefined) {
      symbol.ofType(kind);
    }
    if (!external) {
      const file = this.addOrGetFile(this.writer, sf);
      const nameNode = ts.getNameOfDeclaration(decl as ts.Declaration) ?? decl;
      symbol
        .explicitly()
        .atLocation(nodeToSourceRange(nameNode, file))
        .withSignature(nodeToSourceRange(decl, file));
    }
    return symbol;
  }

  /** The declaration an identifier refers to, following imports and re-exports through barrel files. */
  private resolve(id: ts.Identifier): ts.Declaration | undefined {
    const parent = id.parent;
    let symbol: ts.Symbol | undefined =
      ts.isShorthandPropertyAssignment(parent) && parent.name === id
        ? this.checker.getShorthandAssignmentValueSymbol(parent)
        : this.checker.getSymbolAtLocation(id);
    while (symbol && symbol.flags & ts.SymbolFlags.Alias) {
      symbol = this.checker.getAliasedSymbol(symbol);
    }
    const declarations = symbol?.declarations;
    if (!declarations || declarations.length === 0) return undefined;
    return (
      declarations.find(d => !this.isExternal(d.getSourceFile())) ??
      declarations[0]
    );
  }

  /** The reference kind of an identifier, or undefined when the identifier is not a reference. */
  private referenceKindOf(id: ts.Identifier): number | undefined {
    const parent = id.parent;
    if (
      ts.isImportSpecifier(parent) ||
      ts.isImportClause(parent) ||
      ts.isNamespaceImport(parent)
    ) {
      return ReferenceKind.IMPORT;
    }
    if (ts.isExportSpecifier(parent) || ts.isJsxAttribute(parent)) {
      return undefined;
    }
    if (ts.isPropertyAssignment(parent) && parent.name === id) {
      return undefined;
    }
    if (
      NAMED_DECLARATION_KINDS.has(parent.kind) &&
      ts.getNameOfDeclaration(parent as ts.Declaration) === id
    ) {
      return undefined;
    }
    if (
      ts.isExpressionWithTypeArguments(parent) &&
      ts.isHeritageClause(parent.parent)
    ) {
      return ReferenceKind.INHERITANCE;
    }
    if (
      ts.isTypeReferenceNode(parent) ||
      (ts.isQualifiedName(parent) && ts.isTypeReferenceNode(parent.parent))
    ) {
      return ReferenceKind.TYPE_USAGE;
    }
    if (
      ((ts.isCallExpression(parent) || ts.isNewExpression(parent)) &&
        parent.expression === id) ||
      (ts.isPropertyAccessExpression(parent) &&
        parent.name === id &&
        ts.isCallExpression(parent.parent) &&
        parent.parent.expression === parent)
    ) {
      return ReferenceKind.CALL;
    }
    return ReferenceKind.USAGE;
  }

  private recordIdentifier(id: ts.Identifier, file: FileBuilder) {
    const kind = this.referenceKindOf(id);
    if (kind === undefined) return;

    const parent = id.parent;
    const isJsxTag =
      (ts.isJsxOpeningElement(parent) || ts.isJsxSelfClosingElement(parent)) &&
      parent.tagName === id;
    if (isJsxTag && isIntrinsicJsxTag(id)) return;

    const context = this.contextStack[this.contextStack.length - 1];
    const location = nodeToSourceRange(id, file);
    const decl = this.resolve(id);
    if (!decl) {
      // Only calls and JSX components are worth showing as unsolved. Other unresolved names are usually
      // globals or dynamic code.
      if (kind === ReferenceKind.CALL || isJsxTag) {
        this.writer.createUnsolvedReference(context, kind, location);
      }
      return;
    }

    // References to TypeScript's built-in library (Math, Map, Promise) would only add noise to the graph.
    if (this.program.isSourceFileDefaultLibrary(decl.getSourceFile())) return;

    const target = this.symbolFor(decl);
    if (!target) return;
    this.writer.createReference(context, target, kind).atLocation(location);
  }

  private visitNode(node: ts.Node, sf: ts.SourceFile, file: FileBuilder): void {
    // Leading comments are shared by every node that starts at the same position, so record them once.
    const commentKey = `${sf.fileName}:${node.pos}`;
    if (!this.recordedCommentPositions.has(commentKey)) {
      this.recordedCommentPositions.add(commentKey);
      recordAtomicSourceRangesForMultilineComments(this.writer, file, sf, node);
    }

    if (isIndexedDeclaration(node)) {
      this.symbolFor(node);
    }

    if (ts.isIdentifier(node)) {
      this.recordIdentifier(node, file);
    }

    const pushesContext = ownsContext(node) ? this.symbolFor(node) : undefined;
    if (pushesContext) this.contextStack.push(pushesContext);
    ts.forEachChild(node, child => this.visitNode(child, sf, file));
    if (pushesContext) this.contextStack.pop();
  }

  private indexSourceFile(sf: ts.SourceFile) {
    const file = this.addOrGetFile(this.writer, sf);
    this.contextStack = [this.moduleSymbol(sf, file)];
    this.visitNode(sf, sf, file);
    this.contextStack = [];
  }

  static IndexFile(
    databaseFilePath: string,
    filename: string,
    clear: boolean
  ): void {
    Indexing.PerformIndexing(
      databaseFilePath,
      {
        fileNames: [filename],
        options: {},
        errors: []
      },
      clear
    );
  }

  static IndexProject(
    databaseFilePath: string,
    projectPath: string | undefined,
    clear: boolean
  ): void {
    let configFileName: string | undefined;
    if (projectPath === undefined) {
      const currentDirectory = ts.sys.getCurrentDirectory();
      const searchPath = normalizePath(currentDirectory);
      configFileName = ts.findConfigFile(searchPath, ts.sys.fileExists);
      if (configFileName === undefined) {
        console.error(
          "Cannot find a tsconfig.json file at the specified directory: ",
          currentDirectory
        );
        return ts.sys.exit(ts.ExitStatus.DiagnosticsPresent_OutputsSkipped);
      }
    } else {
      const fileOrDirectory = normalizePath(projectPath);
      if (
        !fileOrDirectory /* "." */ ||
        ts.sys.directoryExists(fileOrDirectory)
      ) {
        configFileName = combinePaths(fileOrDirectory, "tsconfig.json");
        if (!ts.sys.fileExists(configFileName)) {
          console.error(
            "Cannot find a tsconfig.json file at the specified directory: ",
            projectPath
          );
          return ts.sys.exit(ts.ExitStatus.DiagnosticsPresent_OutputsSkipped);
        }
      } else {
        configFileName = fileOrDirectory;
        if (!ts.sys.fileExists(configFileName)) {
          if (!ts.sys.fileExists(configFileName)) {
            console.error("The specified path does not exist: ", projectPath);
            return ts.sys.exit(ts.ExitStatus.DiagnosticsPresent_OutputsSkipped);
          }
        }
      }
    }
    const config = parseConfigFile(configFileName);
    if (config.errors.length > 0) {
      config.errors.forEach(diagnostic =>
        console.error(ts.formatDiagnostic(diagnostic, diagHost))
      );
      ts.sys.exit(ts.ExitStatus.DiagnosticsPresent_OutputsSkipped);
    }
    Indexing.PerformIndexing(databaseFilePath, config, clear);
  }

  static PerformIndexing(
    databaseFilePath: string,
    config: ts.ParsedCommandLine,
    clear: boolean
  ): void {
    const indexer = new Indexing(config);
    SourcetrailDB.open(
      databaseFilePath,
      writer => {
        indexer.writer = writer;
        indexer.addDiagnostics(writer);
        indexer.program
          .getSourceFiles()
          .filter(sf => !indexer.isExternal(sf))
          .forEach(sf => indexer.indexSourceFile(sf));
      },
      clear
    );
    writeProjectSettings(databaseFilePath);
  }
}

/**
 * Makes the `.srctrlprj` beside the database match the database's stored project settings, so Sourcetrail opens
 * the pair without asking to reindex.
 *
 * The SourcetrailDB writer creates a minimal `.srctrlprj` (version 0, no source groups) when the database is
 * opened. That file is replaced with the default settings. A project file that has source groups belongs to the
 * user and is kept as it is.
 */
function writeProjectSettings(databaseFilePath: string): void {
  const projectFilePath = databaseFilePath.replace(/\.srctrldb$/, ".srctrlprj");
  if (projectFilePath === databaseFilePath) {
    return;
  }
  const existing = fs.existsSync(projectFilePath)
    ? fs.readFileSync(projectFilePath, "utf8")
    : undefined;
  const settingsText =
    existing !== undefined && existing.includes("<source_groups>")
      ? existing
      : DEFAULT_PROJECT_SETTINGS;
  if (settingsText !== existing) {
    fs.writeFileSync(projectFilePath, settingsText);
  }
  const db = new DatabaseSync(databaseFilePath);
  try {
    db.exec("BEGIN");
    db.prepare("DELETE FROM meta WHERE key = 'project_settings'").run();
    db.prepare("INSERT INTO meta (key, value) VALUES ('project_settings', ?)").run(settingsText);
    db.exec("COMMIT");
  } finally {
    db.close();
  }
}
