// TypeScript programs over materialized file sets (for function discovery, slicing and type
// descriptors). Library files are parsed once per process.
import * as path from 'path';
import * as ts from 'typescript';
import { FileSet } from './spec';

export interface Project {
  set: FileSet;
  program: ts.Program;
  checker: ts.TypeChecker;
  abs(rel: string): string;
  rel(abs: string): string;
  sf(rel: string): ts.SourceFile | undefined;
  isUser(sf: ts.SourceFile): boolean;
}

export const COMPILER_OPTIONS: ts.CompilerOptions = {
  target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler,
  lib: ['lib.es2023.d.ts'], types: [], allowImportingTsExtensions: true, noEmit: true, skipLibCheck: true,
  strict: true, jsx: ts.JsxEmit.Preserve, allowJs: false, resolveJsonModule: false,
};

const libCache = new Map<string, ts.SourceFile>();

export function cachingHost(options: ts.CompilerOptions): ts.CompilerHost {
  const host = ts.createCompilerHost(options, true);
  const orig = host.getSourceFile.bind(host);
  host.getSourceFile = (fileName, lang, onError, shouldCreate) => {
    const isLib = fileName.includes('/node_modules/typescript/lib/');
    if (isLib) {
      const key = fileName + '|' + JSON.stringify(lang);
      let sf = libCache.get(key);
      if (!sf) { sf = orig(fileName, lang, onError, shouldCreate); if (sf) libCache.set(key, sf); }
      return sf;
    }
    return orig(fileName, lang, onError, shouldCreate);
  };
  return host;
}

export function makeProject(set: FileSet, files?: string[]): Project {
  const roots = (files ?? set.files).map(f => path.join(set.dir, f));
  const program = ts.createProgram(roots, COMPILER_OPTIONS, cachingHost(COMPILER_OPTIONS));
  const checker = program.getTypeChecker();
  const dir = path.resolve(set.dir);
  return {
    set, program, checker,
    abs: rel => path.join(dir, rel),
    rel: abs => path.relative(dir, abs).split(path.sep).join('/'),
    sf: rel => program.getSourceFile(path.join(dir, rel)),
    isUser: sf => !sf.isDeclarationFile && path.resolve(sf.fileName).startsWith(dir + path.sep) && !sf.fileName.includes('/node_modules/'),
  };
}
