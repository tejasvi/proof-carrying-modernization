// Translator entry point: builds the TypeScript program, checks the subset, translates.
import * as ts from 'typescript';
import * as path from 'path';
import './core';
import './stmts';
import './exprs';
import './calls';
import './regex';
import './dict';
import './partial';
import './identity';
import './functions';
import { Translator } from './core';
import { Diags } from './diag';
import { checkSubset } from './check';
import { emitProgram } from './emit';
import { emitModular, ModularOptions, ModularResult } from './modular';

export interface Options {
  files: string[];
  project?: string;
  namespace?: string;
  eval?: boolean;
  abbreviate?: boolean;
  /** the original subset: no values of type unknown/any (`--strict`) */
  strict?: boolean;
  /** write one module per function instead of returning one file (see `modular.ts`) */
  modular?: ModularOptions;
  cwd: string;
}

export interface Result { ok: boolean; lean?: string; modular?: ModularResult; diagnostics: string; count: number }

export const ENV_DTS = path.join(__dirname, '..', 'lib', 'strictts-env.d.ts');

function strictOptions(o: ts.CompilerOptions): ts.CompilerOptions {
  return {
    ...o,
    strict: true, strictNullChecks: true, noImplicitAny: true, noImplicitThis: true, alwaysStrict: true,
    useUnknownInCatchVariables: true, noEmit: true, skipLibCheck: true, allowJs: false,
  };
}

export function translate(opts: Options): Result {
  let rootNames: string[];
  let options: ts.CompilerOptions;
  if (opts.project) {
    const cfg = ts.getParsedCommandLineOfConfigFile(opts.project, {}, {
      ...ts.sys, onUnRecoverableConfigFileDiagnostic: d => { throw new Error(ts.flattenDiagnosticMessageText(d.messageText, ' ')); },
    });
    if (!cfg) throw new Error(`cannot read ${opts.project}`);
    rootNames = [...cfg.fileNames, ...opts.files];
    options = strictOptions(cfg.options);
    const hasHost = (options.lib ?? []).some(l => /dom/i.test(l)) || (options.types ?? []).includes('node');
    if (!hasHost) { options.types = options.types ?? []; rootNames.push(ENV_DTS); }
  } else {
    rootNames = [...opts.files, ENV_DTS];
    options = strictOptions({
      target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler,
      lib: ['lib.es2023.d.ts'], types: [], allowImportingTsExtensions: true,
    });
  }
  const program = ts.createProgram(rootNames, options);
  const diags = new Diags(opts.cwd);
  for (const d of ts.getPreEmitDiagnostics(program)) diags.fromTs(d);
  if (diags.count) return { ok: false, diagnostics: diags.format(), count: diags.count };
  const userFiles = program.getSourceFiles().filter(sf =>
    !sf.isDeclarationFile && !program.isSourceFileDefaultLibrary(sf) && !sf.fileName.includes('/node_modules/'));
  checkSubset(program, userFiles, diags, !!opts.strict);
  const tr = new Translator(program, diags);
  tr.strict = !!opts.strict;
  for (const sf of userFiles) tr.projectFiles.add(sf);
  // roots in the order given on the command line, then the rest of the project
  const given = opts.files.map(f => path.resolve(opts.cwd, f));
  tr.files = [...userFiles].sort((a, b) => {
    const ia = given.indexOf(path.resolve(a.fileName)), ib = given.indexOf(path.resolve(b.fileName));
    return (ia < 0 ? 1e9 : ia) - (ib < 0 ? 1e9 : ib);
  });
  const pir = tr.translateProgram();
  if (!pir || diags.count) return { ok: false, diagnostics: diags.format(), count: diags.count };
  const first = opts.files[0] ?? opts.project ?? 'program';
  pir.namespace = opts.namespace ?? ('Prog_' + path.basename(first).replace(/\.(ts|tsx|json)$/, '').replace(/[^A-Za-z0-9_]/g, '_'));
  pir.sources = pir.sources.map(f => path.relative(opts.cwd, f));
  if (opts.modular) return { ok: true, modular: emitModular(pir, opts.modular), diagnostics: '', count: 0 };
  return { ok: true, lean: emitProgram(pir, { eval: opts.eval, abbreviate: opts.abbreviate }), diagnostics: '', count: 0 };
}
