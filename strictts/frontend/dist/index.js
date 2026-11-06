"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.ENV_DTS = void 0;
exports.translate = translate;
// Translator entry point: builds the TypeScript program, checks the subset, translates.
const ts = __importStar(require("typescript"));
const path = __importStar(require("path"));
require("./core");
require("./stmts");
require("./exprs");
require("./calls");
require("./regex");
require("./dict");
require("./partial");
require("./identity");
require("./functions");
const core_1 = require("./core");
const diag_1 = require("./diag");
const check_1 = require("./check");
const emit_1 = require("./emit");
const modular_1 = require("./modular");
exports.ENV_DTS = path.join(__dirname, '..', 'lib', 'strictts-env.d.ts');
function strictOptions(o) {
    return {
        ...o,
        strict: true, strictNullChecks: true, noImplicitAny: true, noImplicitThis: true, alwaysStrict: true,
        useUnknownInCatchVariables: true, noEmit: true, skipLibCheck: true, allowJs: false,
    };
}
function translate(opts) {
    let rootNames;
    let options;
    if (opts.project) {
        const cfg = ts.getParsedCommandLineOfConfigFile(opts.project, {}, {
            ...ts.sys, onUnRecoverableConfigFileDiagnostic: d => { throw new Error(ts.flattenDiagnosticMessageText(d.messageText, ' ')); },
        });
        if (!cfg)
            throw new Error(`cannot read ${opts.project}`);
        rootNames = [...cfg.fileNames, ...opts.files];
        options = strictOptions(cfg.options);
        const hasHost = (options.lib ?? []).some(l => /dom/i.test(l)) || (options.types ?? []).includes('node');
        if (!hasHost) {
            options.types = options.types ?? [];
            rootNames.push(exports.ENV_DTS);
        }
    }
    else {
        rootNames = [...opts.files, exports.ENV_DTS];
        options = strictOptions({
            target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler,
            lib: ['lib.es2023.d.ts'], types: [], allowImportingTsExtensions: true,
        });
    }
    const program = ts.createProgram(rootNames, options);
    const diags = new diag_1.Diags(opts.cwd);
    for (const d of ts.getPreEmitDiagnostics(program))
        diags.fromTs(d);
    if (diags.count)
        return { ok: false, diagnostics: diags.format(), count: diags.count };
    const userFiles = program.getSourceFiles().filter(sf => !sf.isDeclarationFile && !program.isSourceFileDefaultLibrary(sf) && !sf.fileName.includes('/node_modules/'));
    (0, check_1.checkSubset)(program, userFiles, diags, !!opts.strict);
    const tr = new core_1.Translator(program, diags);
    tr.strict = !!opts.strict;
    for (const sf of userFiles)
        tr.projectFiles.add(sf);
    // roots in the order given on the command line, then the rest of the project
    const given = opts.files.map(f => path.resolve(opts.cwd, f));
    tr.files = [...userFiles].sort((a, b) => {
        const ia = given.indexOf(path.resolve(a.fileName)), ib = given.indexOf(path.resolve(b.fileName));
        return (ia < 0 ? 1e9 : ia) - (ib < 0 ? 1e9 : ib);
    });
    const pir = tr.translateProgram();
    if (!pir || diags.count)
        return { ok: false, diagnostics: diags.format(), count: diags.count };
    const first = opts.files[0] ?? opts.project ?? 'program';
    pir.namespace = opts.namespace ?? ('Prog_' + path.basename(first).replace(/\.(ts|tsx|json)$/, '').replace(/[^A-Za-z0-9_]/g, '_'));
    pir.sources = pir.sources.map(f => path.relative(opts.cwd, f));
    if (opts.modular)
        return { ok: true, modular: (0, modular_1.emitModular)(pir, opts.modular), diagnostics: '', count: 0 };
    return { ok: true, lean: (0, emit_1.emitProgram)(pir, { eval: opts.eval, abbreviate: opts.abbreviate }), diagnostics: '', count: 0 };
}
