#!/usr/bin/env node
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
// Command line: node frontend/dist/cli.js [-p tsconfig.json] [-o out.lean | --modular OUTDIR] [--namespace N] [--eval] [--check] files...
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const index_1 = require("./index");
const modular_1 = require("./modular");
const coverage_1 = require("./coverage");
function usage() {
    process.stderr.write(`usage: strictts [-p tsconfig.json] [-o out.lean | --modular OUTDIR] [--namespace Name] [--eval] [--check] [file.ts ...]
  Checks that the program is in the StrictTS subset and translates it to Lean 4 IR terms.
  -p, --project   translate a tsconfig project (whole program)
  -o, --out       output file (default: stdout)
  --modular OUTDIR
                  one Lean module per function under OUTDIR/<Namespace>/ (Types, Refs/<f>, Globals/<g>,
                  Externs/<e>, Defs/<f>, Program), for incremental proofs; files are written only when they change
  --index-map FILE.json
                  stable function indices for --modular (read if present, rewritten; default
                  OUTDIR/<Namespace>/index.json): existing names keep their index, new ones are appended
  --namespace     Lean namespace of the generated definitions (default Prog_<file>)
  --eval          append '#eval runMain <namespace>.program' (differential testing)
  --check         only check the subset rules; no output
  --abbrev-types  name large types that occur repeatedly (abbrev ... : Ty)
  --strict, --no-dyn
                  the original subset: unknown and any are rejected (no dyn values); also in
                  coverage mode
  --coverage -p tsconfig.json --report OUT.json [--only-dir DIR] [--label NAME] [--emit-lean OUT.lean]
             [--no-emit-generics]
                  per-function subset coverage of a project (read-only; see src/coverage.ts);
                  --emit-lean: one Lean module with the IR of the covered functions (src/partial.ts),
                  the generic ones at one instance (each type parameter := number; string for
                  extends PropertyKey / string), unless --no-emit-generics
  --combine A.json --combine B.json [--report OUT.json]
                  combined summary of coverage reports
Exit status: 0 = translated, 1 = subset violations (diagnostics on stderr), 2 = usage/internal error.
`);
    process.exit(2);
}
function main() {
    const argv = process.argv.slice(2);
    const files = [];
    let out, project, namespace;
    let modular, indexMap;
    let evalFlag = false, check = false, abbreviate = false, coverage = false;
    let report, label, emitLean;
    let emitGenerics;
    let strict = false;
    const onlyDirs = [];
    const combine = [];
    for (let i = 0; i < argv.length; i++) {
        const a = argv[i];
        if (a === '-o' || a === '--out')
            out = argv[++i];
        else if (a === '-p' || a === '--project')
            project = argv[++i];
        else if (a === '--namespace')
            namespace = argv[++i];
        else if (a === '--modular')
            modular = argv[++i];
        else if (a === '--index-map')
            indexMap = argv[++i];
        else if (a === '--eval')
            evalFlag = true;
        else if (a === '--check')
            check = true;
        else if (a === '--abbrev-types')
            abbreviate = true;
        else if (a === '--coverage')
            coverage = true;
        else if (a === '--report')
            report = argv[++i];
        else if (a === '--only-dir')
            onlyDirs.push(argv[++i]);
        else if (a === '--label')
            label = argv[++i];
        else if (a === '--combine')
            combine.push(argv[++i]);
        else if (a === '--emit-lean')
            emitLean = argv[++i];
        else if (a === '--emit-generics') {
            if (argv[++i] !== 'number')
                usage();
            emitGenerics = 'number';
        }
        else if (a === '--no-emit-generics')
            emitGenerics = false;
        else if (a === '--strict' || a === '--no-dyn')
            strict = true;
        else if (a === '-h' || a === '--help')
            usage();
        else if (a.startsWith('-'))
            usage();
        else
            files.push(a);
    }
    if (combine.length) {
        const rows = [];
        for (const f of combine)
            rows.push(...JSON.parse(fs.readFileSync(f, 'utf8')).rows);
        const s = (0, coverage_1.summarize)(rows, label ?? 'combined');
        if (report)
            fs.writeFileSync(report, JSON.stringify({ summary: s }, null, 1));
        process.stdout.write((0, coverage_1.formatSummary)(s) + '\n');
        return;
    }
    if (coverage) {
        if (!project)
            usage();
        const res = (0, coverage_1.runCoverage)({ project, cwd: process.cwd(), onlyDirs: onlyDirs.length ? onlyDirs : undefined, label, emitLean, emitGenerics, strict });
        if (report)
            (0, coverage_1.writeReport)(report, res);
        process.stdout.write((0, coverage_1.formatSummary)(res.summary) + '\n');
        if (res.emit) {
            const e = res.emit;
            process.stdout.write(`== emit-lean ${e.file}: ${e.unitsEmitted}/${e.units} covered units, ${e.funs} functions, ${e.globals} module variables ` +
                `(${e.globalsUninitialised} uninitialised), ${e.lines} lines, ${e.bytes} bytes; left out: ${e.funsFailed} failed, ${e.funsDropped} needing them (${e.secs.toFixed(1)} s)\n`);
            if (process.env.STRICTTS_EMIT_FAILURES)
                for (const f of e.failures)
                    process.stdout.write(`   ${f}\n`);
        }
        return;
    }
    if (!files.length && !project)
        usage();
    if (modular !== undefined && (out !== undefined || abbreviate || !modular))
        usage();
    if (indexMap !== undefined && modular === undefined)
        usage();
    if (modular && namespace !== undefined && !(0, modular_1.validNamespace)(namespace)) {
        process.stderr.write(`--namespace ${namespace}: expected dot-separated Lean identifiers\n`);
        process.exit(2);
    }
    const r = (0, index_1.translate)({
        files, project, namespace, eval: evalFlag, abbreviate, strict, cwd: process.cwd(),
        modular: modular && !check ? { outDir: modular, indexMap, eval: evalFlag } : undefined,
    });
    if (!r.ok) {
        process.stderr.write(r.diagnostics + '\n');
        process.stderr.write(`${r.count} StrictTS diagnostic(s); nothing translated.\n`);
        process.exit(1);
    }
    if (check)
        return;
    if (r.modular) {
        const m = r.modular;
        process.stdout.write(`${path.relative(process.cwd(), m.dir) || '.'}: ${m.modules} modules, ${m.written.length} written, ` +
            `${m.deleted.length} deleted; index map ${path.relative(process.cwd(), m.indexMap)}\n`);
        for (const f of m.written)
            process.stdout.write(`  wrote ${path.relative(process.cwd(), f)}\n`);
        for (const f of m.deleted)
            process.stdout.write(`  deleted ${path.relative(process.cwd(), f)}\n`);
        return;
    }
    if (out) {
        fs.mkdirSync(path.dirname(path.resolve(out)), { recursive: true });
        fs.writeFileSync(out, r.lean);
    }
    else
        process.stdout.write(r.lean);
}
try {
    main();
}
catch (e) {
    if (e instanceof modular_1.ModularError) {
        process.stderr.write(`error: ${e.message}\n`);
        process.exit(2);
    }
    process.stderr.write(`internal error: ${e.stack ?? e}\n`);
    process.exit(2);
}
