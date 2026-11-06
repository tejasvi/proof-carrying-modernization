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
exports.runSelftest = runSelftest;
// `strictts-diff selftest`: runs the interface fixture (test/fixture/{old,new}/lib.ts), checks the
// result against the strictts-diff/v1 schema (validator in interface.ts, enums of
// schema/strictts-diff-v1.schema.json) and against the stable projection test/fixture/expected.json.
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const pipeline_1 = require("./pipeline");
const interface_1 = require("./interface");
const util_1 = require("./util");
const HERE = path.resolve(__dirname, '..');
async function runSelftest(opts) {
    const fx = path.join(HERE, 'test', 'fixture');
    const work = path.join(util_1.SCRATCH, `selftest-${(0, util_1.timestamp)()}-${process.pid}`);
    const errs = [];
    // 1. the schema file's enums agree with the validator
    const schema = JSON.parse(fs.readFileSync(path.join(HERE, 'schema', 'strictts-diff-v1.schema.json'), 'utf8'));
    const codes = schema.$defs?.reasonCode?.enum ?? [];
    if (JSON.stringify([...codes].sort()) !== JSON.stringify([...interface_1.REASON_CODES].sort()))
        errs.push('schema file: reasonCode enum differs from interface.ts REASON_CODES');
    const verdicts = schema.$defs?.function?.properties?.verdict?.enum ?? [];
    if (JSON.stringify(verdicts) !== JSON.stringify(['PROVED', 'REFUTED', 'REFUTED*', 'UNKNOWN', null]))
        errs.push('schema file: verdict enum differs');
    // 2. run the fixture
    const { reports } = await (0, pipeline_1.runPipeline)(path.join(fx, 'old', 'lib.ts'), path.join(fx, 'new', 'lib.ts'), { ...opts, work, only: undefined });
    const res = (0, interface_1.toResultV1)(reports, { old: 'old/lib.ts', new: 'new/lib.ts', seed: opts.seed, runs: opts.runs, lean: opts.lean, tactic: 'default', tacticWf: 'default' });
    (0, util_1.writeFile)(path.join(work, 'result.json'), JSON.stringify(res, null, 2) + '\n');
    for (const e of (0, interface_1.validateResultV1)(res))
        errs.push(`schema: ${e}`);
    // 3. the stable projection
    const exp = JSON.parse(fs.readFileSync(path.join(fx, 'expected.json'), 'utf8'));
    for (const [k, n] of Object.entries(exp.summary)) {
        const got = res.summary[k];
        if (got !== n)
            errs.push(`summary.${k}: expected ${n}, got ${got}`);
    }
    for (const ef of exp.functions) {
        const f = res.functions.find(x => x.key === ef.key);
        if (!f) {
            errs.push(`${ef.key}: missing`);
            continue;
        }
        if (f.status !== ef.status)
            errs.push(`${ef.key}: status ${f.status}, expected ${ef.status}`);
        if (f.verdict !== ef.verdict)
            errs.push(`${ef.key}: verdict ${f.verdict}, expected ${ef.verdict} (${f.reasons.join('; ').slice(0, 200)})`);
        if (ef.statement && f.proof?.statement !== ef.statement)
            errs.push(`${ef.key}: proof statement ${f.proof?.statement}, expected ${ef.statement}`);
        if (ef.leanConfirmed !== undefined && f.counterexample?.leanConfirmed !== ef.leanConfirmed)
            errs.push(`${ef.key}: leanConfirmed ${f.counterexample?.leanConfirmed}, expected ${ef.leanConfirmed}`);
        for (const d of ef.differs ?? [])
            if (!f.counterexample?.differs.includes(d))
                errs.push(`${ef.key}: counterexample should differ in ${d}`);
        for (const c of ef.reasonCodes ?? [])
            if (!f.reasonCodes.includes(c))
                errs.push(`${ef.key}: reason code ${c} missing (got ${f.reasonCodes.join(', ')})`);
    }
    const out = errs.length ? `selftest FAIL (${errs.length})\n${errs.map(e => '  ' + e).join('\n')}` : `selftest PASS: ${res.functions.length} functions, schema ${res.schema}, result ${path.join(work, 'result.json')}`;
    process.stdout.write(out + '\n');
    return errs.length ? 1 : 0;
}
