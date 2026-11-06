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
exports.summarize = summarize;
exports.runCoverage = runCoverage;
exports.writeReport = writeReport;
exports.formatSummary = formatSummary;
// Coverage mode: how much of a real project fits StrictTS, function by function.
//
// For every top-level function, class method/accessor/constructor, module-level
// `const f = (...) => ...` and handler arrow passed to a module-level call (e.g.
// `export const x = onRequest(async (req, res) => ...)`), the function is translated on its
// own with its signature types. Calls of other project functions are assumed fine; uses of
// package / host APIs outside the modelled library are `external-call`; object types of
// packages / the host are `external-type`. A file with TypeScript errors counts as `ts-error`.
//
// The analysis only reads the project: the TypeScript program is created with noEmit.
const ts = __importStar(require("typescript"));
const path = __importStar(require("path"));
const fs = __importStar(require("fs"));
const core_1 = require("./core");
const diag_1 = require("./diag");
const ty_1 = require("./ty");
const ir_1 = require("./ir");
const check_1 = require("./check");
const exprs_1 = require("./exprs");
const stmts_1 = require("./stmts");
require("./partial");
require("./identity");
const emit_1 = require("./emit");
function loc(node, sf) {
    return node.getText(sf).split('\n').filter(l => l.trim() !== '').length;
}
function where(n, root) {
    if (!n)
        return '?';
    const sf = n.getSourceFile();
    const p = sf.getLineAndCharacterOfPosition(n.getStart(sf));
    return `${path.relative(root, sf.fileName)}:${p.line + 1}:${p.character + 1}`;
}
function collectUnits(sf) {
    const units = [];
    const memberName = (m) => m.name && (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name) || ts.isStringLiteral(m.name)) ? m.name.text : '<computed>';
    const unwrap = (e) => {
        while (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e) || ts.isTypeAssertionExpression(e))
            e = e.expression;
        return e;
    };
    for (const st of sf.statements) {
        if (ts.isFunctionDeclaration(st) && st.body)
            units.push({ file: sf, name: st.name?.text ?? 'default', kind: 'function', node: st });
        else if (ts.isClassDeclaration(st)) {
            const cname = st.name?.text ?? 'default';
            for (const m of st.members) {
                const isStatic = !!ts.getModifiers(m)?.some(x => x.kind === ts.SyntaxKind.StaticKeyword);
                if (ts.isConstructorDeclaration(m) && m.body)
                    units.push({ file: sf, name: `${cname}.constructor`, kind: 'constructor', node: m, cls: st });
                else if (ts.isMethodDeclaration(m) && m.body)
                    units.push({ file: sf, name: `${cname}.${memberName(m)}`, kind: 'method', node: m, cls: st, isStatic });
                else if ((ts.isGetAccessorDeclaration(m) || ts.isSetAccessorDeclaration(m)) && m.body) {
                    units.push({ file: sf, name: `${cname}.${ts.isGetAccessorDeclaration(m) ? 'get' : 'set'} ${memberName(m)}`, kind: 'accessor', node: m, cls: st, isStatic });
                }
            }
        }
        else if (ts.isVariableStatement(st)) {
            for (const d of st.declarationList.declarations) {
                if (!d.initializer || !ts.isIdentifier(d.name))
                    continue;
                const init = unwrap(d.initializer);
                if (ts.isArrowFunction(init) || ts.isFunctionExpression(init))
                    units.push({ file: sf, name: d.name.text, kind: 'arrow', node: init });
                else if (ts.isCallExpression(init)) {
                    init.arguments.forEach((a, i) => {
                        const x = unwrap(a);
                        if (ts.isArrowFunction(x) || ts.isFunctionExpression(x))
                            units.push({ file: sf, name: `${d.name.getText(sf)}/arg${i}`, kind: 'handler', node: x });
                    });
                }
            }
        }
        else if (ts.isExportAssignment(st)) {
            const x = unwrap(st.expression);
            if (ts.isArrowFunction(x) || ts.isFunctionExpression(x))
                units.push({ file: sf, name: 'default', kind: 'arrow', node: x });
        }
    }
    return units;
}
/** Stand-in for a type parameter: its constraint, or an opaque object type. */
function standIn(tr, tp, subst) {
    if (tp.constraint) {
        try {
            return tr.types.map(tr.checker.getTypeAtLocation(tp.constraint), subst, tp);
        }
        catch { /* fall through */ }
    }
    const c = `${tp.name.text}$param`;
    if (!tr.types.classFields.has(c))
        tr.types.classFields.set(c, []);
    return ty_1.T.obj(c);
}
function coverParams(tr, decl, fc, out) {
    for (const p of decl.parameters) {
        if (ts.isIdentifier(p.name) && p.name.text === 'this')
            continue;
        if (ts.isIdentifier(p.name)) {
            const sym = tr.symAt(p.name);
            if (!sym)
                continue;
            try {
                const inner = tr.tyOf(tr.checker.getTypeOfSymbol(sym), fc, p);
                let outer = inner;
                if ((p.questionToken || p.initializer) && !p.dotDotDotToken && outer.k !== 'opt')
                    outer = ty_1.T.opt(outer);
                const v = (0, ir_1.mkVar)(p.name.text, outer, tr.isReassigned(sym));
                if (p.initializer && outer.k === 'opt') {
                    const d = tr.lowerExpr(p.initializer, fc, inner);
                    const y = (0, ir_1.mkVar)(p.name.text, outer.t);
                    tr.declareLocal(sym, p.name.text, inner, ir_1.E.caseOpt(ir_1.E.var(v), d, y, tr.coerce(ir_1.E.var(y), inner, p)), fc, out);
                }
                else if (tr.needsBox(sym))
                    tr.declareLocal(sym, p.name.text, inner, ir_1.E.var(v), fc, out);
                else
                    fc.bind(sym, { k: 'var', v });
            }
            catch (e) {
                if ((0, exprs_1.isFatal)(e))
                    throw e;
                tr.covRecord(e, p);
                tr.poisonCount++;
                fc.bind(sym, { k: 'poison', ty: ty_1.T.undef });
            }
        }
        else {
            try {
                const t = tr.tyAt(p, fc);
                const v = (0, ir_1.mkVar)('p', t);
                tr.bindPattern(p.name, ir_1.E.var(v), fc, out, true);
            }
            catch (e) {
                if ((0, exprs_1.isFatal)(e))
                    throw e;
                tr.covRecord(e, p);
                tr.poisonCount++;
                (0, stmts_1.bindPatternPoison)(tr, p.name, fc);
            }
        }
    }
}
function coverUnit(tr, u) {
    const decl = u.node;
    const subst = new Map();
    for (const tp of [...(u.cls?.typeParameters ?? []), ...(decl.typeParameters ?? [])]) {
        subst.set(tr.checker.getTypeAtLocation(tp), standIn(tr, tp, subst));
    }
    const async = tr.isAsync(decl);
    const fc = new core_1.FnCtx(null, 'fun', async, ty_1.T.undef, subst, decl);
    const items = [];
    fc.pre = items;
    const guard = (f, node) => {
        try {
            f();
        }
        catch (e) {
            if ((0, exprs_1.isFatal)(e))
                throw e;
            tr.covRecord(e, node);
            tr.poisonCount++;
        }
    };
    // `this`
    let thisCls;
    if (u.cls && !u.isStatic) {
        guard(() => {
            const csym = tr.checker.getSymbolAtLocation(u.cls.name ?? u.cls);
            const ct = csym ? tr.checker.getDeclaredTypeOfSymbol(csym) : tr.checker.getTypeAtLocation(u.cls);
            const ci = tr.types.classInst(ct, subst, u.cls);
            thisCls = ci.name;
            fc.thisVar = (0, ir_1.mkVar)('this', ty_1.T.obj(ci.name));
        }, u.cls);
        if (!thisCls)
            fc.thisPoison = true;
    }
    // return type
    if (u.kind === 'constructor') {
        fc.isCtor = true;
        if (thisCls)
            fc.bodyRet = ty_1.T.obj(thisCls);
        else
            fc.retPoison = true;
    }
    else {
        let ok = false;
        guard(() => { fc.bodyRet = tr.returnTy(decl, subst, async); ok = true; }, decl.type ?? decl);
        if (!ok)
            fc.retPoison = true;
    }
    coverParams(tr, decl, fc, items);
    if (u.kind === 'constructor' && u.cls) {
        // field initialisers run as part of construction
        for (const m of u.cls.members) {
            if (ts.isPropertyDeclaration(m) && m.initializer && !ts.getModifiers(m)?.some(x => x.kind === ts.SyntaxKind.StaticKeyword)) {
                guard(() => { tr.lowerExpr(m.initializer, fc); }, m);
            }
        }
    }
    const body = decl.body;
    if (body) {
        if (ts.isBlock(body))
            guard(() => { items.push(...tr.lowerBlockStmts(body.statements, fc)); }, body);
        else
            guard(() => { tr.lowerConciseBody(body, fc, items); }, body);
    }
    void ir_1.S;
    void ir_1.stmtItem;
}
function summarize(rows, label) {
    const analyzed = rows.filter(r => r.status !== 'ts-error');
    const fnCovered = rows.filter(r => r.status === 'covered');
    const ruleFns = new Map(), ruleOnly = new Map(), ruleOcc = new Map();
    for (const r of analyzed) {
        const rules = Object.keys(r.rules);
        for (const k of rules) {
            ruleFns.set(k, (ruleFns.get(k) ?? 0) + 1);
            ruleOcc.set(k, (ruleOcc.get(k) ?? 0) + r.rules[k]);
        }
        if (rules.length === 1)
            ruleOnly.set(rules[0], (ruleOnly.get(rules[0]) ?? 0) + 1);
    }
    const ext = new Map(), extT = new Map();
    for (const r of analyzed) {
        for (const x of new Set(r.externals))
            ext.set(x, (ext.get(x) ?? 0) + 1);
        for (const x of new Set(r.externalTypes))
            extT.set(x, (extT.get(x) ?? 0) + 1);
    }
    const byKind = {};
    for (const r of rows) {
        byKind[r.kind] ??= { covered: 0, total: 0 };
        byKind[r.kind].total++;
        if (r.status === 'covered')
            byKind[r.kind].covered++;
    }
    const onlyExternal = analyzed.filter(r => Object.keys(r.rules).length > 0 && Object.keys(r.rules).every(k => k === 'external-call' || k === 'external-type')).length;
    return {
        label,
        functions: { covered: fnCovered.length, total: rows.length, tsError: rows.length - analyzed.length },
        loc: { covered: fnCovered.reduce((a, r) => a + r.loc, 0), total: rows.reduce((a, r) => a + r.loc, 0) },
        byKind,
        topRules: [...ruleFns.entries()].sort((a, b) => b[1] - a[1]).slice(0, 30)
            .map(([rule, n]) => ({ rule, functions: n, onlyBlocker: ruleOnly.get(rule) ?? 0, occurrences: ruleOcc.get(rule) ?? 0 })),
        topExternals: [...ext.entries()].sort((a, b) => b[1] - a[1]).slice(0, 40).map(([name, n]) => ({ name, functions: n })),
        topExternalTypes: [...extT.entries()].sort((a, b) => b[1] - a[1]).slice(0, 40).map(([name, n]) => ({ name, functions: n })),
        onlyExternal,
    };
}
function runCoverage(opts) {
    const cfgPath = path.resolve(opts.cwd, opts.project);
    const root = path.dirname(cfgPath);
    const cfg = ts.getParsedCommandLineOfConfigFile(cfgPath, {}, {
        ...ts.sys, onUnRecoverableConfigFileDiagnostic: d => { throw new Error(ts.flattenDiagnosticMessageText(d.messageText, ' ')); },
    });
    if (!cfg)
        throw new Error(`cannot read ${cfgPath}`);
    // read-only: never emit, never write build info
    const options = { ...cfg.options, noEmit: true, incremental: false, composite: false, declaration: false, skipLibCheck: true };
    delete options.tsBuildInfoFile;
    const timing = !!process.env.STRICTTS_COV_TIMING;
    const t0 = Date.now();
    const tick = (what) => { if (timing)
        process.stderr.write(`[timing] ${what}: ${((Date.now() - t0) / 1000).toFixed(1)} s\n`); };
    const program = ts.createProgram(cfg.fileNames, options);
    tick('program');
    const diags = new diag_1.Diags(opts.cwd);
    const tr = new core_1.Translator(program, diags);
    tr.coverage = true;
    const own = program.getSourceFiles().filter(sf => !sf.isDeclarationFile && !program.isSourceFileDefaultLibrary(sf) && !sf.fileName.includes('/node_modules/'));
    for (const sf of own)
        tr.projectFiles.add(sf);
    tr.liftConstArrows = false;
    tr.strict = !!opts.strict;
    tr.files = own;
    tr.analysis.run(own);
    // files with TypeScript errors
    const errFirst = new Map();
    for (const sf of own) {
        const ds = [...program.getSyntacticDiagnostics(sf), ...program.getSemanticDiagnostics(sf)].filter(d => d.category === ts.DiagnosticCategory.Error);
        if (ds.length) {
            const d = ds[0];
            const p = d.file && d.start !== undefined ? d.file.getLineAndCharacterOfPosition(d.start) : { line: 0, character: 0 };
            errFirst.set(sf, `${path.relative(root, sf.fileName)}:${p.line + 1}:${p.character + 1} [ts${d.code}] ${ts.flattenDiagnosticMessageText(d.messageText, ' ').slice(0, 200)}`);
        }
    }
    tick('diagnostics');
    // (after the diagnostics: the analysis asks the checker for many types)
    tr.analyzeIdentity(own);
    // module-level variables: globals, or placeholders whose reason is charged to their users
    for (const sf of own) {
        for (const st of sf.statements) {
            if (!ts.isVariableStatement(st))
                continue;
            for (const d of st.declarationList.declarations) {
                if (tr.isRegexConst(d))
                    continue;
                const ids = [];
                const collect = (b) => { if (ts.isIdentifier(b))
                    ids.push(b);
                else
                    b.elements.forEach(el => { if (!ts.isOmittedExpression(el))
                        collect(el.name); }); };
                collect(d.name);
                for (const id of ids) {
                    const sym = tr.symAt(id);
                    if (!sym)
                        continue;
                    try {
                        const ty = tr.types.map(tr.checker.getTypeOfSymbol(sym), new Map(), id);
                        tr.globalOf.set(sym, tr.newGlobal(id.text, ty));
                    }
                    catch (e) {
                        const r = e;
                        tr.globalPoison.set(sym, { rule: r.rule ?? 'internal', node: id, msg: `module-level ${id.text}: ${r.message ?? String(e)}`, extName: r.extName });
                    }
                }
            }
        }
    }
    tick('globals');
    const inScope = (sf) => !opts.onlyDirs || opts.onlyDirs.some(d => {
        const rel = path.relative(path.resolve(root, d), sf.fileName);
        return !rel.startsWith('..') && !path.isAbsolute(rel);
    });
    const rows = [];
    const covered = [];
    for (const sf of own) {
        if (!inScope(sf))
            continue;
        for (const u of collectUnits(sf)) {
            const line = sf.getLineAndCharacterOfPosition(u.node.getStart(sf)).line + 1;
            const row = { file: path.relative(root, sf.fileName), name: u.name, kind: u.kind, line, loc: loc(u.node, sf), status: 'covered', rules: {}, externals: [], externalTypes: [] };
            const te = errFirst.get(sf);
            if (te) {
                row.status = 'ts-error';
                row.rules = { 'ts-error': 1 };
                row.first = te;
                rows.push(row);
                continue;
            }
            tr.covDiags = [];
            tr.covExternals = new Set();
            tr.covExtTypes = new Set();
            tr.poisonCount = 0;
            const tu = Date.now();
            try {
                coverUnit(tr, u);
            }
            catch (e) {
                if (process.env.STRICTTS_DEBUG)
                    process.stderr.write(`[debug] ${u.name}: ${(e.stack ?? '').split('\n').slice(0, 30).join('\n')}\n`);
                tr.covDiags.push({ rule: 'internal', node: u.node, msg: `translator failure: ${e.message ?? e}` });
            }
            (0, check_1.visitSubset)(program, u.node, (n, rule, msg) => tr.covDiags.push({ rule, node: n, msg }), !!opts.strict);
            // de-duplicate (the checker and the translator may report the same node and rule)
            const seen = new Set();
            const ds = tr.covDiags.filter(d => {
                const k = `${d.rule}@${d.node ? d.node.getStart() : -1}`;
                if (seen.has(k))
                    return false;
                seen.add(k);
                return true;
            });
            for (const d of ds)
                row.rules[d.rule] = (row.rules[d.rule] ?? 0) + 1;
            row.diags = ds.slice(0, 40).map(d => ({ rule: d.rule, at: where(d.node, root), msg: d.msg.slice(0, 160) }));
            if (ds.length) {
                row.status = 'blocked';
                const firstD = [...ds].sort((a, b) => (a.node?.getStart() ?? 0) - (b.node?.getStart() ?? 0))[0];
                row.first = `${where(firstD.node, root)} [${firstD.rule}] ${firstD.msg.slice(0, 200)}`;
            }
            if (timing && Date.now() - tu > 1000)
                process.stderr.write(`[timing] slow unit ${row.file}:${row.line} ${row.name}: ${((Date.now() - tu) / 1000).toFixed(1)} s\n`);
            row.externals = [...tr.covExternals].sort();
            row.externalTypes = [...tr.covExtTypes].sort();
            rows.push(row);
            if (row.status === 'covered')
                covered.push(u);
        }
    }
    tick('units');
    const label = opts.label ?? path.basename(root);
    const res = { rows, summary: summarize(rows, label) };
    if (opts.emitLean) {
        // the covered functions as one partial program (normal translation, see partial.ts)
        const t1 = Date.now();
        const tr2 = new core_1.Translator(program, new diag_1.Diags(opts.cwd));
        tr2.files = own;
        for (const sf of own)
            tr2.projectFiles.add(sf);
        tr2.strict = !!opts.strict;
        const { ir, stats } = tr2.translatePartial(covered, opts.emitGenerics === false ? undefined : 'number');
        ir.namespace = 'Cov_' + label.replace(/[^A-Za-z0-9_]/g, '_');
        ir.sources = [`${path.relative(opts.cwd, cfgPath)} (covered functions of ${label})`];
        const lean = (0, emit_1.emitProgram)(ir, {});
        fs.mkdirSync(path.dirname(path.resolve(opts.emitLean)), { recursive: true });
        fs.writeFileSync(opts.emitLean, lean);
        // the declaration of each emitted function (`X.funs.json` next to `X.lean`; tools/validate)
        const instOf = new Map([...tr2.instances.values()].map(i => [i.info, i]));
        const funs = ir.funs.map(f => {
            const inst = instOf.get(f);
            // (constructors of mutable structures have no declaration)
            const decl = inst?.decl;
            const sf = decl?.getSourceFile();
            const file = sf ? path.relative(root, sf.fileName) : null;
            const line = sf && decl ? sf.getLineAndCharacterOfPosition(decl.getStart(sf)).line + 1 : null;
            // a covered generic function at its `--emit-generics` instance: the generic function's own
            // name and kind (as in the coverage rows) and the instantiation
            const g = tr2.genericUnits?.get(f);
            if (g)
                return { name: g.name, lean: f.leanName, role: inst?.role ?? 'helper', generic: true, file, line, kind: g.kind, inst: g.inst };
            return { name: f.name, lean: f.leanName, role: inst?.role ?? 'helper', generic: !!inst && inst.subst.size > 0, file, line };
        });
        fs.writeFileSync(opts.emitLean.replace(/\.lean$/, '') + '.funs.json', JSON.stringify(funs, null, 1) + '\n');
        res.emit = { ...stats, file: opts.emitLean, bytes: Buffer.byteLength(lean), lines: lean.split('\n').length, secs: (Date.now() - t1) / 1000 };
        tick('emit-lean');
    }
    return res;
}
function writeReport(out, res) {
    fs.mkdirSync(path.dirname(path.resolve(out)), { recursive: true });
    fs.writeFileSync(out, JSON.stringify({ summary: res.summary, rows: res.rows }, null, 1));
}
function formatSummary(s) {
    const pct = (a, b) => (b ? `${((100 * a) / b).toFixed(1)}%` : '-');
    const lines = [];
    lines.push(`== ${s.label}: functions ${s.functions.covered}/${s.functions.total} covered (${pct(s.functions.covered, s.functions.total)}), ` +
        `LOC ${s.loc.covered}/${s.loc.total} (${pct(s.loc.covered, s.loc.total)}), ts-error ${s.functions.tsError}, only-external ${s.onlyExternal}`);
    lines.push(`   by kind: ${Object.entries(s.byKind).map(([k, v]) => `${k} ${v.covered}/${v.total}`).join(', ')}`);
    lines.push('   rule                         fns  only  occ');
    for (const r of s.topRules)
        lines.push(`   ${r.rule.padEnd(28)} ${String(r.functions).padStart(4)} ${String(r.onlyBlocker).padStart(5)} ${String(r.occurrences).padStart(5)}`);
    lines.push('   top external callees (functions):');
    for (const e of s.topExternals)
        lines.push(`     ${String(e.functions).padStart(4)}  ${e.name}`);
    lines.push('   top external types (functions):');
    for (const e of s.topExternalTypes.slice(0, 20))
        lines.push(`     ${String(e.functions).padStart(4)}  ${e.name}`);
    return lines.join('\n');
}
