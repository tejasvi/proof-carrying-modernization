// Node side of the designed-panic check: run one function of a checked build
// (tools/public/node/build.js: reads `a[i]` whose type excludes undefined, `x!`, and reads of
// declared class fields throw a type violation instead of continuing with undefined) on the
// recorded inputs of tools/validate, each in fresh module instances, and say where the first
// violation happens. Run it with the permission model:
//
//   node --permission --allow-fs-read=OUTDIR --allow-fs-read=THIS_DIR tools/validate/checked_run.js \
//     OUTDIR FILE NAME KIND INPUTS.json
//
// FILE: the emitted module (relative to OUTDIR); NAME/KIND: `f` function|arrow, `C.m` method,
// `C.constructor` ctor, `C.m` static; INPUTS.json: [{args: [Tagged], self?: [Tagged]}] in the
// tagged form of tools/difftool/src/gen.ts. Prints one JSON line per input:
// {outcome: violation | returned | threw, where?, message?}.
'use strict';
const path = require('path');
const fs = require('fs');
const [outDir, file, name, kind, inputsFile] = process.argv.slice(2);
// the oracles of Lean's World.init and of the validation's Node runs (choosePivot draws with Math.random)
Math.random = () => 0;
Date.now = () => 0;

function violation(where, what) {
  const e = new Error(`${what} at ${where}`);
  e.tsViolation = true;
  e.where = where;
  return e;
}
// the checks of tools/public/node/run.js
globalThis.__strictts_ck = (v, where) => { if (v === undefined) throw violation(where, 'undefined'); return v; };
globalThis.__strictts_nn = (v, where) => { if (v === undefined || v === null) throw violation(where, String(v)); return v; };
globalThis.__strictts_ix = (a, k, where) => {
  if (Array.isArray(a) || typeof a === 'string' || ArrayBuffer.isView(a)) {
    const i = typeof k === 'number' ? k : Number(k);
    if (!(Number.isInteger(i) && i >= 0 && i < a.length)) throw violation(where, `index ${typeof k === 'number' ? (Object.is(k, -0) ? '-0' : k) : JSON.stringify(k)} out of bounds (length ${a.length}),`);
  } else if (a !== null && typeof a === 'object' && !Object.prototype.hasOwnProperty.call(a, k)) {
    throw violation(where, `missing key ${JSON.stringify(String(k))}`);
  }
  return a[k];
};

const index = JSON.parse(fs.readFileSync(path.join(outDir, 'index.json'), 'utf8'));
const classFile = {};
for (const [f, items] of Object.entries(index)) for (const it of items) if (it.cls && !(it.cls in classFile)) classFile[it.cls] = f;
const load = (f) => require(path.join(outDir, f)).__strictts;

/** A tagged value as a JavaScript value (classes built by their constructors). */
function val(t) {
  if (t === null) return undefined;
  switch (t.t) {
    case 'n': return t.v === 'NaN' ? NaN : t.v === 'Inf' ? Infinity : t.v === '-Inf' ? -Infinity : t.v === '-0' ? -0 : Number(t.v);
    case 's': return t.v;
    case 'b': return BigInt(t.v);
    case 'B': return t.v;
    case 'u': return undefined;
    case 'z': return null;
    case 'a': return t.v.map(val);
    case 'o': return Object.fromEntries(t.v.map(([k, x]) => [k, val(x)]));
    case 'm': return new Map(t.v.map(([k, x]) => [val(k), val(x)]));
    case 'S': return new Set(t.v.map(val));
    case 'c': { const base = t.cls.replace(/<.*$/, ''); return new (load(classFile[base])[base])(...t.args.map(val)); }
    case 'ta': return new globalThis[t.kind](t.v.map(val));
    case 'd': return new Date(t.v);
    case 'p': return Promise.resolve(val(t.v));
    default: throw new Error(`tagged value ${t.t}`);
  }
}

(async () => {
  const inputs = JSON.parse(fs.readFileSync(inputsFile, 'utf8'));
  for (const inp of inputs) {
    // fresh module instances for every input (module-level state)
    for (const k of Object.keys(require.cache)) if (k.startsWith(path.resolve(outDir) + path.sep)) delete require.cache[k];
    let out;
    try {
      const exp = load(file);
      const args = inp.args.map(val);
      let r;
      if (kind === 'function' || kind === 'arrow') r = exp[name](...args);
      else {
        const dot = name.indexOf('.');
        const C = exp[name.slice(0, dot).replace(/<.*$/, '')];
        const member = name.slice(dot + 1);
        if (kind === 'ctor') r = new C(...args);
        else if (kind === 'static') r = C[member](...args);
        else r = new C(...(inp.self || []).map(val))[member](...args);
      }
      if (r && typeof r.then === 'function') r = await r;
      out = { outcome: 'returned' };
    } catch (e) {
      if (e && e.tsViolation) out = { outcome: 'violation', where: e.where, message: e.message };
      else out = { outcome: 'threw', name: e && e.name, message: String(e && e.message).slice(0, 200) };
    }
    console.log(JSON.stringify(out));
  }
})();
