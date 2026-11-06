// Node side of the NoPanic counterexample check: run one function of an instrumented build
// (tools/public/node/build.js) on one input and say whether the run reaches a value that its
// TypeScript type excludes. Run it with the permission model (no writes, no child processes):
//
//   node --permission --allow-fs-read=OUTDIR --allow-fs-read=THIS_DIR tools/public/node/run.js \
//     OUTDIR FILE NAME KIND ARGS [plain RET]
//
// With `plain`, the checks are off (the program runs as written) and the result is compared with
// the declared return type RET (primitive types, arrays, unions, literals; other types are not
// checked): {conforms: true | false | null}.
//
// FILE: the emitted module (relative to OUTDIR); NAME/KIND: as in OUTDIR/index.json (`f`,
// `C.m`, `C.constructor`, `C.get p`); ARGS: a JavaScript array literal (methods and getters take
// the object first), which may use `__mk(className, fields)` (an object of that class with these
// fields) and `__err(name, message)`. Prints one JSON line: {outcome: violation | returned |
// threw | timeout, where?, value?, name?, message?}.
'use strict';
const path = require('path');
const [outDir, file, name, kind, argsSrc, mode, retTy] = process.argv.slice(2);
const plain = mode === 'plain';

function violation(where, what) {
  const e = new Error(`${what} at ${where}`);
  e.tsViolation = true;
  e.where = where;
  return e;
}
globalThis.__strictts_ck = (v, where) => { if (v === undefined && !plain) throw violation(where, 'undefined'); return v; };
globalThis.__strictts_nn = (v, where) => { if ((v === undefined || v === null) && !plain) throw violation(where, String(v)); return v; };
globalThis.__strictts_ix = (a, k, where) => {
  if (plain) return a[k];
  if (Array.isArray(a) || typeof a === 'string' || ArrayBuffer.isView(a)) {
    const i = typeof k === 'number' ? k : Number(k);
    if (!(Number.isInteger(i) && i >= 0 && i < a.length)) throw violation(where, `index ${typeof k === 'number' ? (Object.is(k, -0) ? '-0' : k) : JSON.stringify(k)} out of bounds (length ${a.length}),`);
  } else if (a !== null && typeof a === 'object' && !Object.prototype.hasOwnProperty.call(a, k)) {
    throw violation(where, `missing key ${JSON.stringify(String(k))}`);
  }
  return a[k];
};

const index = require(path.join(outDir, 'index.json'));
const classFile = {};
for (const [f, items] of Object.entries(index)) for (const it of items) if (it.cls && !(it.cls in classFile)) classFile[it.cls] = f;
function __mk(cls, fields) {
  const base = cls.replace(/<.*$/, '');   // instances of generic classes: `C<number>`
  const C = require(path.join(outDir, classFile[base])).__strictts[base];
  return Object.assign(Object.create(C.prototype), fields);
}
function __err(n, message) { const e = new Error(message); e.name = n; return e; }

function splitTop(t, sep) {
  const out = []; let depth = 0, cur = '';
  for (const ch of t) {
    if ('(<[{'.includes(ch)) depth++;
    if (')>]}'.includes(ch)) depth--;
    if (ch === sep && depth === 0) { out.push(cur); cur = ''; } else cur += ch;
  }
  out.push(cur);
  return out.map(x => x.trim()).filter(x => x);
}
/** Does `v` have type `t` (a TypeScript type as printed by the checker)? null: not checked. */
function conforms(v, t) {
  t = (t || '').trim();
  if (!t) return null;
  const parts = splitTop(t, '|');
  if (parts.length > 1) {
    let unknown = false;
    for (const p of parts) { const r = conforms(v, p); if (r === true) return true; if (r === null) unknown = true; }
    return unknown ? null : false;
  }
  if (t.startsWith('(') && t.endsWith(')')) return conforms(v, t.slice(1, -1));
  if (t.startsWith('readonly ')) return conforms(v, t.slice(9));
  if (t === 'number') return typeof v === 'number';
  if (t === 'string') return typeof v === 'string';
  if (t === 'boolean') return typeof v === 'boolean';
  if (t === 'true' || t === 'false') return v === (t === 'true');
  if (t === 'bigint') return typeof v === 'bigint';
  if (t === 'undefined' || t === 'void') return v === undefined;
  if (t === 'null') return v === null;
  if (/^"([^"\\]|\\.)*"$/.test(t)) return v === JSON.parse(t);
  if (/^-?\d+(\.\d+)?$/.test(t)) return v === Number(t);
  const arr = t.endsWith('[]') ? t.slice(0, -2) : (/^Array<(.*)>$/.exec(t) || [])[1];
  if (arr !== undefined) {
    if (!Array.isArray(v)) return false;
    let unknown = false;
    for (const x of v) { const r = conforms(x, arr); if (r === false) return false; if (r === null) unknown = true; }
    return unknown ? null : true;
  }
  return null;
}

function show(v, depth = 0) {
  if (depth > 3) return '…';
  if (typeof v === 'number') return Object.is(v, -0) ? '-0' : String(v);
  if (typeof v === 'bigint') return `${v}n`;
  if (typeof v === 'string') return JSON.stringify(v);
  if (typeof v === 'boolean') return String(v);
  if (v === undefined) return 'undefined';
  if (v === null) return 'null';
  if (Array.isArray(v)) return `[${v.slice(0, 20).map(x => show(x, depth + 1)).join(', ')}]`;
  if (v instanceof Map) return `Map(${v.size})`;
  if (v instanceof Set) return `Set(${v.size})`;
  if (typeof v === 'function') return '<function>';
  return `{${Object.keys(v).slice(0, 10).map(k => `${k}: ${show(v[k], depth + 1)}`).join(', ')}}`;
}

(async () => {
  let out;
  try {
    const args = new Function('__mk', '__err', `return ${argsSrc};`)(__mk, __err);
    const exp = require(path.join(outDir, file)).__strictts;
    let fn;
    if (kind === 'function' || kind === 'arrow') fn = exp[name];
    else {
      const dot = name.indexOf('.');
      const C = exp[name.slice(0, dot).replace(/<.*$/, '')];
      const member = name.slice(dot + 1);
      if (kind === 'constructor') fn = (...a) => new C(...a);
      else if (kind === 'static') fn = (...a) => C[member](...a);
      else if (kind === 'getter') fn = (o) => o[member.replace(/^get /, '')];
      else fn = (o, ...a) => C.prototype[member].apply(o, a);
    }
    if (typeof fn !== 'function') throw Object.assign(new Error(`no function ${name} in ${file}`), { harness: true });
    let r = fn(...args);
    if (r && typeof r.then === 'function') {
      r = await Promise.race([r, new Promise((_, rej) => setTimeout(() => rej(Object.assign(new Error('timeout'), { timeout: true })), 5000))]);
    }
    out = { outcome: 'returned', value: show(r) };
    if (plain) out.conforms = conforms(r, retTy);
  } catch (e) {
    if (e && e.tsViolation) out = { outcome: 'violation', where: e.where, message: e.message };
    else if (e && e.timeout) out = { outcome: 'timeout' };
    else if (e && e.harness) out = { outcome: 'harness', message: e.message };
    else out = { outcome: 'threw', name: e && e.name, message: String(e && e.message).slice(0, 200) };
  }
  console.log(JSON.stringify(out));
})();
