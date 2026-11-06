// Runs a transpiled program under Node and prints its final status in the format of the
// Lean driver (StrictTS.Frontend.showRun): `[ok]` or `[uncaught Name: message]`.
// With STRICTTS_TRACE=1 (programs marked `@extern`), the external calls that the translator
// turns into `extern` (regular expressions, JSON, elements of match results, and the host
// functions named in STRICTTS_TRACE_EXTRA) and the values of `Date.now()` are recorded and
// written to stderr after a `=====TRACE=====` line, for the Lean run to replay
// (StrictTS.Frontend.runMainTrace).
'use strict';
const path = require('path');
const fs = require('fs');
const JSONstringify = JSON.stringify;

let trace = null;
if (process.env.STRICTTS_TRACE) {
  const calls = [], nows = [];
  trace = { calls, nows };
  const ids = new WeakMap();
  let nextId = 0, depth = 0;
  const handle = (o) => { if (!ids.has(o)) ids.set(o, nextId++); return { h: ids.get(o) }; };
  const num = (x) => ({ n: Object.is(x, -0) ? '-0' : String(x) });
  const enc = (v) => {
    if (v === undefined) return { u: 1 };
    if (v === null) return null;
    if (typeof v === 'boolean') return v;
    if (typeof v === 'number') return num(v);
    if (typeof v === 'string') return { s: v };
    if (wrapped.has(v)) return handle(v);
    if (Array.isArray(v)) return { a: v.map(enc) };
    if (typeof v === 'object' && Object.getPrototypeOf(v) === Object.prototype) {
      return { o: Object.entries(v).map(([k, x]) => [k, enc(x)]) };
    }
    return { other: 1 };
  };
  const wrapped = new WeakSet();
  const rawOf = new WeakMap();
  // the elements and properties of a match result are external reads too
  const matchResult = (tyName, m) => {
    if (m === null) return null;
    const p = new Proxy(m, {
      get(t, k, r) {
        const v = Reflect.get(t, k, r);
        if (depth > 0 || typeof k !== 'string') return v;
        // (no regex here: RegExp.prototype.test is recorded)
        if (k.length > 0 && [...k].every((c) => c >= '0' && c <= '9')) calls.push({ name: `${tyName}.get:[]`, args: [handle(p), num(Number(k))], out: enc(v) });
        else if (k === 'index' || k === 'input' || k === 'length') calls.push({ name: `${tyName}.get:${k}`, args: [handle(p)], out: enc(v) });
        return v;
      },
    });
    wrapped.add(p);
    rawOf.set(p, m);
    return p;
  };
  const record = (name, args, f, post = (v) => v) => {
    if (depth > 0) return f();
    depth++;
    let v;
    try { v = post(f()); } catch (e) {
      depth--;
      calls.push({ name, args: args.map(enc), err: [String(e && e.name), String(e && e.message)] });
      throw e;
    }
    depth--;
    calls.push({ name, args: args.map(enc), out: enc(v) });
    return v;
  };
  const RP = RegExp.prototype, SP = String.prototype;
  const test = RP.test, exec = RP.exec;
  RP.test = function (s) { return record('RegExp.test', [this.source, this.flags, s], () => test.call(this, s)); };
  RP.exec = function (s) { return record('RegExp.exec', [this.source, this.flags, s], () => exec.call(this, s), (m) => matchResult('RegExpExecArray', m)); };
  const matchAll = SP.matchAll;
  SP.matchAll = function (re) {
    if (!(re instanceof RegExp) || depth > 0) return matchAll.call(this, re);
    // the iterator's results as an array (what the translator's extern answers)
    return record('String.matchAll', [String(this), re.source, re.flags], () => [...matchAll.call(this, re)],
      (ms) => ms.map((m) => matchResult('RegExpExecArray', m)));
  };
  // `s.replace(re, f)` with a replacer function, as the translator does it: the matches (one
  // recorded call), then for each match its index, match and groups (recorded reads), the
  // replacer, and the pieces between the matches
  const replaceFn = (str, re, fn) => {
    const ms = re.global ? SP.matchAll.call(str, re) : (() => { const m = RP.exec.call(re, str); return m === null ? [] : [m]; })();
    let out = '', next = 0;
    for (const m of ms) {
      const raw = rawOf.get(m);
      const idx = m.index;
      const m0 = m[0];
      const groups = [];
      for (let k = 1; k < raw.length; k++) groups.push(m[k]);
      const repl = String(fn(m0, ...groups, idx, str));
      if (idx >= next) { out += str.slice(next, idx) + repl; next = idx + m0.length; }
    }
    return out + str.slice(next);
  };
  for (const name of ['match', 'replace', 'replaceAll', 'split', 'search']) {
    const orig = SP[name];
    SP[name] = function (re, ...rest) {
      if (!(re instanceof RegExp) || depth > 0) return orig.call(this, re, ...rest);
      if ((name === 'replace' || name === 'replaceAll') && typeof rest[0] === 'function') return replaceFn(String(this), re, rest[0]);
      return record(`String.${name}`, [String(this), re.source, re.flags, ...rest], () => orig.call(this, re, ...rest),
        name === 'match' ? (m) => matchResult('RegExpMatchArray', m) : (v) => v);
    };
  }
  // `new RegExp(p, f)` / `RegExp(p, f)` as the translator calls it (the extern "RegExp.new"):
  // the record of the regex's flags and source, or the SyntaxError of a bad pattern
  const ORegExp = RegExp;
  const regexpNew = function RegExp(...a) {
    if (depth > 0) return new ORegExp(...a);
    let re;
    try { re = new ORegExp(...a); } catch (e) {
      calls.push({ name: 'RegExp.new', args: a.map(enc), err: [String(e && e.name), String(e && e.message)] });
      throw e;
    }
    calls.push({ name: 'RegExp.new', args: a.map(enc), out: { o: [['flags', { s: re.flags }], ['source', { s: re.source }]] } });
    return re;
  };
  regexpNew.prototype = ORegExp.prototype;
  Object.setPrototypeOf(regexpNew, ORegExp);
  globalThis.RegExp = regexpNew;
  // console.warn / console.error, which the translator calls as externs (standard error)
  for (const cn of ['warn', 'error']) {
    const orig = console[cn];
    console[cn] = function (...a) { return record(`console.${cn}`, a, () => orig.apply(console, a)); };
  }
  const normalize = SP.normalize;
  SP.normalize = function (form) {
    return record('String.normalize', [String(this), form === undefined ? 'NFC' : form], () => normalize.call(this, form));
  };
  const parse = JSON.parse, stringify = JSON.stringify;
  JSON.parse = function (s, ...rest) { return record('JSON.parse', [s, ...rest], () => parse(s, ...rest)); };
  JSON.stringify = function (...a) { return record('JSON.stringify', a, () => stringify(...a)); };
  const now = Date.now;
  Date.now = () => { const t = now(); if (depth === 0) nows.push(num(t)); return t; };
  // other host functions the translator calls as externs, by name (comma-separated in
  // STRICTTS_TRACE_EXTRA): `f` is the global function f; `C.f` is the static function C.f, or
  // else the method f of C's instances with the receiver as the first argument (as the
  // translator passes it)
  for (const name of (process.env.STRICTTS_TRACE_EXTRA || '').split(',').filter(Boolean)) {
    const [cn, fn] = name.split('.');
    const C = globalThis[cn];
    if (!fn && typeof C === 'function') {
      globalThis[cn] = function (...args) { return record(name, args, () => C.apply(this, args)); };
      continue;
    }
    if (!C || !fn) continue;
    if (typeof C[fn] === 'function') {
      const orig = C[fn];
      C[fn] = function (...args) { return record(name, args, () => orig.apply(this, args)); };
    } else if (C.prototype && typeof C.prototype[fn] === 'function') {
      const orig = C.prototype[fn];
      C.prototype[fn] = function (...args) { return record(name, [this, ...args], () => orig.apply(this, args)); };
    }
  }
}

process.on('uncaughtException', (e) => {
  const name = e && typeof e === 'object' ? e.name : typeof e;
  const msg = e && typeof e === 'object' ? e.message : String(e);
  process.stdout.write(`[uncaught ${name}: ${msg}]\n`);
  process.exit(1);
});
// (written with fs.writeSync until done: in an exit handler, a large process.stderr.write to a
// pipe is cut off when the process ends)
function writeAll(fd, s) {
  const b = Buffer.from(s, 'utf8');
  for (let off = 0; off < b.length;) {
    try { off += fs.writeSync(fd, b, off, b.length - off); } catch (e) { if (e.code !== 'EAGAIN') throw e; }
  }
}
process.on('exit', (code) => {
  if (code === 0) writeAll(1, '[ok]\n');
  if (trace) writeAll(2, `=====TRACE=====\n${JSONstringify(trace)}\n`);
});
require(path.resolve(process.argv[2]));
