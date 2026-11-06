// Regular expressions as external calls. A regex used as the receiver of `test` / `exec` or as
// the pattern of `match` / `replace` / `replaceAll` / `split` / `search` becomes an `extern`
// whose arguments are the receiver, then the pattern and the flags, then the other arguments:
//   re.test(s)        -> .extern "RegExp.test" [pattern, flags, s]
//   s.replace(re, r)  -> .extern "String.replace" [s, pattern, flags, r]
// A literal (written at the call or bound by a `const` declaration) gives them as string
// literals; any other regex is a value, the record of its flags and source (`REGEXP_TY`): a
// literal used as a value, or `new RegExp(pattern, flags)`, the extern "RegExp.new" (which
// throws Node's SyntaxError for a bad pattern). `test` / `exec` (and `match` / `replace` on
// sticky regexes) read and write `lastIndex` when the regex is global or sticky; that state is
// not modelled, so such calls are accepted on a literal written at the call (a fresh regex each
// time), rejected on a literal bound to a name, and panic on a value with such flags; `lastIndex`
// itself is rejected, and so is `===` on regex values (identity). `split` and replacer functions
// need the groups of the pattern, so they take literals only.
import * as ts from 'typescript';
import { Ty, T, showTy, REGEXP_TY } from './ty';
import { Expr, E, S, Item, mkVar, declItem, stmtItem } from './ir';
import { reject } from './diag';
import { Translator, FnCtx, strLit, numLit, isLibDecl } from './core';
import { skipParens } from './stmts';

const P = Translator.prototype;

export interface RegexLit { pattern: string; flags: string; inline: boolean }

declare module './core' {
  interface Translator {
    /** The literal of a regex expression (a literal, or a `const` bound to one). */
    regexLit(e: ts.Expression): RegexLit | undefined;
    /** `const re = /…/`: no binding; every use is resolved to the literal. */
    isRegexConst(d: ts.VariableDeclaration): boolean;
    /** A call that uses a regex, as an extern; `undefined` if the call uses none. */
    lowerRegexCall(call: ts.CallExpression, fc: FnCtx, exp: Ty | undefined): Expr | undefined;
    /** A regex literal as a value: the record of its flags and source. */
    regexValue(re: RegexLit): Expr;
    /** Is `t` the library type `RegExp`? */
    isRegExpType(t: ts.Type): boolean;
  }
}

/** Pattern and flags of a literal; the flags in the order of `RegExp.prototype.flags`. */
function parseLit(n: ts.RegularExpressionLiteral): { pattern: string; flags: string } {
  const i = n.text.lastIndexOf('/');
  const fl = n.text.slice(i + 1);
  return { pattern: n.text.slice(1, i), flags: [...'dgimsuvy'].filter(c => fl.includes(c)).join('') };
}

/** The number of capturing groups of the pattern (`none` if it has named groups, whose
 * `groups` object would be passed to replacers). */
function captureCount(p: string): number | undefined {
  let inClass = false, n = 0;
  for (let i = 0; i < p.length; i++) {
    const c = p[i];
    if (c === '\\') { i++; continue; }
    if (inClass) { if (c === ']') inClass = false; continue; }
    if (c === '[') inClass = true;
    else if (c === '(') {
      if (p[i + 1] !== '?') n++;
      else if (p[i + 2] === '<' && p[i + 3] !== '=' && p[i + 3] !== '!') return undefined;
    }
  }
  return n;
}

/** Whether the pattern has a capturing group (`(` not escaped, not in a class, not `(?`
 * except named groups `(?<name>`). */
function hasCapture(p: string): boolean {
  let inClass = false;
  for (let i = 0; i < p.length; i++) {
    const c = p[i];
    if (c === '\\') { i++; continue; }
    if (inClass) { if (c === ']') inClass = false; continue; }
    if (c === '[') inClass = true;
    else if (c === '(' && (p[i + 1] !== '?' || (p[i + 2] === '<' && p[i + 3] !== '=' && p[i + 3] !== '!'))) return true;
  }
  return false;
}

// STRICTTS_NO_REGEX=1: regexes rejected as before (to measure coverage without them)
const off = !!process.env.STRICTTS_NO_REGEX;

P.isRegexConst = function (this: Translator, d) {
  return !off && ts.isIdentifier(d.name) && !!d.initializer && ts.isRegularExpressionLiteral(skipParens(d.initializer)) &&
    !!(d.parent.flags & ts.NodeFlags.Const);
};

P.regexLit = function (this: Translator, e0) {
  const e = skipParens(e0);
  if (ts.isRegularExpressionLiteral(e)) return { ...parseLit(e), inline: true };
  if (ts.isIdentifier(e)) {
    const d = this.symAt(e)?.valueDeclaration;
    if (d && ts.isVariableDeclaration(d) && this.isRegexConst(d) && this.isProjectDecl(d)) {
      return { ...parseLit(skipParens(d.initializer!) as ts.RegularExpressionLiteral), inline: false };
    }
  }
  return undefined;
};

/** `s.replace(re, f)` / `s.replaceAll(re, f)` with a replacer function, as RegExp.prototype
 * [@@replace] does it: the matches first (the extern `String.matchAll` for a global regex,
 * `RegExp.exec` otherwise), then for each match, in order, its index, the match and its groups
 * (each an extern read of the match result), the replacer called with them, the offset and the
 * string, and the pieces of the string between the matches. */
function replaceWithFunction(tr: Translator, call: ts.CallExpression, recv: ts.Expression, re: RegexLit, fnNode: ts.Expression, fc: FnCtx): Expr {
  const n = captureCount(re.pattern);
  if (n === undefined) reject(call, 'no-regexp', 'a replacer function with named groups (its groups argument)');
  const global = re.flags.includes('g');
  if (!global && !re.inline && re.flags.includes('y')) reject(call, 'no-regexp', 'replace with a sticky regex bound to a name reads and writes its lastIndex (not modelled)');
  const mt = T.ext('RegExpExecArray');
  const fnTy = T.fn([T.str, ...Array.from({ length: n }, () => T.opt(T.str)), T.num, T.str], T.str);
  const [s0, f0] = tr.seq([() => tr.lowerExpr(recv, fc, T.str), () => tr.lowerCallback(fnNode, fc, fnTy)], fc);
  const s = E.var(tr.bindTemp(s0, fc, 's'));
  const f = E.var(tr.bindTemp(f0, fc, 'f'));
  const lit = [strLit(re.pattern), strLit(re.flags)];
  if (tr.coverage) { tr.covExternals.add(global ? 'String.matchAll' : 'RegExp.exec'); tr.covExternals.add('RegExpExecArray.get:[]'); }
  // the matches, as an array
  let ms: Expr;
  if (global) ms = E.extern('String.matchAll', [s, ...lit], T.arr(mt));
  else {
    const one = E.extern('RegExp.exec', [...lit, s], T.union([mt, T.null]));
    const v = mkVar('m', mt), u = mkVar('u', T.null);
    ms = E.caseU(one, [{ v, body: E.builtin(`(.arrOf ${showTy(mt)} 1)`, [E.var(v)], [mt], T.arr(mt)) }, { v: u, body: E.builtin(`(.arrOf ${showTy(mt)} 0)`, [], [], T.arr(mt)) }]);
  }
  const out = mkVar('out', T.str, true), next = mkVar('next', T.num, true);
  fc.pre.push(declItem(out, strLit('')));
  fc.pre.push(declItem(next, E.lit('(.num 0)', T.num, 0)));
  const m = mkVar('m', mt);
  const body: Item[] = [];
  const idx = mkVar('idx', T.num), m0 = mkVar('m0', T.str);
  body.push(declItem(idx, E.extern('RegExpExecArray.get:index', [E.var(m)], T.num)));
  body.push(declItem(m0, E.unwrap(E.extern('RegExpExecArray.get:[]', [E.var(m), E.lit('(.num 0)', T.num, 0)], T.opt(T.str)))));
  const groups = Array.from({ length: n }, (_, k) => {
    const g = mkVar(`g${k + 1}`, T.opt(T.str));
    body.push(declItem(g, E.extern('RegExpExecArray.get:[]', [E.var(m), E.lit(`(.num ${k + 1})`, T.num, k + 1)], T.opt(T.str))));
    return E.var(g);
  });
  const repl = mkVar('repl', T.str);
  body.push(declItem(repl, E.app(f, [E.var(m0), ...groups, E.var(idx), s])));
  const slice = (a: Expr, b?: Expr) => E.prim('.strSlice', [s, a, b ? E.some(b) : E.none(T.num)], [T.str, T.num, T.opt(T.num)], T.str);
  const cat = (a: Expr, b: Expr) => E.prim('.strConcat', [a, b], [T.str, T.str], T.str);
  // (a match before the end of the previous one adds nothing: as in the specification)
  body.push(stmtItem(S.ite(E.prim('(.numCmp .ge)', [E.var(idx), E.var(next)], [T.num, T.num], T.bool), [
    stmtItem(S.assign(out, cat(cat(E.var(out), slice(E.var(next), E.var(idx))), E.var(repl)))),
    stmtItem(S.assign(next, E.prim('(.numBin .add)', [E.var(idx), E.prim('.strLength', [E.var(m0)], [T.str], T.num)], [T.num, T.num], T.num))),
  ], [])));
  fc.pre.push(stmtItem({ k: 'forOf', e: ms, v: m, body }));
  return cat(E.var(out), slice(E.var(next)));
}

const STRING_METHODS = new Set(['match', 'matchAll', 'replace', 'replaceAll', 'split', 'search']);

P.regexValue = function (this: Translator, re) {
  return E.mkRec(REGEXP_TY, [strLit(re.flags), strLit(re.pattern)]);
};

P.isRegExpType = function (this: Translator, t) {
  const sym = t.getSymbol();
  return !!sym && sym.name === 'RegExp' && isLibDecl(this.program, sym.declarations?.[0]);
};

/** `call` unless the flags of the regex value contain one of `bad` (and none of `unless`): those
 * flags make the call read and write `lastIndex`, which is not modelled (a panic). */
function guardFlags(flags: Expr, bad: string, unless: string, call: Expr): Expr {
  const has = (c: string) => E.prim('.strIncludes', [flags, strLit(c), numLit(0)], [T.str, T.str, T.num], T.bool);
  let c: Expr = [...bad].map(has).reduce((a, b) => E.or(a, b));
  for (const u of unless) c = E.and(c, E.not(has(u)));
  return E.cond(c, E.unreachable(call.ty), call);
}

P.lowerRegexCall = function (this: Translator, call, fc, exp) {
  const callee = skipParens(call.expression);
  if (off || !ts.isPropertyAccessExpression(callee) || callee.questionDotToken) return undefined;
  const name = callee.name.text;
  const args = call.arguments;
  const stateful = (re: RegexLit, flags: string) => !re.inline && [...flags].some(f => re.flags.includes(f));
  const sig = () => {
    const s = this.checker.getResolvedSignature(call);
    if (!s) reject(call, 'no-regexp', `cannot resolve the signature of ${name}`);
    return this.tyOf(s.getReturnType(), fc, call);
  };
  const lit = (re: RegexLit) => [strLit(re.pattern), strLit(re.flags)];
  // a regex value (not a literal): the record of its flags and source
  const valueOf = (x: ts.Expression): boolean => this.isRegExpType(this.checker.getTypeAtLocation(x));
  // (evaluated into a variable in its turn: its two fields are read)
  const value = (x: ts.Expression) => () => E.var(this.bindTemp(this.lowerExpr(x, fc, REGEXP_TY), fc, 're'));
  const fields = (rv: Expr): [Expr, Expr] => [E.getRec(rv, 1), E.getRec(rv, 0)];
  if (name === 'test' || name === 'exec') {
    const re = this.regexLit(callee.expression);
    if (!re && !valueOf(callee.expression)) return undefined;
    if (args.length !== 1 || ts.isSpreadElement(args[0])) reject(call, 'no-regexp', `RegExp.${name} takes one string`);
    if (re && stateful(re, 'gy')) {
      reject(call, 'no-regexp', `${name} on a global or sticky regex bound to a name reads and writes its lastIndex (not modelled); write the literal at the call`);
    }
    if (this.coverage) this.covExternals.add(`RegExp.${name}`);
    const ret = name === 'test' ? T.bool : sig();
    if (re) return E.extern(`RegExp.${name}`, [...lit(re), this.lowerExpr(args[0], fc, T.str)], ret);
    const [rv, s] = this.seq([value(callee.expression), () => this.lowerExpr(args[0], fc, T.str)], fc);
    const [pat, fl] = fields(rv);
    return guardFlags(fl, 'gy', '', E.extern(`RegExp.${name}`, [pat, fl, s], ret));
  }
  if (STRING_METHODS.has(name) && args.length >= 1 && !ts.isSpreadElement(args[0])) {
    const re = this.regexLit(args[0]);
    if (!re && !valueOf(args[0])) return undefined;
    const rt = this.checker.getTypeAtLocation(callee.expression);
    if (!(rt.flags & ts.TypeFlags.StringLike)) return undefined;
    if (re && (name === 'match' || name === 'replace') && stateful(re, 'y') && !re.flags.includes('g')) {
      reject(call, 'no-regexp', `${name} with a sticky regex bound to a name reads and writes its lastIndex (not modelled)`);
    }
    if (name === 'split' && re && hasCapture(re.pattern)) {
      reject(call, 'no-regexp', 'split with a capturing group puts the groups (possibly undefined) into the result');
    }
    const rest = args.slice(1);
    const fnArg = rest.length === 1 && (() => { const ax = skipParens(rest[0]); return ts.isArrowFunction(ax) || ts.isFunctionExpression(ax) || this.checker.getTypeAtLocation(rest[0]).getCallSignatures().length > 0; })();
    if ((name === 'replace' || name === 'replaceAll') && fnArg) {
      if (!re) reject(call, 'no-regexp', `${name} with a replacer function and a regex value: the groups it is called with are not known`);
      return replaceWithFunction(this, call, callee.expression, re, rest[0], fc);
    }
    for (const a of rest) {
      const ax = skipParens(a);
      if (ts.isSpreadElement(a)) reject(a, 'extern-spread', `spread argument to String.${name}`);
      if (ts.isArrowFunction(ax) || ts.isFunctionExpression(ax) || this.checker.getTypeAtLocation(a).getCallSignatures().length) {
        reject(a, 'extern-callback', `callback passed to the external function String.${name}`);
      }
    }
    if (name === 'matchAll' && args.length !== 1) reject(call, 'no-regexp', 'String.matchAll takes one regex');
    const restTys: Ty[] = name === 'split' ? [T.num] : [T.str];
    if (rest.length > restTys.length) reject(call, 'no-regexp', `String.${name} with ${args.length} arguments`);
    const vals = this.seq([() => this.lowerExpr(callee.expression, fc, T.str), ...(re ? [] : [value(args[0])]),
      ...rest.map((a, i) => () => this.lowerExpr(a, fc, restTys[i]))], fc);
    const pf = re ? lit(re) : fields(vals.splice(1, 1)[0]);
    if (this.coverage) this.covExternals.add(`String.${name}`);
    // matchAll: its iterator as the array of the match results (consumed by for…of, spreads and
    // Array.from; the oracle answers a fresh array)
    const matchAllElem = (): Ty => {
      const it = this.checker.getTypeAtLocation(call) as ts.TypeReference;
      const targs = (it.flags & ts.TypeFlags.Object) ? this.checker.getTypeArguments(it) : [];
      const el = targs.length ? this.tyOf(targs[0], fc, call) : T.ext('RegExpMatchArray');
      if (el.k !== 'ext') reject(call, 'no-regexp', 'matchAll elements of an unexpected type');
      return el;
    };
    // match with a global regex answers the array of the matched strings (or null), not a match
    // object (TypeScript's lib types both as RegExpMatchArray): typed so where an array is
    // expected (e.g. `Array.from(s.match(re) ?? [])`); elsewhere the value keeps the lib's type
    const ret = name === 'replace' || name === 'replaceAll' ? T.str : name === 'search' ? T.num : name === 'split' ? T.arr(T.str)
      : name === 'matchAll' ? T.arr(matchAllElem()) : name === 'match' && re && re.flags.includes('g') && exp && (exp.k === 'arr' || (exp.k === 'opt' && exp.t.k === 'arr')) ? T.opt(T.arr(T.str)) : sig();
    if (name === 'split' && !re) {
      // the groups of a value's pattern are put into the result: an absent one (undefined, which
      // the type string[] excludes) panics
      const os = T.opt(T.str);
      const ps = [mkVar('x', os), mkVar('i', T.num), mkVar('a', T.arr(os))];
      const unwrap = E.lam(false, ps, T.str, [stmtItem(S.ret(E.unwrap(E.var(ps[0]))))]);
      const got = E.extern('String.split', [vals[0], ...pf, ...vals.slice(1)], T.arr(os));
      return E.builtin(`(.arrMap ${showTy(os)} .str)`, [got, unwrap], [T.arr(os), T.fn([os, T.num, T.arr(os)], T.str)], T.arr(T.str));
    }
    const ext = E.extern(`String.${name}`, [vals[0], ...pf, ...vals.slice(1)], ret);
    // (a sticky value that is not global: match / replace read and write its lastIndex)
    return !re && (name === 'match' || name === 'replace') ? guardFlags(pf[1], 'y', 'g', ext) : ext;
  }
  void exp;
  return undefined;
};
