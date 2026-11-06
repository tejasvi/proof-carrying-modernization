// Functions, lambdas, classes, lambda lifting, globals and program assembly.
import * as ts from 'typescript';
import { Ty, T, tyEq, prettyTy, showTy, tyKey, stripIdBoxes } from './ty';
import { Expr, Item, Block, VarInfo, FunInfo, GlobalInfo, E, S, mkVar, declItem, stmtItem, InternalError } from './ir';
import { reject, Reject } from './diag';
import { Translator, FnCtx, Binding, FunDeclInst, within } from './core';
import { Subst, ClassInst, MutStruct, substKey, isLibDecl } from './types';
import { ParamSpec } from './exprs';
import { ProgramIR } from './emit';
import { skipParens } from './stmts';

declare module './core' {
  interface Translator {
    topFunDecl(sym: ts.Symbol): ts.FunctionDeclaration | undefined;
    /** The arrow of a module-level `const f = (…) => …` translated as a function (see below). */
    liftedArrow(d: ts.VariableDeclaration): ts.ArrowFunction | ts.FunctionExpression | undefined;

    funInfoFor(decl: ts.FunctionDeclaration, subst: Subst, node: ts.Node): FunInfo;
    instantiate(decl: ts.SignatureDeclaration, call: ts.CallLikeExpression, fc: FnCtx, base: Subst): Subst;
    paramSpecs(decl: ts.SignatureDeclaration, subst: Subst): ParamSpec[];
    tsParams(decl: ts.SignatureDeclaration): ts.ParameterDeclaration[];
    returnTy(decl: ts.SignatureDeclaration, subst: Subst, async: boolean): Ty;
    lowerLambda(n: ts.ArrowFunction | ts.FunctionExpression, fc: FnCtx, exp?: Ty, fixedParams?: boolean): Expr;
    lowerConciseBody(body: ts.Expression, fc: FnCtx, out: Item[]): void;
    bindParams(decl: ts.SignatureDeclaration, params: (VarInfo | undefined)[], fc: FnCtx, out: Item[], fixedParams?: boolean): void;
    lowerFunBody(inst: FunDeclInst): void;
    classMember(ci: ClassInst, name: string, kind: 'method' | 'getter' | 'setter', node: ts.Node): FunInfo | null;
    classStatic(ci: ClassInst, name: string, node: ts.Node): FunInfo | null;
    classCtor(ci: ClassInst, node: ts.Node): FunInfo;
    structCtor(ms: MutStruct, node: ts.Node): FunInfo;
    staticFieldGlobal(pa: ts.PropertyAccessExpression): GlobalInfo | null;
    liftedConstArrow(d: ts.VariableDeclaration, sym: ts.Symbol, fc: FnCtx): boolean;
    liftedAsValue(b: Extract<Binding, { k: 'lifted' }>, node: ts.Node, fc: FnCtx, target?: Ty): Expr;
    liftedCapArgs(b: Extract<Binding, { k: 'lifted' }>, fc: FnCtx, node: ts.Node): Expr[];
    lowerClassDeclStmt(cd: ts.ClassDeclaration, fc: FnCtx, out: Item[]): void;
    isGlobalDecl(d: ts.VariableDeclaration): boolean;
    lowerGlobalDecl(d: ts.VariableDeclaration, fc: FnCtx, out: Item[]): void;
    queueInst(inst: FunDeclInst): void;
    isAsync(decl: ts.Node): boolean;
  }
}

const P = Translator.prototype;
const SK = ts.SyntaxKind;

function declId(n: ts.Node): string {
  return `${n.getSourceFile().fileName}:${n.pos}`;
}

P.isAsync = function (decl) {
  return !!ts.getModifiers(decl as ts.HasModifiers)?.some(m => m.kind === SK.AsyncKeyword);
};

P.queueInst = function (this: Translator, inst) {
  this.instances.set(`${inst.role}:${inst.info.name}:${inst.info.idx}`, inst);
  this.queue.push(inst);
};

P.topFunDecl = function (this: Translator, sym) {
  const decls = sym.declarations ?? [];
  const fds = decls.filter(ts.isFunctionDeclaration);
  if (!fds.length) {
    // `const f = (…) => …` at module level is the function f when that is safe (liftedArrow)
    const vd = decls.find(ts.isVariableDeclaration);
    const a = vd && !isLibDecl(this.program, vd) ? this.liftedArrow(vd) : undefined;
    if (!a) return undefined;
    this.unitNames ??= new Map();
    if (!this.unitNames.has(a)) this.unitNames.set(a, (vd!.name as ts.Identifier).text);
    return a as unknown as ts.FunctionDeclaration;
  }
  const withBody = fds.filter(d => d.body);
  const d = withBody[0];
  if (!d || !ts.isSourceFile(d.parent) || isLibDecl(this.program, d)) return undefined;
  // overload signatures only type the calls; the implementation (the one declaration with a body)
  // is the function that runs, and calls convert their arguments to its parameter types
  if (withBody.length > 1) reject(d, 'unsupported', 'more than one implementation of a function');
  return d;
};

/** `const f = (…) => …` (or a function expression) at module level. */
function liftableArrow(d: ts.VariableDeclaration): ts.ArrowFunction | ts.FunctionExpression | undefined {
  if (!ts.isIdentifier(d.name) || !d.initializer || !(d.parent.flags & ts.NodeFlags.Const)) return undefined;
  const st = d.parent.parent;
  if (!st || !ts.isVariableStatement(st) || !ts.isSourceFile(st.parent)) return undefined;
  let e = d.initializer;
  while (ts.isParenthesizedExpression(e)) e = e.expression;
  return ts.isArrowFunction(e) || ts.isFunctionExpression(e) ? e : undefined;
}

// A module-level `const f = (…) => …` is translated as a top-level function (FunRef, callFun)
// instead of a module variable holding a closure. The constant is never reassigned and a
// closure at module level captures only module-level bindings, which a function reads the
// same way; the one difference is the temporal dead zone: the variable cannot be read before
// its declaration has run. So f is lifted only if no code that may run before that point can
// reach it: the module statements before the declaration (and the earlier declarators of the
// same statement), followed through every function, class and lifted arrow they mention
// (conservatively: mentioned, not only called).
P.liftedArrow = function (this: Translator, d) {
  if (!this.liftConstArrows) return undefined;
  const a = liftableArrow(d);
  if (!a) return undefined;
  const known = this.liftSafe.get(d);
  if (known !== undefined) return known ? a : undefined;
  const f = this.symAt(d.name as ts.Identifier);
  const st = d.parent.parent as ts.VariableStatement;
  const sf = st.getSourceFile();
  const work: ts.Node[] = [...sf.statements.slice(0, sf.statements.indexOf(st))];
  for (const x of st.declarationList.declarations) { if (x === d) break; work.push(x); }
  const visited = new Set<ts.Node>();
  let safe = !!f;
  const visit = (n: ts.Node): void => {
    if (!safe) return;
    if (ts.isIdentifier(n)) {
      const s = this.symAt(n);
      if (!s) return;
      if (s === f) { safe = false; return; }
      for (const decl of s.declarations ?? []) {
        if (isLibDecl(this.program, decl) || decl.getSourceFile().isDeclarationFile) continue;
        // code that runs when the symbol is called or constructed
        const body = ts.isFunctionDeclaration(decl) || ts.isClassDeclaration(decl) || ts.isMethodDeclaration(decl) ? decl
          : ts.isVariableDeclaration(decl) ? liftableArrow(decl) : undefined;
        if (body && !visited.has(body)) { visited.add(body); work.push(body); }
      }
      return;
    }
    ts.forEachChild(n, visit);
  };
  while (safe && work.length) visit(work.pop()!);
  this.liftSafe.set(d, safe);
  return safe ? a : undefined;
};

P.tsParams = function (decl) {
  return decl.parameters.filter(p => !(ts.isIdentifier(p.name) && p.name.text === 'this'));
};

P.paramSpecs = function (this: Translator, decl, subst) {
  if (decl.parameters.some(p => ts.isIdentifier(p.name) && p.name.text === 'this')) reject(decl, 'unsupported', '`this` parameters');
  return this.tsParams(decl).map(p => {
    let ty = this.types.map(this.checker.getTypeAtLocation(p), subst, p);
    if (p.dotDotDotToken) {
      if (ty.k !== 'arr') reject(p, 'unsupported', 'rest parameter must be an array');
      return { ty, optional: false, rest: true };
    }
    const optional = !!(p.questionToken || p.initializer);
    if (optional && ty.k !== 'opt') ty = T.opt(ty);
    return { ty, optional, rest: false };
  });
};

P.returnTy = function (this: Translator, decl, subst, async) {
  const sig = this.checker.getSignatureFromDeclaration(decl);
  if (!sig) reject(decl, 'unsupported', 'function without signature');
  const rt = this.types.map(sig.getReturnType(), subst, decl);
  if (async) {
    if (rt.k !== 'promise') reject(decl, 'unsupported', 'async function must return a Promise');
    return rt.t;
  }
  return rt;
};

P.instantiate = function (this: Translator, decl, call, fc, base) {
  const tps = decl.typeParameters ?? [];
  if (!tps.length) return base;
  const sig = this.checker.getResolvedSignature(call);
  const targs = sig && this.checker.getTypeArgumentsForResolvedSignature(sig);
  if (!targs || targs.length < tps.length) reject(call, 'unsupported-generic', 'cannot determine the type arguments of this call');
  const s: Subst = new Map(base);
  // a call resolved to an overload signature: its type arguments, matched to the implementation's
  // type parameters by name
  const sdecl = sig!.declaration;
  if (sdecl && sdecl !== decl && !ts.isJSDocSignature(sdecl)) {
    const names = (sdecl.typeParameters ?? []).map(tp => tp.name.text);
    for (const tp of tps) {
      const i = names.indexOf(tp.name.text);
      if (i < 0) reject(call, 'unsupported-generic', `the overload this call resolves to has no type parameter ${tp.name.text} of the implementation`);
      s.set(this.checker.getTypeAtLocation(tp), this.tyOf(targs![i], fc, call));
    }
    return s;
  }
  tps.forEach((tp, i) => s.set(this.checker.getTypeAtLocation(tp), this.tyOf(targs[i], fc, call)));
  return s;
};

function paramName(p: ts.ParameterDeclaration | undefined, i: number): string {
  return p && ts.isIdentifier(p.name) ? p.name.text : `p${i}`;
}

P.funInfoFor = function (this: Translator, decl, subst, node) {
  const tps = decl.typeParameters ?? [];
  const own = new Map([...subst].filter(([k]) => tps.some(tp => this.checker.getTypeAtLocation(tp) === k)));
  const key = `fun:${declId(decl)}:${substKey(own)}`;
  const known = this.instances.get(key);
  if (known) return known.info;
  if (decl.asteriskToken) reject(decl, 'no-generators', 'generators are not allowed');
  const async = this.isAsync(decl);
  const specs = this.paramSpecs(decl, own);
  const tsp = this.tsParams(decl);
  const params = specs.map((s, i) => mkVar(paramName(tsp[i], i), s.ty));
  const base = this.unitNames?.get(decl) ?? decl.name?.text ?? 'anon';
  const targs = tps.map(tp => own.get(this.checker.getTypeAtLocation(tp))!);
  const suffix = tps.length ? `<${targs.map(prettyTy).join(', ')}>` : '';
  const leanBase = tps.length ? `${base}_${targs.map(t => this.types.shortName(t)).join('_')}` : base;
  const info = this.newFun(base + suffix, leanBase, params, this.returnTy(decl, own, async), async);
  this.funDocs.set(info, `${base}${suffix}(${tsp.map((p, i) => `${paramName(p, i)}: ${prettyTy(specs[i].ty)}`).join(', ')}): ${prettyTy(info.ret)}`);
  const inst: FunDeclInst = { decl, subst: own, info, role: 'fun' };
  this.instances.set(key, inst);
  this.queue.push(inst);
  void node;
  return info;
};

// ---------------------------------------------------------------------------------------
// parameters and lambdas

P.bindParams = function (this: Translator, decl, params, fc, out, fixedParams = false) {
  const tsp = this.tsParams(decl);
  tsp.forEach((p, i) => {
    const v = params[i];
    if (fixedParams && v && ts.isIdentifier(p.name)) {
      // callback parameters typed by the library (Promise executors, rejection handlers)
      const sym = this.symAt(p.name)!;
      if (this.isReassigned(sym)) reject(p, 'unsupported', `reassigned parameter ${p.name.text}`);
      if (v.ty.k === 'fn' && this.types.boxedFns.has(tyKey(stripIdBoxes(v.ty)))) {
        // (a resolve function of a type compared by identity, e.g. kept in a Set: one cell)
        const bt = T.box(v.ty);
        this.declareLocal(sym, p.name.text, bt, E.builtin(`(.boxNew ${showTy(v.ty)})`, [E.var(v)], [v.ty], bt), fc, out);
        return;
      }
      fc.bind(sym, { k: 'var', v, fixed: true, errVar: v.ty.k === 'err' });
      return;
    }
    if (p.dotDotDotToken) {
      if (!v) reject(p, 'unsupported', 'rest parameter in a callback');
      if (!ts.isIdentifier(p.name)) reject(p, 'unsupported-syntax', 'destructured rest parameter');
      const sym = this.symAt(p.name)!;
      if (this.needsBox(sym) || this.isReassigned(sym)) this.declareLocal(sym, p.name.text, v.ty, E.var(v), fc, out);
      else fc.bind(sym, { k: 'var', v });
      return;
    }
    if (ts.isIdentifier(p.name)) {
      const sym = this.symAt(p.name)!;
      const inner = this.tyOf(this.checker.getTypeOfSymbol(sym), fc, p);
      let value: Expr;
      if (!v) {
        if (p.initializer) {
          const [d, pre] = this.isolate(fc, () => this.lowerExpr(p.initializer!, fc, inner));
          out.push(...pre);
          value = d;
        } else if (inner.k === 'opt') value = E.none(inner.t);
        else if (inner.k === 'undef') value = E.undef();
        else reject(p, 'unsupported', `parameter ${p.name.text} receives no argument here`);
      } else if (p.initializer && v.ty.k === 'opt') {
        const y = mkVar(p.name.text, v.ty.t);
        const [d, pre] = this.isolate(fc, () => this.lowerExpr(p.initializer!, fc, inner));
        if (pre.length) reject(p.initializer, 'unsupported', 'default parameter value with await/assignments');
        value = E.caseOpt(E.var(v), d, y, this.coerce(E.var(y), inner, p));
      } else if (inner.k === 'box' && inner.t.k === 'fn' && v.ty.k === 'fn' && tyEq(inner.t, v.ty)) {
        // a plain function received where functions are compared by identity: one cell
        value = E.builtin(`(.boxNew ${showTy(v.ty)})`, [E.var(v)], [v.ty], inner);
      } else value = this.adapt(E.var(v), inner, p);
      if (v && value.k === 'var' && value.v === v && !this.needsBox(sym)) {
        v.mayChange = this.isReassigned(sym);
        fc.bind(sym, { k: 'var', v });
      } else this.declareLocal(sym, p.name.text, inner, value, fc, out);
      return;
    }
    if (!v) reject(p, 'unsupported', 'destructured parameter without argument');
    if (p.initializer) {
      // `{ a = 1 }: T = {}`: the default where the argument is undefined, then the pattern
      if (v.ty.k !== 'opt') reject(p, 'unsupported-syntax', 'default value for a destructured parameter that cannot be undefined');
      const t = v.ty.t;
      const [d, pre] = this.isolate(fc, () => this.lowerExpr(p.initializer!, fc, t));
      if (pre.length) reject(p.initializer, 'unsupported', 'default parameter value with await/assignments');
      const y = mkVar('p', t), pv = mkVar('p', t);
      out.push(declItem(pv, E.caseOpt(E.var(v), d, y, E.var(y))));
      this.bindPattern(p.name, E.var(pv), fc, out, true);
      return;
    }
    this.bindPattern(p.name, E.var(v), fc, out, true);
  });
};

P.lowerConciseBody = function (this: Translator, body, fc, out) {
  const saved = fc.pre;
  fc.pre = out;
  try {
    if (fc.retPoison) { this.lowerExpr(body, fc); return; }
    const nat = this.tyAt(body, fc);
    if (fc.async && nat.k === 'promise') {
      out.push(stmtItem({ k: 'retP', e: this.lowerExpr(body, fc, T.promise(fc.bodyRet)) }));
      return;
    }
    if (fc.bodyRet.k === 'undef') {
      // `() => f(x)` used as a void function: evaluate for effect, return undefined
      this.lowerExprStmt(body, fc, out);
      return;
    }
    if (fc.bodyRet.k === 'bool' && this.tyAt(body, fc).k !== 'bool') {
      // `xs.filter(x => x.parent)`: JavaScript tests truthiness (a pure null test for
      // optional objects; otherwise the truthiness rule)
      out.push(stmtItem(S.ret(this.truthy(this.lowerExpr(body, fc), body))));
      return;
    }
    out.push(stmtItem(S.ret(this.lowerExpr(body, fc, fc.bodyRet))));
  } finally { fc.pre = saved; }
};

P.lowerLambda = function (this: Translator, n, fc, exp, fixedParams = false) {
  if ((n as ts.FunctionExpression).asteriskToken) reject(n, 'no-generators', 'generators are not allowed');
  // a function compared by identity (identity.ts): a new cell holding the closure, each time
  const boxedTarget = exp && exp.k === 'box' && exp.t.k === 'fn' ? exp.t : undefined;
  const ownBoxed = !boxedTarget && (!exp || exp.k !== 'fn') && (() => { const own = this.tyAt(n, fc); return own.k === 'box' && own.t.k === 'fn'; })();
  if (boxedTarget || ownBoxed) {
    const ft = boxedTarget ?? (this.tyAt(n, fc) as Extract<Ty, { k: 'box' }>).t;
    const lam = this.lowerLambda(n, fc, ft, fixedParams);
    const cell = E.builtin(`(.boxNew ${showTy(lam.ty)})`, [lam], [lam.ty], T.box(lam.ty));
    return exp && !boxedTarget ? this.coerce(cell, exp, n) : cell;
  }
  let fnTy = exp && exp.k === 'fn' ? exp : this.tyAt(n, fc);
  if (fnTy.k !== 'fn') reject(n, 'unsupported', `function used as ${prettyTy(fnTy)}`);
  const async = this.isAsync(n);
  if (async && fnTy.ret.k === 'undef' && exp) {
    // an async callback where a void function is expected: its promise is dropped
    const nat = this.tyAt(n, fc);
    if (nat.k === 'fn' && nat.ret.k === 'promise') {
      const inner = this.lowerLambda(n, fc, T.fn(fnTy.args, nat.ret), fixedParams);
      return this.coerce(inner, exp, n);
    }
  }
  let bodyRet = fnTy.ret;
  if (async) {
    if (bodyRet.k !== 'promise') reject(n, 'unsupported', 'async function used as a function that does not return a Promise');
    bodyRet = bodyRet.t;
  }
  if (ts.isFunctionExpression(n) && n.name) {
    const self = this.symAt(n.name);
    const f = self && this.facts(self);
    if (self && this.analysis.vars.get(self) === undefined) {
      // named function expression: references to its own name are not supported
      void f;
    }
  }
  const child = new FnCtx(fc, 'lambda', async, bodyRet, fc.subst, n);
  const tsp = this.tsParams(n);
  const params = fnTy.args.map((t, i) => mkVar(paramName(tsp[i], i), t));
  const items: Item[] = [];
  child.pre = items;
  this.bindParams(n, params, child, items, fixedParams);
  if (ts.isBlock(n.body)) items.push(...this.lowerBlockStmts(n.body.statements, child));
  else this.lowerConciseBody(n.body, child, items);
  const lam = E.lam(async, params, bodyRet, items);
  return exp && exp.k !== 'fn' ? this.coerce(lam, exp, n) : lam;
};

// ---------------------------------------------------------------------------------------
// function bodies

P.lowerFunBody = function (this: Translator, inst) {
  const { decl, subst, info } = inst;
  const fc = new FnCtx(null, 'fun', info.async, info.bodyRet, subst, decl);
  const items: Item[] = [];
  fc.pre = items;
  let params = info.params;
  if (inst.role === 'method' || inst.role === 'getter' || inst.role === 'setter') {
    fc.thisVar = info.params[0];
    params = info.params.slice(1);
  }
  if (inst.role === 'lifted' && inst.lifted) {
    const { caps, capBindings } = inst.lifted;
    caps.forEach((sym, i) => fc.bind(sym, capBindings[i]));
    for (const [sym, b] of inst.liftedScope ?? []) fc.bind(sym, b);
    params = info.params.slice(caps.length);
  }
  if (inst.role === 'ctor') {
    lowerCtorBody(this, inst, fc, items);
    info.body = items;
    return;
  }
  this.bindParams(decl, params, fc, items);
  const body = (decl as ts.FunctionLikeDeclaration).body;
  if (!body) reject(decl, 'unsupported', 'function without body');
  if (ts.isBlock(body)) items.push(...this.lowerBlockStmts(body.statements, fc));
  else this.lowerConciseBody(body, fc, items);
  info.body = items;
};

declare module './core' {
  interface FunDeclInst { liftedScope?: Map<ts.Symbol, Binding> }
}

function lowerCtorBody(tr: Translator, inst: FunDeclInst, fc: FnCtx, items: Item[]): void {
  const ci = inst.cls!;
  const info = inst.info;
  fc.isCtor = true;
  const thisV = mkVar('this', T.obj(ci.name));
  items.push(declItem(thisV, E.newObj(ci.name)));
  fc.thisVar = thisV;
  // field initialisers (declaration order), before the parameters are bound (ECMA-262
  // [[Construct]]: InitializeInstanceElements precedes FunctionDeclarationInstantiation)
  for (const m of ci.decl.members) {
    if (!ts.isPropertyDeclaration(m) || ts.getModifiers(m)?.some(x => x.kind === SK.StaticKeyword)) continue;
    const name = (m.name as ts.Identifier).text;
    const idx = ci.fieldIdx.get(name)!;
    const fty = ci.fields[idx].ty;
    if (m.initializer) {
      const saved = fc.pre;
      fc.pre = items;
      try { items.push(stmtItem(S.setField(E.var(thisV), ci.name, idx, fty, tr.lowerExpr(m.initializer, fc, fty)))); } finally { fc.pre = saved; }
    } else if (fty.k === 'opt') items.push(stmtItem(S.setField(E.var(thisV), ci.name, idx, fty, E.none(fty.t))));
    else if (fty.k === 'undef') items.push(stmtItem(S.setField(E.var(thisV), ci.name, idx, fty, E.undef())));
  }
  const ctor = ci.decl.members.find(ts.isConstructorDeclaration);
  if (ctor) {
    tr.bindParams(ctor, info.params, fc, items);
    for (const p of ctor.parameters) {
      if (!ts.getModifiers(p)?.some(m => [SK.PublicKeyword, SK.PrivateKeyword, SK.ProtectedKeyword, SK.ReadonlyKeyword].includes(m.kind))) continue;
      const name = (p.name as ts.Identifier).text;
      const idx = ci.fieldIdx.get(name)!;
      const sym = tr.symAt(p.name)!;
      const b = tr.lookup(sym, fc)!;
      const v = tr.coerce(tr.readBinding(b, p), ci.fields[idx].ty, p);
      items.push(stmtItem(S.setField(E.var(thisV), ci.name, idx, ci.fields[idx].ty, v)));
    }
    if (ctor.body) items.push(...tr.lowerBlockStmts(ctor.body.statements, fc));
  }
  items.push(stmtItem(S.ret(E.var(thisV))));
}

// ---------------------------------------------------------------------------------------
// classes

function memberName(m: ts.ClassElement): string | undefined {
  if (!m.name) return undefined;
  if (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name) || ts.isStringLiteral(m.name)) return m.name.text;
  return undefined;
}

function isStatic(m: ts.ClassElement): boolean {
  return !!ts.getModifiers(m as ts.HasModifiers)?.some(x => x.kind === SK.StaticKeyword);
}

P.classCtor = function (this: Translator, ci, node) {
  const key = `ctor:${ci.name}`;
  const known = this.instances.get(key);
  if (known) return known.info;
  const ctor = ci.decl.members.find(ts.isConstructorDeclaration);
  const specs = ctor ? this.paramSpecs(ctor, ci.subst) : [];
  const tsp = ctor ? this.tsParams(ctor) : [];
  const params = specs.map((s, i) => mkVar(paramName(tsp[i], i), s.ty));
  const info = this.newFun(`${ci.name}.constructor`, `${ci.name}_new`, params, T.obj(ci.name), false);
  this.funDocs.set(info, `new ${ci.name}(${tsp.map((p, i) => `${paramName(p, i)}: ${prettyTy(specs[i].ty)}`).join(', ')})`);
  const inst: FunDeclInst = { decl: ctor ?? (ci.decl as unknown as ts.SignatureDeclaration), subst: ci.subst, info, cls: ci, role: 'ctor' };
  this.instances.set(key, inst);
  this.queue.push(inst);
  void node;
  return info;
};

P.classMember = function (this: Translator, ci, name, kind, node) {
  const key = `${kind}:${ci.name}:${name}`;
  const known = this.instances.get(key);
  if (known) return known.info;
  const m = ci.decl.members.find(x => !isStatic(x) && memberName(x) === name &&
    (kind === 'method' ? ts.isMethodDeclaration(x) : kind === 'getter' ? ts.isGetAccessorDeclaration(x) : ts.isSetAccessorDeclaration(x))) as
    ts.MethodDeclaration | ts.AccessorDeclaration | undefined;
  if (!m) return null;
  if (m.typeParameters?.length) reject(m, 'unsupported-generic', 'generic methods are not supported');
  if ((m as ts.MethodDeclaration).asteriskToken) reject(m, 'no-generators', 'generators are not allowed');
  const async = this.isAsync(m);
  const specs = this.paramSpecs(m, ci.subst);
  const tsp = this.tsParams(m);
  const thisV = mkVar('this', T.obj(ci.name));
  const params = [thisV, ...specs.map((s, i) => mkVar(paramName(tsp[i], i), s.ty))];
  const ret = kind === 'setter' ? T.undef : this.returnTy(m, ci.subst, async);
  const lean = kind === 'method' ? `${ci.name}_${name}` : `${ci.name}_${kind === 'getter' ? 'get' : 'set'}_${name}`;
  const info = this.newFun(`${ci.name}.${kind === 'method' ? '' : kind === 'getter' ? 'get ' : 'set '}${name}`, lean, params, ret, async);
  this.funDocs.set(info, `${ci.name}.${name}(this${tsp.map((p, i) => `, ${paramName(p, i)}: ${prettyTy(specs[i].ty)}`).join('')}): ${prettyTy(info.ret)}`);
  const inst: FunDeclInst = { decl: m, subst: ci.subst, info, cls: ci, role: kind };
  this.instances.set(key, inst);
  this.queue.push(inst);
  void node;
  return info;
};

P.classStatic = function (this: Translator, ci, name, node) {
  const key = `static:${ci.name}:${name}`;
  const known = this.instances.get(key);
  if (known) return known.info;
  const m = ci.decl.members.find(x => isStatic(x) && memberName(x) === name && ts.isMethodDeclaration(x)) as ts.MethodDeclaration | undefined;
  if (!m) return null;
  if (m.typeParameters?.length) reject(m, 'unsupported-generic', 'generic methods are not supported');
  const async = this.isAsync(m);
  const specs = this.paramSpecs(m, ci.subst);
  const tsp = this.tsParams(m);
  const params = specs.map((s, i) => mkVar(paramName(tsp[i], i), s.ty));
  const info = this.newFun(`${ci.name}.${name}`, `${ci.name}_static_${name}`, params, this.returnTy(m, ci.subst, async), async);
  const inst: FunDeclInst = { decl: m, subst: ci.subst, info, cls: ci, role: 'static' };
  this.instances.set(key, inst);
  this.queue.push(inst);
  void node;
  return info;
};

P.structCtor = function (this: Translator, ms, _node) {
  const key = `struct:${ms.name}`;
  const known = this.instances.get(key);
  if (known) return known.info;
  const params = ms.fields.map(f => mkVar(f.name, f.ty));
  const info = this.newFun(`${ms.name}.literal`, `${ms.name}_lit`, params, T.obj(ms.name), false);
  this.funDocs.set(info, `{ ${ms.fields.map(f => `${f.name}: ${prettyTy(f.ty)}`).join(', ')} } (object literal of ${ms.name})`);
  const o = mkVar('o', T.obj(ms.name));
  info.body = [
    declItem(o, E.newObj(ms.name)),
    ...ms.fields.map((f, i) => stmtItem(S.setField(E.var(o), ms.name, i, f.ty, E.var(params[i])))),
    stmtItem(S.ret(E.var(o))),
  ];
  this.instances.set(key, { decl: undefined as unknown as ts.SignatureDeclaration, subst: new Map(), info, role: 'structCtor', struct: ms });
  return info;
};

P.staticFieldGlobal = function (this: Translator, pa) {
  const base = skipParens(pa.expression);
  if (!ts.isIdentifier(base)) return null;
  const sym = this.symAt(base);
  if (!sym || !(sym.flags & ts.SymbolFlags.Class) || isLibDecl(this.program, sym.declarations?.[0])) return null;
  const decl = sym.declarations!.find(ts.isClassDeclaration)!;
  const prop = decl.members.find(m => isStatic(m) && ts.isPropertyDeclaration(m) && memberName(m) === pa.name.text) as ts.PropertyDeclaration | undefined;
  if (!prop) return null;
  const psym = this.checker.getSymbolAtLocation(prop.name)!;
  const known = this.staticFields.get(psym);
  if (known) return known;
  if (decl.typeParameters?.length) reject(pa, 'unsupported-generic', 'static fields of generic classes');
  const ty = this.types.map(this.checker.getTypeAtLocation(prop), new Map(), prop);
  const g = this.newGlobal(`${decl.name?.text}.${pa.name.text}`, ty);
  this.staticFields.set(psym, g);
  return g;
};

P.lowerClassDeclStmt = function (this: Translator, cd, fc, out) {
  if (fc.kind !== 'main' || !ts.isSourceFile(cd.parent)) reject(cd, 'unsupported', 'classes must be declared at module level');
  for (const m of cd.members) {
    if (ts.isClassStaticBlockDeclaration(m)) reject(m, 'unsupported-syntax', 'static blocks');
    if (ts.isPropertyDeclaration(m) && isStatic(m)) {
      const psym = this.checker.getSymbolAtLocation(m.name)!;
      let g = this.staticFields.get(psym);
      if (!g) {
        const ty = this.types.map(this.checker.getTypeAtLocation(m), new Map(), m);
        g = this.newGlobal(`${cd.name?.text}.${memberName(m)}`, ty);
        this.staticFields.set(psym, g);
      }
      if (m.initializer) {
        const saved = fc.pre;
        fc.pre = out;
        try { out.push(stmtItem(S.gset(g, this.lowerExpr(m.initializer, fc, g.ty)))); } finally { fc.pre = saved; }
      } else if (g.ty.k === 'opt') out.push(stmtItem(S.gset(g, E.none(g.ty.t))));
      else if (g.ty.k === 'undef') out.push(stmtItem(S.gset(g, E.undef())));
    }
  }
};

// ---------------------------------------------------------------------------------------
// lambda lifting of nested function declarations (and recursive const arrows)

interface FreeInfo { syms: ts.Symbol[]; lifted: ts.Symbol[] }

function freeOf(tr: Translator, fn: ts.Node, selfSym: ts.Symbol | undefined): FreeInfo {
  const syms: ts.Symbol[] = [];
  const lifted: ts.Symbol[] = [];
  const visit = (n: ts.Node, inArrowOfFn: boolean) => {
    if (n.kind === SK.ThisKeyword && inArrowOfFn) reject(n, 'no-this', '`this` in a nested function');
    if (ts.isIdentifier(n)) {
      const sym = tr.symAt(n);
      if (sym && sym !== selfSym) {
        const f = tr.facts(sym);
        if (f && !within(f.decl, fn) && !tr.globalOf.has(sym)) { if (!syms.includes(sym)) syms.push(sym); }
        else if (!f) {
          const d = sym.declarations?.[0];
          if (d && ((ts.isFunctionDeclaration(d) && !ts.isSourceFile(d.parent)) || (ts.isVariableDeclaration(d) && d.initializer && ts.isArrowFunction(d.initializer))) && !within(d, fn)) {
            if (!lifted.includes(sym)) lifted.push(sym);
          }
        }
      }
    }
    const isFnBoundary = ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isClassLike(n);
    ts.forEachChild(n, c => visit(c, isFnBoundary && n !== fn ? false : inArrowOfFn));
  };
  visit(fn, true);
  return { syms, lifted };
}

declare module './core' {
  interface Translator {
    liftFunctions(items: { decl: ts.SignatureDeclaration; sym: ts.Symbol; name: string }[], fc: FnCtx): void;
  }
}

P.liftFunctions = function (this: Translator, list, fc) {
  // captures: free variables plus the captures of lifted functions they call (fixpoint)
  const infos = list.map(x => ({ ...x, free: freeOf(this, x.decl, x.sym) }));
  const caps = new Map<ts.Symbol, ts.Symbol[]>();
  for (const x of infos) caps.set(x.sym, [...x.free.syms]);
  const capsOfOuter = (s: ts.Symbol): ts.Symbol[] | undefined => {
    const b = this.lookup(s, fc);
    return b && b.k === 'lifted' ? b.caps : undefined;
  };
  let changed = true;
  while (changed) {
    changed = false;
    for (const x of infos) {
      const mine = caps.get(x.sym)!;
      for (const g of x.free.lifted) {
        const theirs = caps.get(g) ?? capsOfOuter(g) ?? [];
        for (const s of theirs) if (!mine.includes(s)) { mine.push(s); changed = true; }
      }
    }
  }
  const created: { x: typeof infos[0]; b: Extract<Binding, { k: 'lifted' }>; inst: FunDeclInst }[] = [];
  for (const x of infos) {
    const cs = caps.get(x.sym)!;
    const optInit = (s: ts.Symbol) => {
      const d = s.valueDeclaration;
      return !!d && ts.isVariableDeclaration(d) && !d.initializer && !(d.parent && ts.isVariableDeclarationList(d.parent) && d.parent.parent && ts.isForOfStatement(d.parent.parent));
    };
    const capTys = cs.map(s => {
      const declTy = this.tyOf(this.checker.getTypeOfSymbol(s), fc, x.decl);
      if (this.needsBox(s) && optInit(s) && declTy.k !== 'opt' && declTy.k !== 'undef') return T.box(T.opt(declTy));
      return this.needsBox(s) ? T.box(declTy) : declTy;
    });
    const capVars = cs.map((s, i) => mkVar(s.name, capTys[i]));
    const async = this.isAsync(x.decl);
    const specs = this.paramSpecs(x.decl, fc.subst);
    const tsp = this.tsParams(x.decl);
    const params = specs.map((s, i) => mkVar(paramName(tsp[i], i), s.ty));
    const info = this.newFun(x.name, x.name, [...capVars, ...params], this.returnTy(x.decl, fc.subst, async), async);
    this.funDocs.set(info, `${x.name}(${[...cs.map((s, i) => `${s.name}: ${prettyTy(capTys[i])} (captured)`), ...tsp.map((p, i) => `${paramName(p, i)}: ${prettyTy(specs[i].ty)}`)].join(', ')}): ${prettyTy(info.ret)}`);
    const capBindings: Binding[] = cs.map((s, i) => {
      if (!this.needsBox(s)) return { k: 'var', v: capVars[i] };
      const inner = (capTys[i] as Extract<Ty, { k: 'box' }>).t;
      const declTy = this.tyOf(this.checker.getTypeOfSymbol(s), fc, x.decl);
      if (inner.k === 'opt' && declTy.k !== 'opt') return { k: 'boxOpt', v: capVars[i], t: declTy };
      return { k: 'box', v: capVars[i], t: inner };
    });
    const b: Extract<Binding, { k: 'lifted' }> = { k: 'lifted', f: info, caps: cs };
    const inst: FunDeclInst = { decl: x.decl, subst: fc.subst, info, role: 'lifted', lifted: { caps: cs, capBindings } };
    created.push({ x, b, inst });
    fc.bind(x.sym, b);
  }
  // inside each lifted body, the lifted functions it can see are bound too
  for (const c of created) {
    const scope = new Map<ts.Symbol, Binding>();
    for (const d of created) scope.set(d.x.sym, d.b);
    for (const g of c.x.free.lifted) {
      const ob = this.lookup(g, fc);
      if (ob && ob.k === 'lifted' && !scope.has(g)) scope.set(g, ob);
    }
    c.inst.liftedScope = scope;
    this.instances.set(`lifted:${declId(c.x.decl)}`, c.inst);
    this.queue.push(c.inst);
  }
};

P.hoistFunctions = function (this: Translator, stmts, fc) {
  if (!stmts.length || ts.isSourceFile(stmts[0].parent)) return;
  const fds = stmts.filter(ts.isFunctionDeclaration).filter(d => d.body);
  if (!fds.length) return;
  this.liftFunctions(fds.map(d => {
    if (!d.name) reject(d, 'unsupported-syntax', 'anonymous function declaration');
    return { decl: d, sym: this.symAt(d.name)!, name: d.name.text };
  }), fc);
};

P.liftedConstArrow = function (this: Translator, d, sym, fc) {
  const init = d.initializer && skipParens(d.initializer);
  if (!init || !(ts.isArrowFunction(init) || ts.isFunctionExpression(init))) return false;
  const f = this.facts(sym);
  if (!f || this.isReassigned(sym)) return false;
  const selfRef = f.refs.some(r => within(r, init));
  if (!selfRef) return false;
  if (fc.kind === 'main' && this.globalOf.has(sym)) return false;
  this.liftFunctions([{ decl: init, sym, name: (d.name as ts.Identifier).text }], fc);
  return true;
};

P.liftedCapArgs = function (this: Translator, b, fc, node) {
  return b.caps.map((s, i) => {
    const cb = this.lookup(s, fc);
    if (!cb) reject(node, 'unsupported', `${b.f.name} is called before ${s.name} (which it uses) is declared`);
    const pt = b.f.params[i].ty;
    if (cb.k === 'box' || cb.k === 'boxOpt') return E.var(cb.v);
    if (cb.k === 'lifted') reject(node, 'unsupported', 'captured function');
    return this.coerce(this.readBinding(cb, node), pt, node);
  });
};

P.liftedAsValue = function (this: Translator, b, node, fc, target) {
  const caps = this.liftedCapArgs(b, fc, node);
  const userParams = b.f.params.slice(b.caps.length).map(p => mkVar(p.name, p.ty));
  const capVals = caps.map(c => {
    if (c.k === 'var' || c.k === 'lit') return c;
    const v = this.bindTemp(c, fc, 'cap');
    return E.var(v);
  });
  const call = E.call(b.f, [...capVals, ...userParams.map(p => E.var(p))]);
  const lam = E.lam(false, userParams, b.f.ret, [stmtItem(S.ret(call))]);
  return this.adapt(lam, target ?? this.tyAt(node, fc), node);
};

// ---------------------------------------------------------------------------------------
// globals

P.isGlobalDecl = function (this: Translator, d) {
  const list = d.parent;
  return ts.isVariableDeclarationList(list) && ts.isVariableStatement(list.parent) && ts.isSourceFile(list.parent.parent);
};

P.lowerGlobalDecl = function (this: Translator, d, fc, out) {
  if (ts.isIdentifier(d.name)) {
    const sym = this.symAt(d.name)!;
    const g = this.globalOf.get(sym);
    if (!g) reject(d, 'unsupported', `module-level variable ${d.name.text} has an unsupported type`);
    if (!d.initializer) {
      if (g.ty.k === 'opt') out.push(stmtItem(S.gset(g, E.none(g.ty.t))));
      else if (g.ty.k === 'undef') out.push(stmtItem(S.gset(g, E.undef())));
      return;
    }
    out.push(stmtItem(S.gset(g, this.lowerExpr(d.initializer, fc, g.ty))));
    return;
  }
  if (!d.initializer) reject(d, 'unsupported-syntax', 'destructuring without initialiser');
  const init = this.lowerExpr(d.initializer, fc);
  const v = this.bindTemp(init, fc, 'd');
  this.bindPattern(d.name, E.var(v), fc, out, true);
};

// ---------------------------------------------------------------------------------------
// program

function importOrder(tr: Translator, roots: ts.SourceFile[]): ts.SourceFile[] {
  const order: ts.SourceFile[] = [];
  const seen = new Set<ts.SourceFile>();
  const user = new Set(roots);
  const visit = (sf: ts.SourceFile) => {
    if (seen.has(sf)) return;
    seen.add(sf);
    for (const st of sf.statements) {
      const spec = (ts.isImportDeclaration(st) || ts.isExportDeclaration(st)) ? st.moduleSpecifier : undefined;
      if (!spec || !ts.isStringLiteral(spec)) continue;
      const res = ts.resolveModuleName(spec.text, sf.fileName, tr.program.getCompilerOptions(), ts.sys);
      const target = res.resolvedModule && tr.program.getSourceFile(res.resolvedModule.resolvedFileName);
      if (target && user.has(target)) visit(target);
    }
    order.push(sf);
  };
  for (const r of roots) visit(r);
  return order;
}

function collectNames(n: ts.BindingName, out: ts.Identifier[]): void {
  if (ts.isIdentifier(n)) { out.push(n); return; }
  for (const el of n.elements) if (!ts.isOmittedExpression(el)) collectNames(el.name, out);
}

declare module './core' {
  interface Translator {
    guard(node: ts.Node | undefined, f: () => void): void;
  }
}

P.guard = function (this: Translator, node, f) {
  try { f(); } catch (e) {
    if (e instanceof Reject) this.diags.at(e.node ?? node, e.rule, e.message);
    else if (e instanceof InternalError) this.diags.at(node, 'internal', e.message);
    else if (e instanceof Error && !(e instanceof RangeError && /call stack/.test(e.message))) {
      this.diags.at(node, 'internal', `translator error: ${e.message} (${(e.stack ?? '').split('\n')[1]?.trim() ?? ''})`);
    } else throw e;
  }
};

P.translateProgram = function (this: Translator) {
  const files = importOrder(this, this.files);
  this.analysis.run(files);
  this.analyzeIdentity(files);
  // module-level variables
  for (const sf of files) {
    for (const st of sf.statements) {
      if (!ts.isVariableStatement(st)) continue;
      for (const d of st.declarationList.declarations) {
        if (this.isRegexConst(d) || this.liftedArrow(d)) continue;
        const ids: ts.Identifier[] = [];
        collectNames(d.name, ids);
        for (const id of ids) this.guard(id, () => {
          const sym = this.symAt(id)!;
          const ty = this.types.map(this.checker.getTypeOfSymbol(sym), new Map(), id);
          this.globalOf.set(sym, this.newGlobal(id.text, ty));
        });
      }
    }
  }
  // top-level functions and classes
  for (const sf of files) {
    for (const st of sf.statements) {
      if (ts.isFunctionDeclaration(st) && st.body && !st.typeParameters?.length) {
        this.guard(st, () => { this.topFunDecl(this.symAt(st.name!)!); this.funInfoFor(st, new Map(), st); });
      }
      // a lifted `const f = (…) => …` is a top-level function like a declaration: translated even
      // when nothing calls it (before, only a use translated it, so an uncalled one was missing)
      if (ts.isVariableStatement(st)) {
        for (const d of st.declarationList.declarations) {
          const a = this.liftedArrow(d);
          if (!a || a.typeParameters?.length || isLibDecl(this.program, d)) continue;
          this.guard(d, () => { const fd = this.topFunDecl(this.symAt(d.name as ts.Identifier)!); if (fd) this.funInfoFor(fd, new Map(), d); });
        }
      }
      if (ts.isClassDeclaration(st) && !st.typeParameters?.length) {
        this.guard(st, () => {
          if (st.heritageClauses?.some(h => h.token === SK.ExtendsKeyword)) reject(st, 'no-extends', 'classes cannot extend other classes');
          const t = this.checker.getTypeAtLocation(st);
          const ci = this.types.classInst(t, new Map(), st);
          this.classCtor(ci, st);
          for (const m of st.members) {
            const name = memberName(m);
            if (!name) continue;
            if (ts.isMethodDeclaration(m)) { if (isStatic(m)) this.classStatic(ci, name, m); else this.classMember(ci, name, 'method', m); }
            else if (ts.isGetAccessorDeclaration(m) && !isStatic(m)) this.classMember(ci, name, 'getter', m);
            else if (ts.isSetAccessorDeclaration(m) && !isStatic(m)) this.classMember(ci, name, 'setter', m);
          }
        });
      }
    }
  }
  // module bodies
  const main = new FnCtx(null, 'main', false, T.undef, new Map(), files[0]);
  const mainItems: Item[] = [];
  for (const sf of files) {
    for (const st of sf.statements) {
      this.guard(st, () => {
        const items: Item[] = [];
        this.lowerStmt(st, main, items);
        mainItems.push(...items);
      });
    }
  }
  // function bodies (instantiations may enqueue more)
  for (let i = 0; i < this.queue.length; i++) {
    const inst = this.queue[i];
    this.guard(inst.decl, () => this.lowerFunBody(inst));
    if (!inst.info.body) inst.info.body = [];
  }
  if (this.diags.count) return null;
  const pir: ProgramIR = {
    namespace: '', sources: files.map(f => f.fileName), aliases: this.types.aliases, classes: this.types.classFields,
    funs: this.funs, globals: this.globals, main: [...this.fnBoxInits, ...mainItems], funDocs: this.funDocs,
  };
  return pir;
};

void tyEq; void showTy;
