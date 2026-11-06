// Drivers: TypeScript code appended to a slice's entry file that calls the target on given
// inputs and prints the outcome, the console output and the arguments afterwards. The same
// driver runs under Node and (after translation) under the Lean semantics, so Lean confirms a
// counterexample without any hand-written Lean value construction, and `validate` compares
// Node with Lean on the same function.
import { Desc, Signature, Param } from './typedesc';
import { Input, Tagged, memberFor } from './gen';
import { tsLiteral } from './literal';
import { Unit } from './units';

const PRELUDE = `
// ---- difftool driver ----
function __dt_num(x: number): string { return x === 0 && 1 / x < 0 ? "-0" : String(x); }
function __dt_hex4(c: number): string {
  const h = "0123456789abcdef";
  return h.charAt(Math.floor(c / 4096) % 16) + h.charAt(Math.floor(c / 256) % 16) + h.charAt(Math.floor(c / 16) % 16) + h.charAt(c % 16);
}
function __dt_str(s: string): string {
  let r = "\\"";
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c >= 32 && c < 127 && c !== 34 && c !== 92) r = r + s.charAt(i);
    else r = r + "\\\\u" + __dt_hex4(c);
  }
  return r + "\\"";
}
function __dt_arr<T>(xs: readonly T[], f: (x: T) => string): string {
  let s = "[";
  for (let i = 0; i < xs.length; i++) { if (i > 0) s = s + ", "; s = s + f(xs[i]); }
  return s + "]";
}
function __dt_opt<T>(x: T | undefined, f: (y: T) => string): string { return x === undefined ? "undefined" : f(x); }
function __dt_nul<T>(x: T | null, f: (y: T) => string): string { return x === null ? "null" : f(x); }
function __dt_map<K, V>(m: ReadonlyMap<K, V>, fk: (k: K) => string, fv: (v: V) => string): string {
  let s = "Map{";
  let first = true;
  for (const [k, v] of m) { if (!first) s = s + ", "; first = false; s = s + fk(k) + " => " + fv(v); }
  return s + "}";
}
function __dt_set<T>(m: ReadonlySet<T>, f: (x: T) => string): string {
  let s = "Set{";
  let first = true;
  for (const x of m) { if (!first) s = s + ", "; first = false; s = s + f(x); }
  return s + "}";
}
`;

const IDENT = /^[A-Za-z_$][A-Za-z0-9_$]*$/;

class ShowGen {
  helpers: string[] = [];
  private primHelpers = new Map<string, string>();
  constructor(private table: Map<number, Desc>) {}

  private resolve(d: Desc): Desc {
    let x = d;
    for (let i = 0; x.k === 'ref' && i < 50; i++) x = this.table.get(x.id) ?? { k: 'unsupported', why: 'ref' };
    return x;
  }

  private primType(d: Desc): string | null {
    switch (d.k) {
      case 'num': return 'number'; case 'str': return 'string'; case 'bool': return 'boolean'; case 'big': return 'bigint';
      case 'undef': return 'undefined'; case 'null': return 'null';
      case 'lit': return d.v.t === 'n' ? 'number' : d.v.t === 's' ? 'string' : d.v.t === 'B' ? 'boolean' : d.v.t === 'b' ? 'bigint' : d.v.t === 'u' ? 'undefined' : 'null';
      default: return null;
    }
  }

  /** A TypeScript expression of type string showing the value of expression `v`. */
  show(d0: Desc, v: string, depth: number): string {
    const d = this.resolve(d0);
    if (depth > 6) return '"…"';
    const x = `__dt_x${depth}`;
    switch (d.k) {
      case 'num': return `__dt_num(${v})`;
      case 'str': return `__dt_str(${v})`;
      case 'bool': return `(${v} ? "true" : "false")`;
      case 'big': return `(String(${v}) + "n")`;
      case 'undef': return '"undefined"';
      case 'null': return '"null"';
      case 'lit': {
        switch (d.v.t) {
          case 's': return `__dt_str(${v})`; case 'n': return `__dt_num(${v})`; case 'B': return `(${v} ? "true" : "false")`;
          case 'b': return `(String(${v}) + "n")`; case 'u': return '"undefined"'; case 'z': return '"null"';
        }
        return '"?"';
      }
      case 'arr': return `__dt_arr(${v}, (${x}) => ${this.show(d.t, x, depth + 1)})`;
      case 'tup': {
        const els = d.ts.slice(0, d.req).map((t, i) => this.show(t, `${v}[${i}]`, depth + 1));
        return els.length ? `("[" + ${els.join(' + ", " + ')} + "]")` : '"[]"';
      }
      case 'obj': {
        const parts = d.fields.map(f => {
          const acc = IDENT.test(f.name) ? `${v}.${f.name}` : `${v}[${JSON.stringify(f.name)}]`;
          const s = f.opt ? `__dt_opt(${acc}, (${x}) => ${this.show(f.t, x, depth + 1)})` : this.show(f.t, acc, depth + 1);
          return `${JSON.stringify(f.name + ': ')} + ${s}`;
        });
        return parts.length ? `("{" + ${parts.join(' + ", " + ')} + "}")` : '"{}"';
      }
      case 'class': {
        const parts = d.fields.map(f => {
          const acc = `${v}.${f.name}`;
          const s = f.opt ? `__dt_opt(${acc}, (${x}) => ${this.show(f.t, x, depth + 1)})` : this.show(f.t, acc, depth + 1);
          return `${JSON.stringify(f.name + ': ')} + ${s}`;
        });
        return parts.length ? `(${JSON.stringify(d.name + '{')} + ${parts.join(' + ", " + ')} + "}")` : JSON.stringify(d.name + '{}');
      }
      case 'map': return `__dt_map(${v}, (${x}k) => ${this.show(d.key, x + 'k', depth + 1)}, (${x}) => ${this.show(d.val, x, depth + 1)})`;
      case 'set': return `__dt_set(${v}, (${x}) => ${this.show(d.t, x, depth + 1)})`;
      case 'union': {
        const ms = d.ts.map(m => this.resolve(m));
        const undef = ms.filter(m => m.k === 'undef' || (m.k === 'lit' && m.v.t === 'u'));
        const nul = ms.filter(m => m.k === 'null' || (m.k === 'lit' && m.v.t === 'z'));
        const rest = ms.filter(m => !undef.includes(m) && !nul.includes(m));
        const inner: Desc = rest.length === 1 ? rest[0] : { k: 'union', ts: rest };
        if (undef.length && rest.length) return `__dt_opt(${v}, (${x}) => ${nul.length ? `__dt_nul(${x}, (${x}n) => ${this.show(inner, x + 'n', depth + 1)})` : this.show(inner, x, depth + 1)})`;
        if (nul.length && rest.length) return `__dt_nul(${v}, (${x}) => ${this.show(inner, x, depth + 1)})`;
        // unions of primitives: typeof dispatch in a helper
        const kinds = [...new Set(rest.map(m => this.primType(m)))];
        if (kinds.every(k => k !== null) && kinds.length > 1) {
          const key = kinds.join('|');
          let h = this.primHelpers.get(key);
          if (!h) {
            h = `__dt_p${this.primHelpers.size}`;
            this.primHelpers.set(key, h);
            const show1 = (k: string) => k === 'number' ? '__dt_num(x)' : k === 'string' ? '__dt_str(x)' : k === 'boolean' ? '(x ? "true" : "false")' : '(String(x) + "n")';
            let body = '';
            kinds.forEach((k, i) => { body += i < kinds.length - 1 ? `typeof x === "${k}" ? ${show1(k!)} : ` : show1(k!); });
            this.helpers.push(`function ${h}(x: ${kinds.join(' | ')}): string { return ${body}; }`);
          }
          return `${h}(${v})`;
        }
        if (kinds.length === 1 && kinds[0]) return this.show(rest[0], v, depth);
        return '"<union>"';
      }
      default: return '"<value>"';
    }
  }
}

export interface DriverOpts {
  /** the driver prints one block per input */
  inputs: Input[];
}

/** TypeScript type text of a descriptor (null when it has no simple spelling). */
function tsType(d0: Desc, table: Map<number, Desc>, depth = 0): string | null {
  if (depth > 6) return null;
  let d = d0;
  for (let i = 0; d.k === 'ref' && i < 50; i++) d = table.get(d.id) ?? { k: 'unsupported', why: 'ref' };
  const sub = (x: Desc) => tsType(x, table, depth + 1);
  switch (d.k) {
    case 'num': return 'number'; case 'str': return 'string'; case 'bool': return 'boolean'; case 'big': return 'bigint';
    case 'undef': return 'undefined'; case 'null': return 'null';
    case 'lit': return d.v.t === 's' ? JSON.stringify(d.v.v) : d.v.t === 'B' ? String(d.v.v) : d.v.t === 'u' ? 'undefined' : d.v.t === 'z' ? 'null' : d.v.t === 'b' ? `${d.v.v}n` : null;
    case 'arr': { const e = sub(d.t); return e ? `(${e})[]` : null; }
    case 'set': { const e = sub(d.t); return e ? `Set<${e}>` : null; }
    case 'map': { const k = sub(d.key), v = sub(d.val); return k && v ? `Map<${k}, ${v}>` : null; }
    case 'class': return d.name;
    case 'union': { const ms = d.ts.map(sub); return ms.every(m => m) ? ms.join(' | ') : null; }
    case 'obj': {
      if (d.name && /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(d.name) && d.name !== '__type' && d.name !== '__object') return d.name;
      const fs = d.fields.map(f => { const t = sub(f.t); return t ? `${JSON.stringify(f.name)}${f.opt ? '?' : ''}: ${t}` : null; });
      return fs.every(f => f) ? `{ ${fs.join('; ')} }` : null;
    }
    default: return null;
  }
}

/** Literal of a value of type `unknown`: every nested element and field asserted to `unknown`, so
 * that TypeScript infers no union type for a heterogeneous array or object literal. */
function dynLiteral(t: Tagged | null, depth = 0): string {
  if (t === null || depth > 20) return tsLiteral(t);
  switch (t.t) {
    case 'a': return '[' + t.v.map(x => `(${dynLiteral(x, depth + 1)} as unknown)`).join(', ') + ']';
    case 'o': return t.v.length ? '{ ' + t.v.map(([k, x]) => `${/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(k) ? k : JSON.stringify(k)}: (${dynLiteral(x, depth + 1)} as unknown)`).join(', ') + ' }' : '{}';
    default: return tsLiteral(t);
  }
}

/** Literal of a value of type `d`; empty collections inside unions get an assertion to their member type. */
function tsLiteralD(t: Tagged | null, d0: Desc, table: Map<number, Desc>, depth = 0): string {
  if (t === null || depth > 20) return tsLiteral(t);
  let d = d0;
  for (let i = 0; d.k === 'ref' && i < 50; i++) d = table.get(d.id) ?? { k: 'unsupported', why: 'ref' };
  // (asserted to `unknown` here too: an array or object literal nested at a field or element of
  // type `unknown` would otherwise be a literal of type `unknown`, which the translator rejects)
  if (d.k === 'unknown') return `(${dynLiteral(t, depth)} as unknown)`;
  if (d.k === 'union') {
    const m = memberFor(d, t, { table });
    if (!m) return tsLiteral(t);
    const lit = tsLiteralD(t, m, table, depth + 1);
    const ty = tsType(m, table);
    const empty = (t.t === 'a' || t.t === 'm' || t.t === 'S') && t.v.length === 0;
    return empty && ty ? `(${lit} as ${ty})` : lit;
  }
  switch (t.t) {
    case 'a': {
      const et = d.k === 'arr' ? (_: number) => d.t : d.k === 'tup' ? (i: number) => (i < d.ts.length ? d.ts[i] : d.rest ?? d.ts[0]) : null;
      return et ? '[' + t.v.map((x, i) => tsLiteralD(x, et(i), table, depth + 1)).join(', ') + ']' : tsLiteral(t);
    }
    case 'o': {
      if (d.k !== 'obj') return tsLiteral(t);
      if (!t.v.length) return '{}';
      return '{ ' + t.v.map(([k, x]) => {
        const f = d.fields.find(f => f.name === k);
        const ft = f ? f.t : d.index?.t;
        return (/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(k) ? k : JSON.stringify(k)) + ': ' + (ft ? tsLiteralD(x, ft, table, depth + 1) : tsLiteral(x));
      }).join(', ') + ' }';
    }
    // (explicit type arguments: `new Map()` alone is a Map<any, any>, which the translator rejects)
    case 'm': {
      if (d.k !== 'map') return tsLiteral(t);
      const k = tsType(d.key, table), v = tsType(d.val, table);
      const targs = k && v ? `<${k}, ${v}>` : '';
      return t.v.length ? `new Map${targs}([` + t.v.map(([kk, x]) => `[${tsLiteralD(kk, d.key, table, depth + 1)}, ${tsLiteralD(x, d.val, table, depth + 1)}]`).join(', ') + '])' : `new Map${targs}()`;
    }
    case 'S': {
      if (d.k !== 'set') return tsLiteral(t);
      const e = tsType(d.t, table);
      const targs = e ? `<${e}>` : '';
      return t.v.length ? `new Set${targs}([` + t.v.map(x => tsLiteralD(x, d.t, table, depth + 1)).join(', ') + '])' : `new Set${targs}()`;
    }
    case 'c': return d.k === 'class' ? `new ${t.cls}(${t.args.map((a, i) => d.ctor[Math.min(i, d.ctor.length - 1)] ? tsLiteralD(a, d.ctor[Math.min(i, d.ctor.length - 1)].t, table, depth + 1) : tsLiteral(a)).join(', ')})` : tsLiteral(t);
    default: return tsLiteral(t);
  }
}

function argDecl(p: Param, name: string, t: Tagged | null, table: Map<number, Desc>): string {
  // an assertion keeps the declared (union) type: a typed const would be narrowed to its literal
  const lit = tsLiteralD(t, p.t, table);
  return `const ${name} = (${lit}) as (${p.text})${p.opt ? ' | undefined' : ''};`;
}

/** A parameter's declared type at the instance the inputs were generated for (typedesc: an
 * unconstrained type parameter := number, a constrained one := its constraint): the driver is
 * top-level code, where the function's type parameters are not in scope. */
function instParam(u: Unit, p: Param): Param {
  let text = p.text;
  for (const tp of u.fn.typeParameters ?? []) {
    const inst = tp.constraint ? `(${tp.constraint.getText()})` : 'number';
    text = text.replace(new RegExp(`\\b${tp.name.text}\\b`, 'g'), inst);
  }
  return text === p.text ? p : { ...p, text };
}

/** Driver source to append to the entry file of a slice. */
export function driverSource(u: Unit, sig: Signature, inputs: Input[]): string {
  const g = new ShowGen(sig.table);
  const isAsync = sig.isAsync || sig.ret.k === 'promise';
  const retDesc = sig.ret.k === 'promise' ? sig.ret.t : sig.ret;
  const blocks: string[] = [];
  const cls = u.cls;
  const method = cls ? u.name.slice(cls.length + 1) : '';
  inputs.forEach((inp, idx) => {
    const lines: string[] = [];
    const names: string[] = [];
    const showArgs: string[] = [];
    let pi = 0;
    inp.args.forEach((a, i) => {
      const p = sig.params[Math.min(i, sig.params.length - 1)];
      if (!p) return;
      const nm = `__dt_a${i}`;
      if (p.rest) {
        const et = p.t.k === 'arr' ? p.t.t : p.t;
        const elemParam: Param = { ...p, t: et, rest: false, opt: false, text: p.text.replace(/\[\]$/, '') };
        lines.push(argDecl(instParam(u, elemParam), nm, a, sig.table));
        showArgs.push(g.show(et, nm, 0));
      } else {
        lines.push(argDecl(instParam(u, p), nm, a, sig.table));
        showArgs.push(p.opt ? `__dt_opt(${nm}, (__dt_o) => ${g.show(p.t, '__dt_o', 1)})` : g.show(p.t, nm, 0));
        pi = i + 1;
      }
      names.push(nm);
    });
    void pi;
    let call: string;
    if (u.kind === 'method' && cls && sig.self) {
      const sargs = (inp.self ?? []).map((a, i) => { const p = sig.self!.ctor[Math.min(i, sig.self!.ctor.length - 1)]; const nm = `__dt_s${i}`; lines.push(argDecl(p, nm, a, sig.table)); return nm; });
      lines.push(`const __dt_self = new ${cls}(${sargs.join(', ')});`);
      call = `__dt_self.${method}(${names.join(', ')})`;
    } else if (u.kind === 'static' && cls) call = `${cls}.${method}(${names.join(', ')})`;
    else if (u.kind === 'ctor' && cls) call = `new ${cls}(${names.join(', ')})`;
    else call = `${u.name}(${names.join(', ')})`;
    const voidRet = retDesc.k === 'undef' && u.kind !== 'ctor';
    const selfD: Desc = sig.selfDesc ?? { k: 'unsupported', why: 'receiver' };
    const retShow = u.kind === 'ctor' ? g.show(selfD, '__dt_r', 0) : g.show(retDesc, '__dt_r', 0);
    const ok = isAsync ? 'resolve' : 'return';
    const bad = isAsync ? 'reject' : 'throw';
    const callStmt = voidRet
      ? `${isAsync ? 'await ' : ''}${call};\n      console.log("${ok} undefined");`
      : `const __dt_r = ${isAsync ? 'await ' : ''}${call};\n      console.log("${ok} " + ${retShow});`;
    blocks.push(`  {
    console.log("#${idx}");
    ${lines.join('\n    ')}
    try {
      ${callStmt}
    } catch (__dt_e) {
      console.log("${bad} " + (__dt_e as Error).name + ": " + (__dt_e as Error).message);
    }
    console.log("args " + ${showArgs.length ? showArgs.join(' + " | " + ') : '""'});${u.kind === 'method' ? `\n    console.log("self " + ${g.show(selfD, '__dt_self', 0)});` : ''}
  }`);
  });
  const main = `${isAsync ? 'async ' : ''}function __dt_main(): ${isAsync ? 'Promise<void>' : 'void'} {\n${blocks.join('\n')}\n}\n__dt_main();\n`;
  return PRELUDE + g.helpers.join('\n') + '\n' + main;
}
