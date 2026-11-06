// Tagged values as TypeScript/JavaScript expressions (for reports and for the Lean driver).
import { Tagged } from './gen';

const IDENT = /^[A-Za-z_$][A-Za-z0-9_$]*$/;

export function numText(v: number | string): string {
  switch (v) {
    case 'NaN': return 'NaN';
    case 'Inf': return 'Infinity';
    case '-Inf': return '-Infinity';
    case '-0': return '-0';
  }
  return String(v);
}

/** A TypeScript expression for the value; Map/Set/array element types come from the context. */
export function tsLiteral(t: Tagged | null): string {
  if (t === null) return 'undefined';
  switch (t.t) {
    case 'n': return numText(t.v);
    case 's': return JSON.stringify(t.v);
    case 'b': return `${t.v}n`;
    case 'B': return String(t.v);
    case 'u': return 'undefined';
    case 'z': return 'null';
    case 'a': return '[' + t.v.map(tsLiteral).join(', ') + ']';
    case 'o': return t.v.length ? '{ ' + t.v.map(([k, x]) => (IDENT.test(k) ? k : JSON.stringify(k)) + ': ' + tsLiteral(x)).join(', ') + ' }' : '{}';
    case 'm': return t.v.length ? 'new Map([' + t.v.map(([k, x]) => `[${tsLiteral(k)}, ${tsLiteral(x)}]`).join(', ') + '])' : 'new Map()';
    case 'S': return t.v.length ? 'new Set([' + t.v.map(tsLiteral).join(', ') + '])' : 'new Set()';
    case 'c': return `new ${t.cls}(${t.args.map(tsLiteral).join(', ')})`;
    case 'ta': return `new ${t.kind}([${t.v.map(tsLiteral).join(', ')}])`;
    case 'd': return `new Date(${t.v})`;
    case 'p': return `Promise.resolve(${tsLiteral(t.v)})`;
  }
}

export function callText(name: string, args: (Tagged | null)[], self?: (Tagged | null)[], cls?: string, kind?: string): string {
  const a = args.map(tsLiteral).join(', ');
  if (kind === 'method' && cls) return `new ${cls}(${(self ?? []).map(tsLiteral).join(', ')}).${name.slice(cls.length + 1)}(${a})`;
  if (kind === 'ctor' && cls) return `new ${cls}(${a})`;
  return `${name}(${a})`;
}
