// Diagnostics in the format `file:line:col [rule-id] message`.
import * as ts from 'typescript';
import * as path from 'path';

export interface Diag { file: string; line: number; col: number; rule: string; msg: string }

export class Diags {
  list: Diag[] = [];
  private seen = new Set<string>();
  constructor(private cwd: string) {}

  at(node: ts.Node | undefined, rule: string, msg: string): void {
    let file = '<unknown>', line = 0, col = 0;
    if (node) {
      const sf = node.getSourceFile();
      if (sf) {
        file = path.relative(this.cwd, sf.fileName) || sf.fileName;
        const pos = sf.getLineAndCharacterOfPosition(node.getStart(sf));
        line = pos.line + 1;
        col = pos.character + 1;
      }
    }
    this.push({ file, line, col, rule, msg });
  }

  push(d: Diag): void {
    const key = `${d.file}:${d.line}:${d.col}:${d.rule}:${d.msg}`;
    if (this.seen.has(key)) return;
    this.seen.add(key);
    this.list.push(d);
  }

  fromTs(d: ts.Diagnostic): void {
    const msg = ts.flattenDiagnosticMessageText(d.messageText, ' ');
    if (d.file && d.start !== undefined) {
      const pos = d.file.getLineAndCharacterOfPosition(d.start);
      this.push({ file: path.relative(this.cwd, d.file.fileName) || d.file.fileName, line: pos.line + 1, col: pos.character + 1, rule: `ts${d.code}`, msg });
    } else this.push({ file: '<options>', line: 0, col: 0, rule: `ts${d.code}`, msg });
  }

  get count(): number { return this.list.length; }

  format(): string {
    const sorted = [...this.list].sort((a, b) => a.file < b.file ? -1 : a.file > b.file ? 1 : a.line - b.line || a.col - b.col);
    return sorted.map(d => `${d.file}:${d.line}:${d.col} [${d.rule}] ${d.msg}`).join('\n');
  }
}

/** A diagnostic raised while translating: aborts the current function. */
export class Reject extends Error {
  /** for `external-type`: the external type's name (coverage reports) */
  extName?: string;
  constructor(public node: ts.Node | undefined, public rule: string, msg: string) { super(msg); }
}

export function reject(node: ts.Node | undefined, rule: string, msg: string, extName?: string): never {
  const r = new Reject(node, rule, msg);
  r.extName = extName;
  if (process.env.STRICTTS_DEBUG) process.stderr.write(`[debug] ${rule}: ${msg}\n${r.stack}\n`);
  throw r;
}
