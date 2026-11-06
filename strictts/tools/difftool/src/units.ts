// Function units of a source file: top-level functions, `const f = (…) => …`, class methods
// and constructors, with a normalized text (comments and formatting removed) used to decide
// whether a unit changed.
import * as ts from 'typescript';
import { Project } from './project';

export type UnitKind = 'function' | 'arrow' | 'method' | 'static' | 'ctor';

export interface Unit {
  /** module key + '::' + qualified name */
  key: string;
  file: string;
  /** f, C.m, C.constructor */
  name: string;
  kind: UnitKind;
  cls?: string;
  /** the function-like node */
  fn: ts.FunctionLikeDeclaration;
  /** the top-level statement that contains it */
  stmt: ts.Statement;
  text: string;
  isAsync: boolean;
  isGeneric: boolean;
  exported: boolean;
  /** private/protected or #private member (not callable from outside the class) */
  isPrivate: boolean;
  line: number;
  /** the type text of each parameter without a type annotation (the checker's, e.g. of a default
   * value `end = arr.length`); undefined for annotated parameters */
  paramTypes: (string | undefined)[];
}

const printer = ts.createPrinter({ removeComments: true, newLine: ts.NewLineKind.LineFeed });

export function normText(node: ts.Node, sf: ts.SourceFile): string {
  return printer.printNode(ts.EmitHint.Unspecified, node, sf);
}

function hasMod(n: ts.Node, k: ts.SyntaxKind): boolean {
  return !!(ts.canHaveModifiers(n) && ts.getModifiers(n)?.some(m => m.kind === k));
}

export function unitsOf(p: Project, file: string, moduleKey: string): Unit[] {
  const sf = p.sf(file);
  if (!sf) return [];
  const out: Unit[] = [];
  const add = (name: string, kind: UnitKind, fn: ts.FunctionLikeDeclaration, stmt: ts.Statement, textNode: ts.Node, cls?: string) => {
    const isAsync = hasMod(fn, ts.SyntaxKind.AsyncKeyword);
    const isGeneric = !!(fn.typeParameters && fn.typeParameters.length) ||
      !!(cls && ts.isClassDeclaration(stmt) && stmt.typeParameters && stmt.typeParameters.length);
    out.push({
      key: `${moduleKey}::${name}`, file, name, kind, cls, fn, stmt, text: normText(textNode, sf), isAsync, isGeneric,
      exported: hasMod(stmt, ts.SyntaxKind.ExportKeyword), line: sf.getLineAndCharacterOfPosition(fn.getStart(sf)).line + 1,
      isPrivate: !!cls && (hasMod(fn, ts.SyntaxKind.PrivateKeyword) || hasMod(fn, ts.SyntaxKind.ProtectedKeyword) || (!!fn.name && ts.isPrivateIdentifier(fn.name))),
      // (an optional parameter: without the undefined its default value excludes; the wrapper marks it optional)
      paramTypes: fn.parameters.map(q => {
        if (q.type) return undefined;
        const t = p.checker.getTypeAtLocation(q);
        return p.checker.typeToString(q.questionToken || q.initializer ? p.checker.getNonNullableType(t) : t, q, ts.TypeFormatFlags.NoTruncation);
      }),
    });
  };
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && st.name && st.body) add(st.name.text, 'function', st, st, st);
    else if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) {
        if (!ts.isIdentifier(d.name) || !d.initializer) continue;
        let init: ts.Expression = d.initializer;
        while (ts.isParenthesizedExpression(init) || ts.isAsExpression(init) || ts.isSatisfiesExpression(init)) init = init.expression;
        if (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) add(d.name.text, 'arrow', init, st, d);
      }
    } else if (ts.isClassDeclaration(st) && st.name) {
      const c = st.name.text;
      for (const m of st.members) {
        if (ts.isConstructorDeclaration(m) && m.body) add(`${c}.constructor`, 'ctor', m, st, m, c);
        else if (ts.isMethodDeclaration(m) && m.body && (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name))) {
          const isStatic = hasMod(m, ts.SyntaxKind.StaticKeyword);
          add(`${c}.${m.name.text}`, isStatic ? 'static' : 'method', m, st, m, c);
        }
      }
    }
  }
  return out;
}

/** Normalized text of everything in the file that is not one of its function units
 * (types, module variables, imports, class fields): used to decide whether a dependency of
 * an unchanged function changed. */
export function moduleContextText(p: Project, file: string): string {
  const sf = p.sf(file);
  if (!sf) return '';
  const parts: string[] = [];
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st)) continue;
    if (ts.isClassDeclaration(st)) {
      parts.push(normText(ts.factory.updateClassDeclaration(st, st.modifiers, st.name, st.typeParameters, st.heritageClauses,
        st.members.filter(m => !(ts.isMethodDeclaration(m) || ts.isConstructorDeclaration(m)))), sf));
      continue;
    }
    parts.push(normText(st, sf));
  }
  return parts.join('\n');
}
