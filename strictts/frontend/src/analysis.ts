// Whole-program pre-pass: per-variable facts (reassigned? captured by a closure?) and the
// object types whose fields are assigned somewhere (those become heap objects).
import * as ts from 'typescript';

export interface VarFacts {
  sym: ts.Symbol;
  decl: ts.Declaration;
  /** the function-like node (or source file) whose body declares the variable */
  owner: ts.Node;
  /** write sites after the declaration (assignment / update expressions, for-of heads) */
  writes: ts.Node[];
  /** identifier reads and writes */
  refs: ts.Identifier[];
  /** referenced from a nested function */
  captured: boolean;
  /** identifiers that reference the variable from a nested function */
  capturedRefs: ts.Identifier[];
}

export function isFunctionLike(n: ts.Node): boolean {
  return ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) ||
    ts.isMethodDeclaration(n) || ts.isConstructorDeclaration(n) || ts.isGetAccessorDeclaration(n) ||
    ts.isSetAccessorDeclaration(n) || ts.isClassStaticBlockDeclaration(n);
}

/** The function-like node whose code contains `n` (class field initialisers count as the
 * constructor of their class), or the source file. */
export function ownerOf(n: ts.Node): ts.Node {
  let cur: ts.Node | undefined = n.parent;
  let prev: ts.Node = n;
  while (cur) {
    if (isFunctionLike(cur)) {
      // parameters' default values and bodies belong to the function
      return cur;
    }
    if (ts.isPropertyDeclaration(cur) && cur.initializer === prev) {
      const cls = cur.parent;
      const ctor = (cls as ts.ClassLikeDeclaration).members.find(ts.isConstructorDeclaration);
      return ctor ?? cls;
    }
    if (ts.isSourceFile(cur)) return cur;
    prev = cur;
    cur = cur.parent;
  }
  return n.getSourceFile();
}

function skipParens(n: ts.Node): ts.Node {
  while (n.parent && ts.isParenthesizedExpression(n.parent)) n = n.parent;
  return n;
}

/** Is identifier `id` the target of an assignment or update? */
export function isWriteRef(id: ts.Identifier): ts.Node | undefined {
  const n = skipParens(id);
  const p = n.parent;
  if (!p) return undefined;
  if (ts.isBinaryExpression(p) && p.left === n &&
      p.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && p.operatorToken.kind <= ts.SyntaxKind.LastAssignment) return p;
  if ((ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p)) &&
      (p.operator === ts.SyntaxKind.PlusPlusToken || p.operator === ts.SyntaxKind.MinusMinusToken)) return p;
  if ((ts.isForOfStatement(p) || ts.isForInStatement(p)) && p.initializer === n) return p;
  // destructuring assignment targets: [a, b] = ..., ({ a } = ...)
  let q: ts.Node = n;
  while (q.parent && (ts.isArrayLiteralExpression(q.parent) || ts.isObjectLiteralExpression(q.parent) ||
    ts.isShorthandPropertyAssignment(q.parent) || ts.isPropertyAssignment(q.parent) || ts.isSpreadElement(q.parent) ||
    ts.isParenthesizedExpression(q.parent))) {
    q = q.parent;
    if (ts.isPropertyAssignment(q) && (q as ts.PropertyAssignment).name === n) return undefined;
  }
  if (q !== n && q.parent && ts.isBinaryExpression(q.parent) && q.parent.left === q &&
      q.parent.operatorToken.kind === ts.SyntaxKind.EqualsToken) return q.parent;
  if (q !== n && q.parent && ts.isForOfStatement(q.parent) && q.parent.initializer === q) return q.parent;
  return undefined;
}

/** Is identifier `id` a reference (not a declaration name, property name, label, ...)? */
function isReference(id: ts.Identifier): boolean {
  const p = id.parent;
  if (!p) return false;
  if ((ts.isVariableDeclaration(p) || ts.isParameter(p) || ts.isFunctionDeclaration(p) || ts.isClassDeclaration(p) ||
    ts.isFunctionExpression(p) || ts.isInterfaceDeclaration(p) || ts.isTypeAliasDeclaration(p) || ts.isEnumDeclaration(p) ||
    ts.isMethodDeclaration(p) || ts.isPropertyDeclaration(p) || ts.isPropertySignature(p) || ts.isMethodSignature(p) ||
    ts.isGetAccessorDeclaration(p) || ts.isSetAccessorDeclaration(p) || ts.isTypeParameterDeclaration(p) ||
    ts.isImportSpecifier(p) || ts.isImportClause(p) || ts.isNamespaceImport(p) || ts.isExportSpecifier(p) ||
    ts.isEnumMember(p) || ts.isModuleDeclaration(p)) && (p as ts.NamedDeclaration).name === id) return false;
  if (ts.isBindingElement(p) && (p.name === id || p.propertyName === id)) return p.name === id ? false : false;
  if (ts.isPropertyAccessExpression(p) && p.name === id) return false;
  if (ts.isPropertyAssignment(p) && p.name === id) return false;
  if (ts.isQualifiedName(p) && p.right === id) return false;
  if ((ts.isLabeledStatement(p) || ts.isBreakStatement(p) || ts.isContinueStatement(p)) && p.label === id) return false;
  if (ts.isTypeReferenceNode(p) || ts.isExpressionWithTypeArguments(p) || ts.isTypeQueryNode(p)) return false;
  return true;
}

/** The parameter symbol of a parameter property (`constructor(public x: T)`), whose
 * declaration also introduces a property symbol. */
export function paramSymbol(checker: ts.TypeChecker, name: ts.Identifier): ts.Symbol | undefined {
  const p = name.parent;
  if (p && ts.isParameter(p) && p.name === name && ts.isParameterPropertyDeclaration(p, p.parent)) {
    return checker.getSymbolsOfParameterPropertyDeclaration(p, name.text)[0];
  }
  return undefined;
}

export class Analysis {
  vars = new Map<ts.Symbol, VarFacts>();
  /** object types (by id) that are the base of a field assignment */
  mutatedTypes: ts.Type[] = [];
  private mutatedIds = new Set<number>();

  constructor(private checker: ts.TypeChecker) {}

  run(files: readonly ts.SourceFile[]): void {
    for (const sf of files) this.visitDecls(sf);
    for (const sf of files) this.visitRefs(sf);
  }

  private facts(sym: ts.Symbol, decl: ts.Declaration): VarFacts {
    let f = this.vars.get(sym);
    if (!f) {
      f = { sym, decl, owner: ownerOf(decl), writes: [], refs: [], captured: false, capturedRefs: [] };
      this.vars.set(sym, f);
    }
    return f;
  }

  private visitDecls(n: ts.Node): void {
    const declName = (ts.isVariableDeclaration(n) || ts.isParameter(n) || ts.isBindingElement(n)) ? n.name : undefined;
    if (declName) this.declareNames(declName, n as ts.Declaration);
    if (ts.isCatchClause(n) && n.variableDeclaration) this.declareNames(n.variableDeclaration.name, n.variableDeclaration);
    ts.forEachChild(n, c => this.visitDecls(c));
  }

  private declareNames(name: ts.BindingName, decl: ts.Declaration): void {
    if (ts.isIdentifier(name)) {
      const sym = paramSymbol(this.checker, name) ?? this.checker.getSymbolAtLocation(name);
      if (sym) this.facts(sym, ts.isBindingElement(name.parent) ? name.parent : decl);
    } else {
      for (const el of name.elements) if (!ts.isOmittedExpression(el)) this.declareNames(el.name, el);
    }
  }

  private visitRefs(n: ts.Node): void {
    if (ts.isIdentifier(n) && isReference(n)) {
      let sym = this.checker.getSymbolAtLocation(n);
      if (n.parent && ts.isShorthandPropertyAssignment(n.parent) && n.parent.name === n) {
        sym = this.checker.getShorthandAssignmentValueSymbol(n.parent) ?? sym;
      }
      const f = sym && this.vars.get(sym);
      if (f) {
        f.refs.push(n);
        const w = isWriteRef(n);
        if (w) f.writes.push(w);
        if (ownerOf(n) !== f.owner) { f.captured = true; f.capturedRefs.push(n); }
      }
    }
    // field assignments: base.f = ..., base.f += ..., base.f++
    let target: ts.Expression | undefined;
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment) target = n.left;
    else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken)) target = n.operand;
    while (target && ts.isParenthesizedExpression(target)) target = target.expression;
    if (target && ts.isPropertyAccessExpression(target)) this.markMutated(target.expression);
    ts.forEachChild(n, c => this.visitRefs(c));
  }

  private markMutated(base: ts.Expression): void {
    const t = this.checker.getTypeAtLocation(base);
    const parts = t.isUnion() ? t.types : [t];
    for (const p of parts) {
      if (!(p.flags & ts.TypeFlags.Object)) continue;
      const sym = p.getSymbol();
      if (sym && (sym.flags & ts.SymbolFlags.Class)) continue; // classes are heap objects anyway
      const id = (p as { id?: number }).id ?? -1;
      if (!this.mutatedIds.has(id)) { this.mutatedIds.add(id); this.mutatedTypes.push(p); }
    }
  }

  isMutatedId(t: ts.Type): boolean { return this.mutatedIds.has((t as { id?: number }).id ?? -1); }
}
