// Slices: a changed function together with everything it needs (functions, classes, types,
// module variables, the module statements that initialise them), as a pruned copy of the
// original files. Imports keep their structure, so a slice is translated and run exactly like
// the original modules, restricted to the declarations the function depends on.
import * as fs from 'fs';
import * as path from 'path';
import * as ts from 'typescript';
import { FileSet } from './spec';
import { Project, makeProject } from './project';
import { Unit } from './units';
import { writeFile } from './util';

export interface Slice {
  ok: boolean;
  reason?: string;
  /** root directory of the slice files */
  dir: string;
  /** relative path of the file that defines the target */
  entry: string;
  files: Map<string, string>;
  /** name under which the entry module exports the target (function or class) */
  exportName: string;
  /** external modules whose values the slice uses (it cannot run without them) */
  externals: string[];
  /** external modules used only for types */
  typeExternals: string[];
  /** identifiers that resolve to nothing in the ECMAScript library (host globals such as `process`) */
  hostGlobals: string[];
  /** literal module constants that were inlined (proof variant) */
  inlined: string[];
}

function topLevel(n: ts.Node): ts.Statement | undefined {
  let c: ts.Node | undefined = n;
  while (c && c.parent && !ts.isSourceFile(c.parent)) c = c.parent;
  return c && c.parent && ts.isSourceFile(c.parent) ? c as ts.Statement : undefined;
}

function inTypePosition(n: ts.Node): boolean {
  for (let c: ts.Node | undefined = n.parent; c; c = c.parent) {
    if (ts.isTypeNode(c) || ts.isInterfaceDeclaration(c) || ts.isTypeAliasDeclaration(c)) return true;
    if (ts.isHeritageClause(c)) return c.token === ts.SyntaxKind.ImplementsKeyword;
    if (ts.isStatement(c) || ts.isSourceFile(c)) return false;
  }
  return false;
}

function isPropertyName(id: ts.Identifier): boolean {
  const p = id.parent;
  return !!p && ((ts.isPropertyAccessExpression(p) && p.name === id) || (ts.isPropertyAssignment(p) && p.name === id) ||
    (ts.isQualifiedName(p) && p.right === id) || ((ts.isMethodDeclaration(p) || ts.isPropertyDeclaration(p) ||
      ts.isPropertySignature(p) || ts.isMethodSignature(p) || ts.isGetAccessor(p) || ts.isSetAccessor(p) ||
      ts.isEnumMember(p)) && p.name === id) || (ts.isBindingElement(p) && p.propertyName === id) ||
    (ts.isImportSpecifier(p) && p.propertyName === id) || (ts.isExportSpecifier(p) && p.propertyName === id) ||
    ts.isLabeledStatement(p) || ts.isBreakOrContinueStatement(p) || (ts.isJsxAttribute(p) && p.name === id));
}

function isDeclName(id: ts.Identifier): boolean {
  const p = id.parent as ts.Node & { name?: ts.Node };
  return !!p && p.name === id && (ts.isVariableDeclaration(p) || ts.isFunctionDeclaration(p) || ts.isParameter(p) ||
    ts.isClassDeclaration(p) || ts.isInterfaceDeclaration(p) || ts.isTypeAliasDeclaration(p) || ts.isBindingElement(p) ||
    ts.isTypeParameterDeclaration(p) || ts.isFunctionExpression(p) || ts.isClassExpression(p) || ts.isEnumDeclaration(p) ||
    ts.isImportSpecifier(p) || ts.isImportClause(p) || ts.isNamespaceImport(p));
}

const ES_GLOBAL_VALUES = new Set(['undefined', 'NaN', 'Infinity', 'globalThis']);

interface Closure {
  stmts: Map<ts.SourceFile, Set<ts.Statement>>;
  imports: Map<ts.ImportDeclaration, Set<string>>;
  wholeFiles: Set<ts.SourceFile>;
  externals: Set<string>;
  typeExternals: Set<string>;
  hostGlobals: Set<string>;
}

function moduleNameOf(decl: ts.Declaration): string | undefined {
  let c: ts.Node | undefined = decl;
  while (c && !ts.isImportDeclaration(c)) c = c.parent;
  return c && ts.isImportDeclaration(c) && ts.isStringLiteral(c.moduleSpecifier) ? c.moduleSpecifier.text : undefined;
}

function closure(p: Project, start: ts.Statement): Closure {
  const checker = p.checker;
  const cl: Closure = { stmts: new Map(), imports: new Map(), wholeFiles: new Set(), externals: new Set(), typeExternals: new Set(), hostGlobals: new Set() };
  const queue: ts.Statement[] = [];
  const add = (st: ts.Statement) => {
    const sf = st.getSourceFile();
    let s = cl.stmts.get(sf);
    if (!s) { s = new Set(); cl.stmts.set(sf, s); }
    if (s.has(st)) return;
    s.add(st);
    queue.push(st);
  };
  const inSet = (sf: ts.SourceFile) => p.isUser(sf) || (sf.isDeclarationFile && path.resolve(sf.fileName).startsWith(path.resolve(p.set.dir) + path.sep) && !sf.fileName.includes('/node_modules/'));
  const visitId = (id: ts.Identifier) => {
    if (isPropertyName(id)) {
      // property names: their declarations (interfaces, classes) are needed for types and methods
      const s = checker.getSymbolAtLocation(id);
      if (s) for (const d of s.declarations ?? []) { const sf = d.getSourceFile(); if (inSet(sf) && !sf.isDeclarationFile) { const t = topLevel(d); if (t) add(t); } }
      return;
    }
    let sym = checker.getSymbolAtLocation(id);
    if (!sym) {
      if (!isDeclName(id) && !ES_GLOBAL_VALUES.has(id.text) && !inTypePosition(id)) cl.hostGlobals.add(id.text);
      return;
    }
    if (sym.flags & ts.SymbolFlags.Alias) {
      for (const d of sym.declarations ?? []) {
        let imp: ts.Node | undefined = d;
        while (imp && !ts.isImportDeclaration(imp)) imp = imp.parent;
        if (imp && ts.isImportDeclaration(imp)) {
          let names = cl.imports.get(imp);
          if (!names) { names = new Set(); cl.imports.set(imp, names); }
          names.add(id.text);
        }
      }
      const decl0 = sym.declarations?.[0];
      let target: ts.Symbol;
      try { target = checker.getAliasedSymbol(sym); } catch { target = sym; }
      const tdecls = target.declarations ?? [];
      const external = tdecls.length === 0 || tdecls.every(d => !inSet(d.getSourceFile()));
      if (external) {
        const m = decl0 ? moduleNameOf(decl0) : undefined;
        if (m) (inTypePosition(id) ? cl.typeExternals : cl.externals).add(m);
        return;
      }
      // a namespace object used other than as `ns.member` (e.g. `ns[name]`) needs the whole module
      if (decl0 && ts.isNamespaceImport(decl0) && !inTypePosition(id) &&
          !(id.parent && ts.isPropertyAccessExpression(id.parent) && id.parent.expression === id)) {
        for (const d of tdecls) if (ts.isSourceFile(d) && inSet(d) && !d.isDeclarationFile) for (const st of d.statements) add(st);
      }
      sym = target;
    }
    for (const d of sym.declarations ?? []) {
      const sf = d.getSourceFile();
      if (p.program.isSourceFileDefaultLibrary(sf)) continue;
      if (!inSet(sf)) {
        if (!inTypePosition(id)) cl.hostGlobals.add(id.text);
        continue;
      }
      if (sf.isDeclarationFile) { cl.wholeFiles.add(sf); continue; }
      const t = topLevel(d);
      if (t) add(t);
    }
  };
  const walk = (n: ts.Node) => {
    if (ts.isIdentifier(n)) visitId(n);
    else if (ts.isShorthandPropertyAssignment(n)) {
      const s = checker.getShorthandAssignmentValueSymbol(n);
      if (s) for (const d of s.declarations ?? []) { const t = topLevel(d); if (t && inSet(d.getSourceFile())) add(t); }
    }
    ts.forEachChild(n, walk);
  };
  add(start);
  for (;;) {
    while (queue.length) walk(queue.shift()!);
    // module statements that initialise or update a needed module variable
    const varSyms = new Set<ts.Symbol>();
    for (const [, ss] of cl.stmts) for (const st of ss) if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) { const s = checker.getSymbolAtLocation(d.name); if (s) varSyms.add(s); }
    }
    let grew = false;
    for (const sf of [...cl.stmts.keys()]) {
      for (const st of sf.statements) {
        if (cl.stmts.get(sf)!.has(st) || ts.isDeclarationStatement(st) || ts.isVariableStatement(st) || ts.isImportDeclaration(st) ||
            ts.isExportDeclaration(st) || ts.isExportAssignment(st) || ts.isTypeAliasDeclaration(st) || ts.isInterfaceDeclaration(st)) continue;
        let touches = false;
        const scan = (n: ts.Node) => {
          if (touches) return;
          if (ts.isIdentifier(n)) { let s = checker.getSymbolAtLocation(n); if (s && (s.flags & ts.SymbolFlags.Alias)) { try { s = checker.getAliasedSymbol(s); } catch { /* keep */ } } if (s && varSyms.has(s)) touches = true; }
          ts.forEachChild(n, scan);
        };
        scan(st);
        if (touches) { add(st); grew = true; }
      }
    }
    if (!grew && !queue.length) break;
  }
  return cl;
}

function importText(imp: ts.ImportDeclaration, names: Set<string>, sf: ts.SourceFile): string | null {
  const ic = imp.importClause;
  if (!ic) return null;
  const parts: string[] = [];
  if (ic.name && names.has(ic.name.text)) parts.push(ic.name.text);
  const nb = ic.namedBindings;
  if (nb && ts.isNamespaceImport(nb) && names.has(nb.name.text)) parts.push(`* as ${nb.name.text}`);
  if (nb && ts.isNamedImports(nb)) {
    const els = nb.elements.filter(e => names.has(e.name.text)).map(e => e.getText(sf));
    if (els.length) parts.push(`{ ${els.join(', ')} }`);
  }
  if (!parts.length) return null;
  return `import ${ic.isTypeOnly ? 'type ' : ''}${parts.join(', ')} from ${imp.moduleSpecifier.getText(sf)};`;
}

function isExported(st: ts.Statement): boolean {
  return !!(ts.canHaveModifiers(st) && ts.getModifiers(st)?.some(m => m.kind === ts.SyntaxKind.ExportKeyword));
}

function isDefaultExport(st: ts.Statement): boolean {
  return !!(ts.canHaveModifiers(st) && ts.getModifiers(st)?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword));
}

function emit(p: Project, cl: Closure, target: ts.Statement, targetName: string, entryRel: string): { files: Map<string, string>; exportName: string } {
  const files = new Map<string, string>();
  const reached = new Set<ts.SourceFile>([...cl.stmts.keys(), ...cl.wholeFiles]);
  // files imported by kept imports must exist (possibly empty)
  for (const [imp] of cl.imports) {
    const sf = imp.getSourceFile();
    const r = ts.resolveModuleName((imp.moduleSpecifier as ts.StringLiteral).text, sf.fileName, p.program.getCompilerOptions(), ts.sys);
    const f = r.resolvedModule?.resolvedFileName;
    if (f) { const t = p.program.getSourceFile(f); if (t) reached.add(t); }
  }
  let exportName = targetName;
  for (const sf of reached) {
    const rel = p.rel(sf.fileName);
    if (cl.wholeFiles.has(sf)) { files.set(rel, sf.getFullText()); continue; }
    const keep = cl.stmts.get(sf) ?? new Set();
    const out: string[] = [];
    const reexported = new Set<string>();
    for (const st of sf.statements) {
      if (ts.isImportDeclaration(st)) {
        const names = cl.imports.get(st);
        if (names) { const t = importText(st, names, sf); if (t) out.push(t); }
        continue;
      }
      if (ts.isExportDeclaration(st) && st.moduleSpecifier && !st.exportClause) { out.push(st.getText(sf)); continue; }
      if (ts.isExportDeclaration(st) && st.exportClause && ts.isNamedExports(st.exportClause)) {
        // `export { a, b as c } (from './m')`: the names whose declarations the slice keeps (an
        // importer of this module reaches them through it, e.g. an index file)
        const els = st.exportClause.elements.filter(el => {
          const s = p.checker.getExportSpecifierLocalTargetSymbol(el);
          let t = s;
          if (s && (s.flags & ts.SymbolFlags.Alias)) { try { t = p.checker.getAliasedSymbol(s); } catch { t = s; } }
          return !!t && (t.declarations ?? []).some(d => {
            const dsf = d.getSourceFile(), top = topLevel(d);
            return cl.wholeFiles.has(dsf) || (!!top && !!cl.stmts.get(dsf)?.has(top));
          });
        });
        if (els.length) {
          for (const el of els) reexported.add(el.name.text);
          const from = st.moduleSpecifier ? ` from ${st.moduleSpecifier.getText(sf)}` : '';
          out.push(`export ${st.isTypeOnly ? 'type ' : ''}{ ${els.map(el => el.getText(sf)).join(', ')} }${from};`);
        }
        continue;
      }
      if (keep.has(st)) {
        out.push(st.getText(sf));
        // classes are exported so that the runner can build instances of parameter types
        if (ts.isClassDeclaration(st) && st.name && !isExported(st)) out.push(`export { ${st.name.text} };`);
      }
    }
    if (sf === target.getSourceFile()) {
      if (isDefaultExport(target)) {
        // re-export under a plain name as well
        if (ts.isFunctionDeclaration(target) || ts.isClassDeclaration(target)) {
          const nm = target.name?.text;
          if (nm) out.push(`export { ${nm} as __difftool_default };`), exportName = '__difftool_default';
        }
      } else if (!isExported(target) && !reexported.has(targetName) && !out.includes(`export { ${targetName} };`)) out.push(`export { ${targetName} };`);
    }
    files.set(rel, out.join('\n') + '\n');
  }
  if (!files.has(entryRel)) files.set(entryRel, '');
  return { files, exportName };
}

function writeSlice(dir: string, files: Map<string, string>): void {
  fs.rmSync(dir, { recursive: true, force: true });
  for (const [rel, text] of files) writeFile(path.join(dir, rel), text);
}

/** Name the entry module exports for the unit: the function, or the class of a method. */
export function exportedTargetName(u: Unit): string {
  return u.cls ?? u.name;
}

export function sliceUnit(p: Project, u: Unit, dir: string): Slice {
  const targetName = exportedTargetName(u);
  const cl = closure(p, u.stmt);
  const { files, exportName } = emit(p, cl, u.stmt, targetName, u.file);
  writeSlice(dir, files);
  const res: Slice = {
    ok: true, dir, entry: u.file, files, exportName, externals: [...cl.externals].sort(), typeExternals: [...cl.typeExternals].sort(),
    hostGlobals: [...cl.hostGlobals].sort(), inlined: [],
  };
  if (res.externals.length) { res.ok = false; res.reason = `uses external module(s) ${res.externals.join(', ')}`; }
  return res;
}

/** Literal initializers that can replace references to a module constant. */
function literalText(e: ts.Expression, sf: ts.SourceFile): string | null {
  if (ts.isNumericLiteral(e) || ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e) || ts.isBigIntLiteral(e)) return e.getText(sf);
  if (e.kind === ts.SyntaxKind.TrueKeyword || e.kind === ts.SyntaxKind.FalseKeyword || e.kind === ts.SyntaxKind.NullKeyword) return e.getText(sf);
  if (ts.isPrefixUnaryExpression(e) && (e.operator === ts.SyntaxKind.MinusToken || e.operator === ts.SyntaxKind.PlusToken) &&
      (ts.isNumericLiteral(e.operand) || ts.isBigIntLiteral(e.operand))) return `(${e.getText(sf)})`;
  if (ts.isParenthesizedExpression(e)) return literalText(e.expression, sf);
  return null;
}

/** Proof variant of a slice: module constants with literal initializers are inlined (so that
 * the theorem does not depend on the module's initialised state), then the slice is recomputed. */
export function inlineConstants(sl: Slice, targetUnitName: string, dir: string): Slice {
  const set: FileSet = { label: 'slice', dir: sl.dir, files: [...sl.files.keys()], roots: [sl.entry], single: false, externals: new Map() };
  const p = makeProject(set);
  const checker = p.checker;
  // candidates
  const cands = new Map<ts.Symbol, { text: string; name: string }>();
  for (const rel of set.files) {
    const sf = p.sf(rel);
    if (!sf) continue;
    for (const st of sf.statements) {
      if (!ts.isVariableStatement(st) || !(st.declarationList.flags & ts.NodeFlags.Const)) continue;
      for (const d of st.declarationList.declarations) {
        if (!ts.isIdentifier(d.name) || !d.initializer) continue;
        const lit = literalText(d.initializer, sf);
        if (lit === null) continue;
        const s = checker.getSymbolAtLocation(d.name);
        if (!s) continue;
        cands.set(s, { text: d.type ? `(${lit} as ${d.type.getText(sf)})` : lit, name: d.name.text });
      }
    }
  }
  if (!cands.size) return { ...sl, inlined: [] };
  // references (expression positions only; constants also used in types are kept)
  const edits = new Map<string, { start: number; end: number; text: string }[]>();
  const blocked = new Set<ts.Symbol>();
  const refs: { rel: string; id: ts.Identifier; sym: ts.Symbol }[] = [];
  for (const rel of set.files) {
    const sf = p.sf(rel);
    if (!sf) continue;
    const walk = (n: ts.Node) => {
      if (ts.isIdentifier(n) && !isDeclName(n) && !isPropertyName(n)) {
        let s = checker.getSymbolAtLocation(n);
        if (s && (s.flags & ts.SymbolFlags.Alias)) { try { s = checker.getAliasedSymbol(s); } catch { /* keep */ } }
        if (s && cands.has(s)) {
          if (inTypePosition(n) || (n.parent && (ts.isExportSpecifier(n.parent) || ts.isImportSpecifier(n.parent)))) {
            if (inTypePosition(n)) blocked.add(s);
          } else refs.push({ rel, id: n, sym: s });
        }
      }
      ts.forEachChild(n, walk);
    };
    walk(sf);
  }
  const inlined = new Set<string>();
  for (const r of refs) {
    if (blocked.has(r.sym)) continue;
    const c = cands.get(r.sym)!;
    const sf = r.id.getSourceFile();
    const shorthand = r.id.parent && ts.isShorthandPropertyAssignment(r.id.parent);
    const l = edits.get(r.rel) ?? [];
    l.push({ start: r.id.getStart(sf), end: r.id.getEnd(), text: shorthand ? `${c.name}: ${c.text}` : c.text });
    edits.set(r.rel, l);
    inlined.add(c.name);
  }
  if (!inlined.size) return { ...sl, inlined: [] };
  const files = new Map<string, string>();
  for (const rel of set.files) {
    let text = sl.files.get(rel)!;
    const es = (edits.get(rel) ?? []).sort((a, b) => b.start - a.start);
    for (const e of es) text = text.slice(0, e.start) + e.text + text.slice(e.end);
    files.set(rel, text);
  }
  const tmp = dir + '.inl';
  writeSlice(tmp, files);
  const p2 = makeProject({ ...set, dir: tmp });
  const sf2 = p2.sf(sl.entry);
  const target = sf2 && findTargetStatement(sf2, targetUnitName);
  if (!target) return { ...sl, ok: false, reason: 'inlining lost the target', inlined: [] };
  const cl = closure(p2, target);
  const { files: f2, exportName } = emit(p2, cl, target, sl.exportName === '__difftool_default' ? targetUnitName : sl.exportName, sl.entry);
  // keep the export name of the original slice
  writeSlice(dir, f2);
  fs.rmSync(tmp, { recursive: true, force: true });
  return { ...sl, dir, files: f2, exportName: sl.exportName === '__difftool_default' ? sl.exportName : exportName, inlined: [...inlined].sort() };
}

/** The top-level statement declaring `name` (f, C.m → class C). */
export function findTargetStatement(sf: ts.SourceFile, name: string): ts.Statement | undefined {
  const base = name.includes('.') ? name.slice(0, name.indexOf('.')) : name;
  for (const st of sf.statements) {
    if ((ts.isFunctionDeclaration(st) || ts.isClassDeclaration(st)) && st.name?.text === base) return st;
    if (ts.isVariableStatement(st) && st.declarationList.declarations.some(d => ts.isIdentifier(d.name) && d.name.text === base)) return st;
  }
  return undefined;
}
