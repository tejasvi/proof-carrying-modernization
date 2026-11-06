"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.normText = normText;
exports.unitsOf = unitsOf;
exports.moduleContextText = moduleContextText;
// Function units of a source file: top-level functions, `const f = (…) => …`, class methods
// and constructors, with a normalized text (comments and formatting removed) used to decide
// whether a unit changed.
const ts = __importStar(require("typescript"));
const printer = ts.createPrinter({ removeComments: true, newLine: ts.NewLineKind.LineFeed });
function normText(node, sf) {
    return printer.printNode(ts.EmitHint.Unspecified, node, sf);
}
function hasMod(n, k) {
    return !!(ts.canHaveModifiers(n) && ts.getModifiers(n)?.some(m => m.kind === k));
}
function unitsOf(p, file, moduleKey) {
    const sf = p.sf(file);
    if (!sf)
        return [];
    const out = [];
    const add = (name, kind, fn, stmt, textNode, cls) => {
        const isAsync = hasMod(fn, ts.SyntaxKind.AsyncKeyword);
        const isGeneric = !!(fn.typeParameters && fn.typeParameters.length) ||
            !!(cls && ts.isClassDeclaration(stmt) && stmt.typeParameters && stmt.typeParameters.length);
        out.push({
            key: `${moduleKey}::${name}`, file, name, kind, cls, fn, stmt, text: normText(textNode, sf), isAsync, isGeneric,
            exported: hasMod(stmt, ts.SyntaxKind.ExportKeyword), line: sf.getLineAndCharacterOfPosition(fn.getStart(sf)).line + 1,
            isPrivate: !!cls && (hasMod(fn, ts.SyntaxKind.PrivateKeyword) || hasMod(fn, ts.SyntaxKind.ProtectedKeyword) || (!!fn.name && ts.isPrivateIdentifier(fn.name))),
            // (an optional parameter: without the undefined its default value excludes; the wrapper marks it optional)
            paramTypes: fn.parameters.map(q => {
                if (q.type)
                    return undefined;
                const t = p.checker.getTypeAtLocation(q);
                return p.checker.typeToString(q.questionToken || q.initializer ? p.checker.getNonNullableType(t) : t, q, ts.TypeFormatFlags.NoTruncation);
            }),
        });
    };
    for (const st of sf.statements) {
        if (ts.isFunctionDeclaration(st) && st.name && st.body)
            add(st.name.text, 'function', st, st, st);
        else if (ts.isVariableStatement(st)) {
            for (const d of st.declarationList.declarations) {
                if (!ts.isIdentifier(d.name) || !d.initializer)
                    continue;
                let init = d.initializer;
                while (ts.isParenthesizedExpression(init) || ts.isAsExpression(init) || ts.isSatisfiesExpression(init))
                    init = init.expression;
                if (ts.isArrowFunction(init) || ts.isFunctionExpression(init))
                    add(d.name.text, 'arrow', init, st, d);
            }
        }
        else if (ts.isClassDeclaration(st) && st.name) {
            const c = st.name.text;
            for (const m of st.members) {
                if (ts.isConstructorDeclaration(m) && m.body)
                    add(`${c}.constructor`, 'ctor', m, st, m, c);
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
function moduleContextText(p, file) {
    const sf = p.sf(file);
    if (!sf)
        return '';
    const parts = [];
    for (const st of sf.statements) {
        if (ts.isFunctionDeclaration(st))
            continue;
        if (ts.isClassDeclaration(st)) {
            parts.push(normText(ts.factory.updateClassDeclaration(st, st.modifiers, st.name, st.typeParameters, st.heritageClauses, st.members.filter(m => !(ts.isMethodDeclaration(m) || ts.isConstructorDeclaration(m)))), sf));
            continue;
        }
        parts.push(normText(st, sf));
    }
    return parts.join('\n');
}
