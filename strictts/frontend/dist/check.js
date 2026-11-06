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
exports.isTypeOnlyAmbient = isTypeOnlyAmbient;
exports.checkSubset = checkSubset;
exports.visitSubset = visitSubset;
// Subset checker: syntactic rules of DESIGN.md §2 that do not depend on translation.
// (Type-directed rules — mixed `+`, truthiness, `as` downcasts, conversions — are reported
// by the translator with the same diagnostic format.)
const ts = __importStar(require("typescript"));
const types_1 = require("./types");
const BANNED_GLOBALS = {
    eval: ['no-eval', '`eval` is not allowed'],
    Function: ['no-eval', '`Function` (dynamic code / untyped functions) is not allowed'],
    Proxy: ['no-proxy', '`Proxy` is not allowed'],
    Reflect: ['no-reflect', '`Reflect` is not allowed'],
    Symbol: ['no-symbol', '`Symbol` is not allowed'],
    RegExp: ['no-regexp', '`RegExp` is only supported as `new RegExp(pattern, flags)`'],
};
/** An ambient namespace (`declare namespace NodeJS { interface Timeout … }`, `declare global`)
 * holding only types: it declares nothing that runs. */
function isTypeOnlyAmbient(n) {
    let cur = n;
    let ambient = false;
    for (let p = n; p; p = p.parent) {
        if (ts.isModuleDeclaration(p) && (ts.getCombinedModifierFlags(p) & ts.ModifierFlags.Ambient)) {
            ambient = true;
            break;
        }
    }
    if (!ambient)
        return false;
    const body = cur.body;
    if (!body)
        return true;
    if (ts.isModuleDeclaration(body))
        return isTypeOnlyAmbient(body);
    return ts.isModuleBlock(body) && body.statements.every(s => ts.isInterfaceDeclaration(s) || ts.isTypeAliasDeclaration(s) ||
        (ts.isModuleDeclaration(s) && isTypeOnlyAmbient(s)));
}
function checkSubset(program, files, diags, strict = false) {
    for (const sf of files)
        visitSubset(program, sf, (n, rule, msg) => diags.at(n, rule, msg), strict);
}
/** The syntactic subset rules over a subtree. */
function visitSubset(program, root, report, strict = false) {
    const diags = { at: report };
    const checker = program.getTypeChecker();
    const isLibSym = (s) => !!s && (0, types_1.isLibDecl)(program, s.declarations?.[0]);
    // `null`, the global `undefined`, or `void <number>`
    const isNullishLiteral = (e0) => {
        let e = e0;
        while (ts.isParenthesizedExpression(e))
            e = e.expression;
        if (e.kind === ts.SyntaxKind.NullKeyword)
            return true;
        if (ts.isIdentifier(e) && e.text === 'undefined') {
            const s = checker.getSymbolAtLocation(e);
            return !s || !s.declarations?.length || isLibSym(s);
        }
        return ts.isVoidExpression(e) && ts.isNumericLiteral(e.expression);
    };
    // objects used as dictionaries (one string index signature, no named properties)
    // `unknown`, or `object` (and intersections with it) as TypeScript narrows unknown values
    const isUnknownish = (e) => {
        const t = checker.getTypeAtLocation(e);
        const ok = (x) => !!(x.flags & (ts.TypeFlags.Unknown | ts.TypeFlags.NonPrimitive));
        return ok(t) || (t.isIntersection() && t.types.some(ok));
    };
    const isDict = (e) => {
        const t = checker.getTypeAtLocation(e);
        const infos = checker.getIndexInfosOfType(t);
        // (also with named properties of the index type: TypeMapper.mapObjectType)
        return infos.length === 1 && !!(infos[0].keyType.flags & ts.TypeFlags.String) &&
            checker.getPropertiesOfType(t).every(p => checker.isTypeAssignableTo(checker.getTypeOfSymbol(p), infos[0].type));
    };
    const visit = (n) => {
        switch (n.kind) {
            case ts.SyntaxKind.AnyKeyword:
                // (`any` values are unknown values, except in the original subset: `--strict`)
                if (strict || process.env.STRICTTS_ANY_REJECT)
                    diags.at(n, 'no-any', '`any` is not allowed');
                break;
            case ts.SyntaxKind.UnknownKeyword: {
                const p = n.parent;
                const inCatch = p && ts.isVariableDeclaration(p) && p.parent && ts.isCatchClause(p.parent);
                if (strict && !inCatch)
                    diags.at(n, 'no-any', '`unknown` is only allowed for catch variables');
                break;
            }
            case ts.SyntaxKind.ObjectKeyword:
                // (values of type `object` are unknown values, except in the strict subset)
                if (strict)
                    diags.at(n, 'no-object-type', 'the `object` type is not allowed');
                break;
            case ts.SyntaxKind.SymbolKeyword:
                diags.at(n, 'no-symbol', '`symbol` is not allowed');
                break;
            case ts.SyntaxKind.NeverKeyword: {
                // `never` is fine as a return type (functions that always throw)
                const p = n.parent;
                if (!(p && (ts.isFunctionDeclaration(p) || ts.isMethodDeclaration(p) || ts.isArrowFunction(p) || ts.isFunctionExpression(p)) && p.type === n)) {
                    diags.at(n, 'no-never-value', '`never` values are not allowed');
                }
                break;
            }
            case ts.SyntaxKind.BinaryExpression: {
                const b = n;
                const k = b.operatorToken.kind;
                // `x == null` / `x != undefined` (one operand null or undefined) is the nullish test: allowed
                if ((k === ts.SyntaxKind.EqualsEqualsToken || k === ts.SyntaxKind.ExclamationEqualsToken) && !isNullishLiteral(b.left) && !isNullishLiteral(b.right)) {
                    diags.at(b.operatorToken, 'no-loose-eq', '`==` and `!=` are only allowed against null or undefined; use `===` / `!==`');
                }
                if (k === ts.SyntaxKind.InKeyword && !isDict(b.right) && (strict || !isUnknownish(b.right)))
                    diags.at(b.operatorToken, 'no-in', 'the `in` operator is only allowed on dictionaries and unknown values');
                break;
            }
            case ts.SyntaxKind.DeleteExpression: {
                let x = n.expression;
                while (ts.isParenthesizedExpression(x))
                    x = x.expression;
                if (!((ts.isElementAccessExpression(x) || ts.isPropertyAccessExpression(x)) && isDict(x.expression)))
                    diags.at(n, 'no-delete', '`delete` is only allowed on dictionary entries');
                break;
            }
            case ts.SyntaxKind.ForInStatement:
                diags.at(n, 'no-for-in', '`for … in` is not allowed');
                break;
            case ts.SyntaxKind.WithStatement:
                diags.at(n, 'no-with', '`with` is not allowed');
                break;
            case ts.SyntaxKind.YieldExpression:
                diags.at(n, 'no-generators', 'generators are not allowed');
                break;
            case ts.SyntaxKind.Decorator:
                diags.at(n, 'no-decorators', 'decorators are not allowed');
                break;
            case ts.SyntaxKind.EnumDeclaration:
                diags.at(n, 'no-enum-decl', 'TypeScript `enum` declarations are not supported; use a string-literal union');
                break;
            case ts.SyntaxKind.ModuleDeclaration:
                if (!isTypeOnlyAmbient(n))
                    diags.at(n, 'unsupported-syntax', 'namespaces are not supported');
                break;
            case ts.SyntaxKind.VariableDeclarationList: {
                const l = n;
                if ((l.flags & ts.NodeFlags.BlockScoped) === 0)
                    diags.at(n, 'no-var', '`var` declarations are not allowed; use `let` or `const`');
                break;
            }
            case ts.SyntaxKind.FunctionDeclaration:
            case ts.SyntaxKind.FunctionExpression:
            case ts.SyntaxKind.MethodDeclaration:
                if (n.asteriskToken)
                    diags.at(n, 'no-generators', 'generators are not allowed');
                break;
            case ts.SyntaxKind.ClassDeclaration:
            case ts.SyntaxKind.ClassExpression: {
                const c = n;
                if (c.heritageClauses?.some(h => h.token === ts.SyntaxKind.ExtendsKeyword))
                    diags.at(n, 'no-extends', 'classes cannot extend other classes');
                break;
            }
            case ts.SyntaxKind.LabeledStatement: {
                const s = n.statement;
                if (!ts.isIterationStatement(s, true))
                    diags.at(n, 'no-label-non-loop', 'labels are only allowed on loops');
                break;
            }
            case ts.SyntaxKind.PropertyAccessExpression: {
                const pa = n;
                const name = pa.name.text;
                if (name === 'prototype' || name === '__proto__')
                    diags.at(pa.name, 'no-prototype', `\`${name}\` access is not allowed`);
                if (ts.isIdentifier(pa.expression) && pa.expression.text === 'Object' && isLibSym(checker.getSymbolAtLocation(pa.expression)) &&
                    ['setPrototypeOf', 'getPrototypeOf', 'defineProperty', 'defineProperties', 'create'].includes(name)) {
                    diags.at(pa, 'no-prototype', `Object.${name} is not allowed`);
                }
                break;
            }
            case ts.SyntaxKind.Identifier: {
                const id = n;
                const p = id.parent;
                const isRef = !(p && ((ts.isPropertyAccessExpression(p) && p.name === id) || (ts.isPropertyAssignment(p) && p.name === id) ||
                    ((ts.isMethodDeclaration(p) || ts.isPropertyDeclaration(p) || ts.isPropertySignature(p) || ts.isMethodSignature(p)) && p.name === id)));
                if (!isRef)
                    break;
                if (id.text === 'arguments') {
                    const s = checker.getSymbolAtLocation(id);
                    if (!s || isLibSym(s) || s.declarations === undefined)
                        diags.at(id, 'no-arguments', '`arguments` is not allowed; use rest parameters');
                }
                else if (Object.hasOwn(BANNED_GLOBALS, id.text)) {
                    const s = checker.getSymbolAtLocation(id);
                    const ctor = id.text === 'RegExp' && p && (ts.isNewExpression(p) || ts.isCallExpression(p)) && p.expression === id;
                    if (isLibSym(s) && !ctor && !(p && (ts.isTypeReferenceNode(p) || ts.isExpressionWithTypeArguments(p)))) {
                        const [rule, msg] = BANNED_GLOBALS[id.text];
                        diags.at(id, rule, msg);
                    }
                }
                break;
            }
            case ts.SyntaxKind.JsxElement:
            case ts.SyntaxKind.JsxSelfClosingElement:
            case ts.SyntaxKind.JsxFragment: {
                const p = n.parent;
                const nested = p && (ts.isJsxElement(p) || ts.isJsxFragment(p) || ts.isJsxExpression(p) || ts.isJsxAttribute(p));
                if (!nested)
                    diags.at(n, 'jsx', 'JSX is not supported');
                break;
            }
            case ts.SyntaxKind.ThrowStatement: {
                const e = n.expression;
                const t = checker.getTypeAtLocation(e);
                const sym = t.getSymbol();
                const isErr = !!sym && isLibSym(sym) && /Error$/.test(sym.name);
                const catchVar = ts.isIdentifier(e) && (() => {
                    const s = checker.getSymbolAtLocation(e);
                    const d = s?.declarations?.[0];
                    return !!d && ts.isVariableDeclaration(d) && !!d.parent && ts.isCatchClause(d.parent);
                })();
                // (an unknown value is checked when it is thrown: it must be an Error)
                const unknownish = !!(t.flags & (ts.TypeFlags.Unknown | ts.TypeFlags.Any));
                if (!isErr && !catchVar && (strict || !unknownish))
                    diags.at(n, 'throw-non-error', 'only Error values (new Error(…), TypeError, …) can be thrown');
                break;
            }
        }
        ts.forEachChild(n, visit);
    };
    visit(root);
}
