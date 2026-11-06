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
exports.Reject = exports.Diags = void 0;
exports.reject = reject;
// Diagnostics in the format `file:line:col [rule-id] message`.
const ts = __importStar(require("typescript"));
const path = __importStar(require("path"));
class Diags {
    cwd;
    list = [];
    seen = new Set();
    constructor(cwd) {
        this.cwd = cwd;
    }
    at(node, rule, msg) {
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
    push(d) {
        const key = `${d.file}:${d.line}:${d.col}:${d.rule}:${d.msg}`;
        if (this.seen.has(key))
            return;
        this.seen.add(key);
        this.list.push(d);
    }
    fromTs(d) {
        const msg = ts.flattenDiagnosticMessageText(d.messageText, ' ');
        if (d.file && d.start !== undefined) {
            const pos = d.file.getLineAndCharacterOfPosition(d.start);
            this.push({ file: path.relative(this.cwd, d.file.fileName) || d.file.fileName, line: pos.line + 1, col: pos.character + 1, rule: `ts${d.code}`, msg });
        }
        else
            this.push({ file: '<options>', line: 0, col: 0, rule: `ts${d.code}`, msg });
    }
    get count() { return this.list.length; }
    format() {
        const sorted = [...this.list].sort((a, b) => a.file < b.file ? -1 : a.file > b.file ? 1 : a.line - b.line || a.col - b.col);
        return sorted.map(d => `${d.file}:${d.line}:${d.col} [${d.rule}] ${d.msg}`).join('\n');
    }
}
exports.Diags = Diags;
/** A diagnostic raised while translating: aborts the current function. */
class Reject extends Error {
    node;
    rule;
    /** for `external-type`: the external type's name (coverage reports) */
    extName;
    constructor(node, rule, msg) {
        super(msg);
        this.node = node;
        this.rule = rule;
    }
}
exports.Reject = Reject;
function reject(node, rule, msg, extName) {
    const r = new Reject(node, rule, msg);
    r.extName = extName;
    if (process.env.STRICTTS_DEBUG)
        process.stderr.write(`[debug] ${rule}: ${msg}\n${r.stack}\n`);
    throw r;
}
