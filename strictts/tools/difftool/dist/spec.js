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
exports.parseSpec = parseSpec;
exports.materialize = materialize;
// Input specifications: a file, a directory, or `git:REV:path` in a repository. A spec is
// materialized into a scratch directory (the named files plus every file they import through
// relative module specifiers), so that later stages work on ordinary files.
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
const util_1 = require("./util");
const SRC_RE = /\.(ts|tsx|mts|cts)$/;
const SKIP_DIR = new Set(['node_modules', 'dist', 'build', 'lib', '.git', 'coverage', 'out']);
function fsSource() {
    return {
        read: k => { try {
            return fs.readFileSync(k, 'utf8');
        }
        catch {
            return null;
        } },
        isFile: k => { try {
            return fs.statSync(k).isFile();
        }
        catch {
            return false;
        } },
        isDir: k => { try {
            return fs.statSync(k).isDirectory();
        }
        catch {
            return false;
        } },
        listDir: k => {
            const out = [];
            const walk = (d) => {
                for (const e of fs.readdirSync(d, { withFileTypes: true })) {
                    if (e.isDirectory()) {
                        if (!SKIP_DIR.has(e.name) && !e.name.startsWith('.'))
                            walk(path.join(d, e.name));
                    }
                    else if (SRC_RE.test(e.name))
                        out.push(path.join(d, e.name));
                }
            };
            walk(k);
            return out.sort();
        },
        join: (d, r) => path.resolve(d, r),
        dirname: k => path.dirname(k),
    };
}
function gitSource(repo, rev) {
    const ls = (0, util_1.run)('git', ['-C', repo, 'ls-tree', '-r', '--name-only', rev], { timeoutS: 60 });
    if (ls.status !== 0)
        throw new Error(`git ls-tree ${rev} failed in ${repo}: ${ls.stderr.trim()}`);
    const all = ls.stdout.split('\n').filter(Boolean);
    const files = new Set(all);
    const dirs = new Set(['']);
    for (const f of all) {
        let d = path.posix.dirname(f);
        while (d !== '.' && !dirs.has(d)) {
            dirs.add(d);
            d = path.posix.dirname(d);
        }
    }
    const cache = new Map();
    return {
        read: k => {
            if (!files.has(k))
                return null;
            if (!cache.has(k)) {
                const r = (0, util_1.run)('git', ['-C', repo, 'show', `${rev}:${k}`], { timeoutS: 60 });
                cache.set(k, r.status === 0 ? r.stdout : null);
            }
            return cache.get(k);
        },
        isFile: k => files.has(k),
        isDir: k => dirs.has(k.replace(/\/$/, '')),
        listDir: k => {
            const pre = k === '' || k === '.' ? '' : k.replace(/\/$/, '') + '/';
            return all.filter(f => f.startsWith(pre) && SRC_RE.test(f) &&
                !f.slice(pre.length).split('/').slice(0, -1).some(seg => SKIP_DIR.has(seg) || seg.startsWith('.'))).sort();
        },
        join: (d, r) => path.posix.normalize(path.posix.join(d, r)).replace(/^\.\//, ''),
        dirname: k => { const d = path.posix.dirname(k); return d === '.' ? '' : d; },
    };
}
/** Resolve a relative module specifier the way TypeScript's bundler resolution does. */
function resolveRel(src, fromKey, spec) {
    const base = src.join(src.dirname(fromKey), spec);
    const cands = [];
    if (SRC_RE.test(base))
        cands.push(base);
    const m = base.match(/^(.*)\.(js|jsx|mjs|cjs)$/);
    if (m)
        cands.push(m[1] + { js: '.ts', jsx: '.tsx', mjs: '.mts', cjs: '.cts' }[m[2]], m[1] + '.d.ts');
    cands.push(base + '.ts', base + '.tsx', base + '.d.ts', base + '/index.ts', base + '/index.tsx');
    for (const c of cands)
        if (src.isFile(c))
            return c;
    return null;
}
function parseSpec(spec, opts) {
    const g = spec.match(/^git:([^:]+):(.*)$/);
    if (g) {
        const [, rev, p] = g;
        return { src: gitSource(opts.repo, rev), key: p.replace(/^\.?\//, '').replace(/\/$/, ''), base: '' };
    }
    return { src: fsSource(), key: path.resolve(spec), base: null };
}
/** Materialize `spec` under `dest`. */
function materialize(spec, dest, opts) {
    const { src, key, base } = parseSpec(spec, opts);
    let roots;
    let single;
    if (src.isFile(key)) {
        roots = [key];
        single = true;
    }
    else if (src.isDir(key)) {
        roots = src.listDir(key);
        single = false;
    }
    else
        throw new Error(`${spec}: no such file or directory`);
    // follow relative imports
    const seen = new Map();
    const externals = new Map();
    const queue = [...roots];
    while (queue.length) {
        const k = queue.shift();
        if (seen.has(k))
            continue;
        const text = src.read(k);
        if (text === null)
            continue;
        seen.set(k, text);
        const info = ts.preProcessFile(text, true, true);
        for (const imp of info.importedFiles) {
            const s = imp.fileName;
            if (s.startsWith('./') || s.startsWith('../')) {
                const r = resolveRel(src, k, s);
                if (r && !seen.has(r))
                    queue.push(r);
            }
            else {
                const l = externals.get(s) ?? [];
                l.push(k);
                externals.set(s, l);
            }
        }
    }
    // common root of everything materialized
    const keys = [...seen.keys()];
    let rootDir;
    if (base !== null)
        rootDir = '';
    else {
        const under = (k, d) => d === '/' || k.startsWith(d + '/');
        rootDir = path.dirname(keys[0]);
        for (const k of keys)
            while (!under(k, rootDir))
                rootDir = path.dirname(rootDir);
    }
    const rel = (k) => base !== null ? k : path.relative(rootDir, k).split(path.sep).join('/');
    fs.rmSync(dest, { recursive: true, force: true });
    for (const [k, text] of seen)
        (0, util_1.writeFile)(path.join(dest, rel(k)), text);
    const ext = new Map();
    for (const [s, ks] of externals)
        ext.set(s, ks.map(rel));
    return { label: spec, dir: dest, files: keys.map(rel).sort(), roots: roots.filter(r => seen.has(r)).map(rel), single, externals: ext };
}
