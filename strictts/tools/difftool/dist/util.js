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
exports.Rng = exports.SCRATCH = exports.ROOT = void 0;
exports.sha1 = sha1;
exports.mkdirp = mkdirp;
exports.writeFile = writeFile;
exports.readFile = readFile;
exports.run = run;
exports.timestamp = timestamp;
exports.leanEnv = leanEnv;
exports.truncate = truncate;
// Small shared helpers: paths, hashing, process execution, deterministic PRNG.
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const crypto = __importStar(require("crypto"));
const child_process_1 = require("child_process");
const boot_1 = require("./boot");
Object.defineProperty(exports, "ROOT", { enumerable: true, get: function () { return boot_1.ROOT; } });
exports.SCRATCH = path.join(boot_1.ROOT, 'scratch', 'difftool');
function sha1(s) {
    return crypto.createHash('sha1').update(s).digest('hex');
}
function mkdirp(d) {
    fs.mkdirSync(d, { recursive: true });
    return d;
}
function writeFile(f, text) {
    mkdirp(path.dirname(f));
    fs.writeFileSync(f, text);
}
function readFile(f) {
    return fs.readFileSync(f, 'utf8');
}
/** Run a command synchronously (no shell), with a timeout; the child is killed with SIGKILL. */
function run(cmd, args, opts = {}) {
    const t0 = Date.now();
    const r = (0, child_process_1.spawnSync)(cmd, args, {
        cwd: opts.cwd ?? boot_1.ROOT, env: opts.env ?? process.env, encoding: 'utf8', input: opts.input,
        timeout: (opts.timeoutS ?? 600) * 1000, killSignal: 'SIGKILL', maxBuffer: 256 << 20,
    });
    const timedOut = !!r.error && /ETIMEDOUT/.test(String(r.error.code ?? r.error.message));
    return { status: r.status, stdout: r.stdout ?? '', stderr: (r.stderr ?? '') + (r.error && !timedOut ? `\n${r.error.message}` : ''), timedOut, secs: (Date.now() - t0) / 1000 };
}
/** splitmix64-style PRNG on two 32-bit halves (deterministic across runs). */
class Rng {
    s;
    constructor(seed) { this.s = BigInt.asUintN(64, BigInt(seed)); }
    nextU64() {
        this.s = BigInt.asUintN(64, this.s + 0x9e3779b97f4a7c15n);
        let z = this.s;
        z = BigInt.asUintN(64, (z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n);
        z = BigInt.asUintN(64, (z ^ (z >> 27n)) * 0x94d049bb133111ebn);
        return z ^ (z >> 31n);
    }
    /** uniform in [0, 1) */
    float() { return Number(this.nextU64() >> 11n) / 2 ** 53; }
    /** uniform integer in [0, n) */
    below(n) { return n <= 0 ? 0 : Math.floor(this.float() * n); }
    int(lo, hi) { return lo + this.below(hi - lo + 1); }
    chance(p) { return this.float() < p; }
    pick(xs) { return xs[this.below(xs.length)]; }
}
exports.Rng = Rng;
function timestamp() {
    return new Date().toISOString().replace(/[-:]/g, '').replace(/\.\d+Z$/, 'Z');
}
/** Lean's library path (computed once through `lake env`). */
let leanPath = null;
function leanEnv() {
    if (leanPath === null) {
        const home = process.env.HOME ?? '';
        const env = { ...process.env, PATH: `${home}/.elan/bin:${process.env.PATH}` };
        const r = (0, child_process_1.spawnSync)('lake', ['env', 'printenv', 'LEAN_PATH'], { cwd: boot_1.ROOT, env, encoding: 'utf8' });
        leanPath = (r.stdout || '').trim();
        if (!leanPath)
            throw new Error(`cannot determine LEAN_PATH (lake env): ${r.stderr}`);
    }
    const home = process.env.HOME ?? '';
    return { ...process.env, PATH: `${home}/.elan/bin:${process.env.PATH}`, LEAN_PATH: leanPath };
}
function truncate(s, n) {
    return s.length <= n ? s : s.slice(0, n) + `… (${s.length - n} more chars)`;
}
