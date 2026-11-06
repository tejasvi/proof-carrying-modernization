// Input specifications: a file, a directory, or `git:REV:path` in a repository. A spec is
// materialized into a scratch directory (the named files plus every file they import through
// relative module specifiers), so that later stages work on ordinary files.
import * as fs from 'fs';
import * as path from 'path';
import * as ts from 'typescript';
import { run, writeFile } from './util';

export interface FileSet {
  label: string;
  /** materialized root (absolute) */
  dir: string;
  /** relative (posix) paths of all materialized source files */
  files: string[];
  /** the files the spec names (single file: that file; directory: every source file in it) */
  roots: string[];
  single: boolean;
  /** non-relative module specifiers imported by some file (packages, path aliases) */
  externals: Map<string, string[]>;
}

const SRC_RE = /\.(ts|tsx|mts|cts)$/;
const SKIP_DIR = new Set(['node_modules', 'dist', 'build', 'lib', '.git', 'coverage', 'out']);

interface Source {
  read(key: string): string | null;
  isFile(key: string): boolean;
  isDir(key: string): boolean;
  listDir(key: string): string[];
  join(dir: string, rel: string): string;
  dirname(key: string): string;
}

function fsSource(): Source {
  return {
    read: k => { try { return fs.readFileSync(k, 'utf8'); } catch { return null; } },
    isFile: k => { try { return fs.statSync(k).isFile(); } catch { return false; } },
    isDir: k => { try { return fs.statSync(k).isDirectory(); } catch { return false; } },
    listDir: k => {
      const out: string[] = [];
      const walk = (d: string) => {
        for (const e of fs.readdirSync(d, { withFileTypes: true })) {
          if (e.isDirectory()) { if (!SKIP_DIR.has(e.name) && !e.name.startsWith('.')) walk(path.join(d, e.name)); }
          else if (SRC_RE.test(e.name)) out.push(path.join(d, e.name));
        }
      };
      walk(k);
      return out.sort();
    },
    join: (d, r) => path.resolve(d, r),
    dirname: k => path.dirname(k),
  };
}

function gitSource(repo: string, rev: string): Source {
  const ls = run('git', ['-C', repo, 'ls-tree', '-r', '--name-only', rev], { timeoutS: 60 });
  if (ls.status !== 0) throw new Error(`git ls-tree ${rev} failed in ${repo}: ${ls.stderr.trim()}`);
  const all = ls.stdout.split('\n').filter(Boolean);
  const files = new Set(all);
  const dirs = new Set<string>(['']);
  for (const f of all) { let d = path.posix.dirname(f); while (d !== '.' && !dirs.has(d)) { dirs.add(d); d = path.posix.dirname(d); } }
  const cache = new Map<string, string | null>();
  return {
    read: k => {
      if (!files.has(k)) return null;
      if (!cache.has(k)) {
        const r = run('git', ['-C', repo, 'show', `${rev}:${k}`], { timeoutS: 60 });
        cache.set(k, r.status === 0 ? r.stdout : null);
      }
      return cache.get(k)!;
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
function resolveRel(src: Source, fromKey: string, spec: string): string | null {
  const base = src.join(src.dirname(fromKey), spec);
  const cands: string[] = [];
  if (SRC_RE.test(base)) cands.push(base);
  const m = base.match(/^(.*)\.(js|jsx|mjs|cjs)$/);
  if (m) cands.push(m[1] + ({ js: '.ts', jsx: '.tsx', mjs: '.mts', cjs: '.cts' } as Record<string, string>)[m[2]], m[1] + '.d.ts');
  cands.push(base + '.ts', base + '.tsx', base + '.d.ts', base + '/index.ts', base + '/index.tsx');
  for (const c of cands) if (src.isFile(c)) return c;
  return null;
}

export interface SpecOpts { repo: string }

export function parseSpec(spec: string, opts: SpecOpts): { src: Source; key: string; base: string | null } {
  const g = spec.match(/^git:([^:]+):(.*)$/);
  if (g) {
    const [, rev, p] = g;
    return { src: gitSource(opts.repo, rev), key: p.replace(/^\.?\//, '').replace(/\/$/, ''), base: '' };
  }
  return { src: fsSource(), key: path.resolve(spec), base: null };
}

/** Materialize `spec` under `dest`. */
export function materialize(spec: string, dest: string, opts: SpecOpts): FileSet {
  const { src, key, base } = parseSpec(spec, opts);
  let roots: string[];
  let single: boolean;
  if (src.isFile(key)) { roots = [key]; single = true; }
  else if (src.isDir(key)) { roots = src.listDir(key); single = false; }
  else throw new Error(`${spec}: no such file or directory`);
  // follow relative imports
  const seen = new Map<string, string>();
  const externals = new Map<string, string[]>();
  const queue = [...roots];
  while (queue.length) {
    const k = queue.shift()!;
    if (seen.has(k)) continue;
    const text = src.read(k);
    if (text === null) continue;
    seen.set(k, text);
    const info = ts.preProcessFile(text, true, true);
    for (const imp of info.importedFiles) {
      const s = imp.fileName;
      if (s.startsWith('./') || s.startsWith('../')) {
        const r = resolveRel(src, k, s);
        if (r && !seen.has(r)) queue.push(r);
      } else {
        const l = externals.get(s) ?? [];
        l.push(k);
        externals.set(s, l);
      }
    }
  }
  // common root of everything materialized
  const keys = [...seen.keys()];
  let rootDir: string;
  if (base !== null) rootDir = '';
  else {
    const under = (k: string, d: string) => d === '/' || k.startsWith(d + '/');
    rootDir = path.dirname(keys[0]);
    for (const k of keys) while (!under(k, rootDir)) rootDir = path.dirname(rootDir);
  }
  const rel = (k: string) => base !== null ? k : path.relative(rootDir, k).split(path.sep).join('/');
  fs.rmSync(dest, { recursive: true, force: true });
  for (const [k, text] of seen) writeFile(path.join(dest, rel(k)), text);
  const ext = new Map<string, string[]>();
  for (const [s, ks] of externals) ext.set(s, ks.map(rel));
  return { label: spec, dir: dest, files: keys.map(rel).sort(), roots: roots.filter(r => seen.has(r)).map(rel), single, externals: ext };
}
