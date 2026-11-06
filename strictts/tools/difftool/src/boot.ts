// Module resolution: `require('typescript')` resolves to the translator's copy
// (frontend/node_modules), so that the difftool and the translator share one compiler.
// Must be the first import of every entry point.
import * as path from 'path';

export const ROOT = path.resolve(__dirname, '..', '..', '..');
const Module = require('module');
const extra = path.join(ROOT, 'frontend', 'node_modules');
if (!(process.env.NODE_PATH ?? '').split(path.delimiter).includes(extra)) {
  process.env.NODE_PATH = [extra, process.env.NODE_PATH].filter(Boolean).join(path.delimiter);
  Module._initPaths();
}
