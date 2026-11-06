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
exports.COMPILER_OPTIONS = void 0;
exports.cachingHost = cachingHost;
exports.makeProject = makeProject;
// TypeScript programs over materialized file sets (for function discovery, slicing and type
// descriptors). Library files are parsed once per process.
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
exports.COMPILER_OPTIONS = {
    target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler,
    lib: ['lib.es2023.d.ts'], types: [], allowImportingTsExtensions: true, noEmit: true, skipLibCheck: true,
    strict: true, jsx: ts.JsxEmit.Preserve, allowJs: false, resolveJsonModule: false,
};
const libCache = new Map();
function cachingHost(options) {
    const host = ts.createCompilerHost(options, true);
    const orig = host.getSourceFile.bind(host);
    host.getSourceFile = (fileName, lang, onError, shouldCreate) => {
        const isLib = fileName.includes('/node_modules/typescript/lib/');
        if (isLib) {
            const key = fileName + '|' + JSON.stringify(lang);
            let sf = libCache.get(key);
            if (!sf) {
                sf = orig(fileName, lang, onError, shouldCreate);
                if (sf)
                    libCache.set(key, sf);
            }
            return sf;
        }
        return orig(fileName, lang, onError, shouldCreate);
    };
    return host;
}
function makeProject(set, files) {
    const roots = (files ?? set.files).map(f => path.join(set.dir, f));
    const program = ts.createProgram(roots, exports.COMPILER_OPTIONS, cachingHost(exports.COMPILER_OPTIONS));
    const checker = program.getTypeChecker();
    const dir = path.resolve(set.dir);
    return {
        set, program, checker,
        abs: rel => path.join(dir, rel),
        rel: abs => path.relative(dir, abs).split(path.sep).join('/'),
        sf: rel => program.getSourceFile(path.join(dir, rel)),
        isUser: sf => !sf.isDeclarationFile && path.resolve(sf.fileName).startsWith(dir + path.sep) && !sf.fileName.includes('/node_modules/'),
    };
}
