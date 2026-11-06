"""Target configuration files (TOML) -> `Target`."""
from __future__ import annotations

import tomllib
from pathlib import Path

from .model import Target, Variant


def load_target(path: str | Path) -> Target:
    d = tomllib.loads(Path(path).read_text())
    variants = [Variant(v["name"], list(v.get("flags", [])), list(v.get("sources", [])))
                for v in d.pop("variants", [])] or [Variant("default")]
    extra = d.pop("extra", {})
    known = {"name", "lang", "root", "sources", "include", "tests", "entry", "version"}
    extra.update({k: v for k, v in d.items() if k not in known})
    extra.setdefault("_target_dir", str(Path(path).resolve().parent))   # relative paths in options resolve here
    explicit = bool(variants) and not (len(variants) == 1 and variants[0].name == "default" and not variants[0].flags)
    t = Target(name=d["name"], lang=d["lang"], root=d["root"], sources=list(d.get("sources", [])),
               include=list(d.get("include", [])), variants=variants, tests=list(d.get("tests", [])),
               entry=list(d.get("entry", [])), version=d.get("version", "v0"), extra=extra)
    if t.lang == "cir" and extra.get("compile_commands"):
        extra.setdefault("compile_commands_abs", str((Path(t.root) / extra["compile_commands"]).resolve()))
        extra.setdefault("orig_root", str(Path(t.root).resolve()))
    if t.lang == "cir" and extra.get("compile_commands") and not explicit:
        # one build per translation unit of the compilation database, with its recorded flags
        from .adapters.cir.compdb import variants_from_compdb
        t.variants = variants_from_compdb(t)
    return t
