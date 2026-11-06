# Third-party files in the source bundles

Our own code in sources/ is licensed under Apache-2.0 (LICENSE). The paper, the technical report and the evidence texts
are licensed under CC BY 4.0 (LICENSE-CC-BY-4.0.txt). The files below come from other projects and keep their own licences.
They received only the normalization of home paths and account names (NORMALIZATION.md, rules 1 and 2); their notices are unchanged.

| Path (inside each version directory) | Project | Licence | Licence text | Versions that contain it |
|---|---|---|---|---|
| `equiv-lean-<version>/examples/cir/jsmn/` | jsmn | MIT | examples/cir/jsmn/LICENSE (included) | 19 of the equiv-lean versions |
| `equiv-lean-<version>/examples/cir/musl/` | musl libc (excerpts) | MIT | examples/cir/musl/COPYRIGHT (included) | 19 of the equiv-lean versions |
| `equiv-lean-<version>/examples/cir/tinyregex/` | tiny-regex-c | The Unlicense (public domain) | examples/cir/tinyregex/LICENSE (included) | 24 of the equiv-lean versions |
| `equiv-lean-<version>/examples/cir/zlib_adler32/` | zlib 1.3.1 (Adler-32 and headers) | zlib License | examples/cir/zlib_adler32/LICENSE (included) | 8 of the equiv-lean versions |
| `equiv-lean-<version>/examples/rust/crc32fast_base/` | crc32fast (Rust crate) | MIT or Apache-2.0 | examples/rust/crc32fast_base/LICENSE-MIT (included) | 27 of the equiv-lean versions |
| `equiv-lean-<version>/examples/ts/es-toolkit/` | es-toolkit (function versions) | MIT | third_party_licenses/es-toolkit-LICENSE | 10 of the equiv-lean versions |
| `equiv-lean-<version>/examples/ts/pako_crc32.ts` | pako (crc32 port) | zlib License | notice in the file header | 27 of the equiv-lean versions |
| `equiv-lean-<version>/examples/ts/remeda/` | remeda (function versions) | MIT | third_party_licenses/remeda-LICENSE | 2 of the equiv-lean versions |

Files derived from third-party code:

- The CardDemo intermediate representations (`equiv-lean-*/examples/cobol/carddemo/*.ir.json`, `coblean-*/examples/carddemo/*.ir.json`)
  and the Java and Rust translations of CardDemo programs (`equiv-lean-*/examples/java/mod_*`, `equiv-lean-*/examples/rust/mod_*`)
  derive from AWS CardDemo at commit 59cc6c2f, Apache-2.0 (third_party_licenses/aws-carddemo-LICENSE).
- The Lean program terms generated from the sources above (`equiv-lean-*/EquivLean/Demo/`, under `Gen/`, `XLang/`, `Thrift/`, `TS/` and `Cir/`)
  derive from those projects; the Thrift terms derive from Apache Thrift, Apache-2.0.
