"""C → Rust migration with a differential oracle on cirlean's C semantics (tiny-regex-c, f2632c6).

* cases.py: the test inputs: the project's own vectors (tests/test1.c, the Makefile's random-test patterns,
  tests/test_compile.c), hand-written edge cases and generated (pattern, text) pairs;
* cref.py: the reference: cirrun runs re_match once per case from the module's initial memory (fresh statics),
  and a harness function dumps re_compile's two static arrays; a native build (gcc, ASan + UBSan, one fork per
  case) is a cross-check of cirrun;
* rustrun.py: a candidate crate natively (debug build: overflow checks on) and as its Charon + Aeneas extraction
  evaluated in Lean;
* loop.py: translation by a model and counterexample-only repair rounds, arms `guided` (equiv-lean's style
  guide) and `plain`; every version under runs/c2rust/tiny-regex-c/<arm>/v<k>/.
"""
