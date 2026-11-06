# D2 fixes (prereg D2 v1): java.lang.CharSequence and java.lang.Character

These are the two commons-lang3 fix targets of `PREREG_D2_v1.md`. There is one change per family, and
no unit of any sample or population is named. The labels are checked against the D pin, snapshot
20261024T1029Z (`Jimple/Native.lean` there):

- **listed**: already modelled at 1029Z, newly listed under an exact header in `docs/LIBRARY_MODELS.md`;
- **fixed**: already modelled at 1029Z, newly listed, and its behaviour corrected;
- **new**: newly modelled.

The model table at 1029Z had no section headed `java.lang.CharSequence`. Character's rows sat under
`## Boxed primitives (Integer, Long, …)` and `## java.lang.Character: code points and classification`,
headers that name no class exactly. veriforch's reader (`modelled_library`) therefore matched no
Character or CharSequence row. The other boxed classes keep their 1029Z header in this snapshot
(evidence owner's decision, option (a)).

Every new or fixed behaviour is checked against the JDK 17 JVM by `difftest/src/CharFamily.java` and
`difftest/src/CharSeqIface.java`. Both MATCH on this snapshot; both fail on the 1029Z interpreter (no
model for `Character.isTitleCase(char)`, resp. `CharSequence.subSequence` on a builder).

## java.lang.CharSequence (calls through the interface)

| Method | Receiver | Label |
|---|---|---|
| `length()` | String, StringBuilder, StringBuffer, application classes | listed |
| `charAt(int)` | String, StringBuilder, StringBuffer, application classes | listed |
| `toString()` | String, StringBuilder, StringBuffer, application classes | listed |
| `subSequence(int, int)` | String, application classes | listed |
| `subSequence(int, int)` | StringBuilder, StringBuffer | new (the builder model's `substring(int, int)`) |

## java.lang.Character

| Method | Label |
|---|---|
| `isWhitespace(char)`, `isWhitespace(int)` | listed |
| `toLowerCase(char)`, `toLowerCase(int)` | listed |
| `toUpperCase(char)`, `toUpperCase(int)` | listed |
| `toTitleCase(char)`, `toTitleCase(int)` | listed |
| `charCount(int)` | listed |
| `isDigit(char)`, `isDigit(int)` | listed |
| `isLetter(char)`, `isLetter(int)` | listed |
| `isLetterOrDigit(char)`, `isLetterOrDigit(int)` | listed |
| `isLowerCase(char)`, `isLowerCase(int)` | listed |
| `isUpperCase(char)`, `isUpperCase(int)` | listed |
| `isTitleCase(int)` | listed |
| `isHighSurrogate(char)`, `isLowSurrogate(char)` | listed |
| `getType(char)` | listed |
| `digit(char, int)`, `digit(int, int)`, `forDigit(int, int)` | listed |
| `valueOf(char)` | listed |
| `charValue()`, `equals`, `hashCode`, `compareTo`, `toString()` (the box) | listed |
| `getType(int)` | fixed: an invalid code point (negative) has type 0 (was 15) |
| the `int` predicates (`isDefined`, `isJavaIdentifierStart`/`Part`, `isUnicodeIdentifierStart`/`Part`, `isIdentifierIgnorable`, `isMirrored`, …) | fixed: a negative code point satisfies none (`isDefined` was `true`, the identifier predicates and `isMirrored` went `wrong`) |
| `codePointAt(CharSequence, int)`, `codePointBefore(CharSequence, int)` | fixed: the JDK's message for a bad index ("String index out of range: i" for a Latin-1 `String`, "index i, length n" otherwise) |
| `isTitleCase(char)` | new |
| `compare(char, char)` | new |
| `toChars(int)` | new (IllegalArgumentException "Not a valid Unicode code point: 0x…") |
| `codePointAt(char[], int)` | new |
| `codePointCount(CharSequence, int, int)`, `codePointCount(char[], int, int)` | new |
| the other `char` predicates: `isSpaceChar`, `isDefined`, `isISOControl`, `isMirrored`, `isJavaIdentifierStart`/`Part`, `isUnicodeIdentifierStart`/`Part`, `isIdentifierIgnorable` | new (`isX(char c)` is `isX((int) c)`) |

## Left for after D2 (outside the two families)

- The other boxed classes (Integer, Long, Short, Byte, Boolean, Double, Float) still sit under the header
  `## Boxed primitives (…)`, which veriforch's reader does not match.
- The out-of-range messages of `String.charAt` and `StringBuilder.charAt` (and so of
  `CharSequence.charAt` on those receivers) are not JDK 17's.

## All changes since the D pin (1029Z)

From 1029Z to 20261025T0149Z, the semantics and the library models (`Jimple/Native.lean`,
`Jimple/Semantics.lean`, `docs/LIBRARY_MODELS.md`) are unchanged. The changes are in the proof
automation (`Jimple/Tactic.lean`, `Jimple/SimpAttr.lean`), the examples and the README:

- 20261024T1546Z:
  - automation: `jFrameFacts`; nested `∃` in `jExists`; `StrMono`/`StrsAt` lemmas and `jStrsMono`;
    `Fields.get` lemmas; the `jspec` simproc (contract constants unfold only when applied);
    `jFoldCuts` (cut list and postcondition folded, option `jimple.foldCuts`, on by default);
    `jInjections`; heap lemmas and `jomega_rel` in the discharger; debugging options;
  - examples: the CBACT02C Java proofs (`Examples/CardDemo/Cbact02c*`).
- 20261024T2006Z:
  - automation: `jFrameStep` with `@[jframe]` lemmas; option `jimple.hypHeapFacts` (off by default);
    `ite_nat_ne` removed from `jsimp`;
  - examples: the CBCUS01C proofs.
- 20261024T2110Z:
  - automation: per-cut-point facts in `jFoldCuts`; a second unification pass in the preparation;
  - examples: the CBACT03C proofs.
- 20261025T0149Z: the automation for contracts on abstract states, behind
  `set_option jimple.modelContracts true` (off by default; off, `jvc` runs the 2110Z code).
- This snapshot:
  - the Character and CharSequence changes above, in `Jimple/Native.lean`;
  - `jsimp` unfolds the two new helpers `Native.argSeq` and `Native.seqCharAt`;
  - the model table is regenerated by `tools/gen_library_models.py`;
  - the difftest programs are in `~/jimplelean_work/difftest/src`.
