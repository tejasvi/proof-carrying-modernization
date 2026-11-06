# Differential testing against the JVM

`tools/difftest.sh` (in `~/jimplelean_work`) checks the semantics on real programs: each Java
program is run on the JVM and, after translation to Jimple by Soot, by the executable interpreter of
`Jimple/Interp.lean`; standard output and exit status must agree byte for byte.

## Running

```
tools/difftest.sh [-n] [-s DIR] [NAME...]
```

* `NAME`: a program `DIR/NAME.java` whose public class `NAME` has `main(String[])`; without names,
  every `DIR/*.java` runs.
* `-s DIR`: source directory, default `difftest/src` (the regression corpus); `difftest/repro` holds
  the minimal repros of open issues.
* `-n`: do not rebuild `jimple-run`. Without it the script rebuilds `jimple-run` only if a module of its
  import closure is newer than the binary, holding the workspace lock `build.lock` for that one
  `lake build`.

Per program:

1. `javac --release 8 -d difftest/build/NAME/classes DIR/NAME.java` (Java 8 bytecode: string
   concatenation through `StringBuilder`, lambdas through `invokedynamic`; see the options below)
2. `java NAME` → `difftest/expected/NAME.txt` and its exit status
3. Soot 4.7.1 (`toolchain/soot-4.7.1-jar-with-dependencies.jar`): `-pp -allow-phantom-refs
   -cp classes -process-dir classes -f J` → `difftest/build/NAME/jimple/*.jimple`
4. `jimple-run difftest/build/NAME/jimple NAME` → `difftest/out/NAME.txt` (stdout), `NAME.err` (stderr)
5. MATCH iff stdout and exit status agree; otherwise DIFF with the first differing lines.

javac, java and Soot run on JDK 17 (`/usr/lib/jvm/java-17-openjdk-amd64`) with one CPU, serial GC,
a 1 GB heap and no perf files in `/tmp`; everything runs under `nice` and `ulimit -v 32 GB`. The script
exits with 0 iff every program matches. The 37 corpus programs take about 55 s.

Per-program options are comment lines `// difftest-KEY: VALUE` in the source:

* `// difftest-release: 17`: compile with `javac --release 17` (records, `invokedynamic` string
  concatenation) instead of 8.
* `// difftest-cp: junit5` (or `junit4`, or both separated by a space): put library jars on the
  classpath of javac, java and Soot. `junit5` is junit-jupiter-api 5.10.2, opentest4j 1.3.0,
  junit-platform-commons 1.10.2 and apiguardian-api 1.1.2; `junit4` is junit 4.13.2 and
  hamcrest-core 1.3. They are Maven Central downloads in `~/jimplelean_work/junit_dl`; before each
  use the script compares their SHA-1 sums with the published `.sha1` files, and javac runs with
  `-proc:none`. The JVM runs the real JUnit code (that is the reference); Soot converts only the
  program's classes, and the interpreter uses the JUnit models of `Jimple/Native.lean`. `lang3`
  is commons-lang3 3.14.0 (`scale/lang3_dl`, also checksummed).
* `// difftest-jimple: jdkregex` (or `lang3`, or both): also load library classes from Jimple:
  `jdkregex` is the JDK 17 `java.util.regex` package converted from bytecode by
  `tools/jdkregex.sh` (`jdkregex/jimple`), `lang3` the Jimple of commons-lang3 3.14.0
  (`scale/lang3_jimple`). `jimple-run` accepts several directories separated by `:`.

### jimple-run

`jimple-run` (`JimpleLean/JimpleRun.lean`, built by `lake build jimple-run`, binary
`JimpleLean/.lake/build/bin/jimple-run`) parses `.jimple` files at run time with `Jimple.Parser` and
runs the interpreter natively:

```
jimple-run DIR MAINCLASS [--fuel N]     # run MAINCLASS.main(new String[0])
jimple-run DIR --stats                  # parse only: classes, methods, statements, parse time
```

Exit status: 0 normal, 1 uncaught exception (stderr names it, like the JVM), 2 usage or parse error,
3 `wrong` (unmodelled or undefined behaviour; nothing is printed on stdout, since a `wrong` run has
no final state), 4 out of fuel (default 10^8 steps). Nondeterministic choices are resolved to the
first alternative (see `LIBRARY_MODELS.md`).

### Writing a test program

Print ASCII only (the JVM's output encoding depends on the locale; use `\u` escapes in sources) and
avoid what the JDK leaves unspecified, which the model treats as nondeterministic: `HashMap`/`HashSet`
iteration order, `==` on boxes and strings, identity hash codes and `Object.toString`, and the text of
JVM-generated `NullPointerException` messages. Floating-point values cannot be printed (no model of
`Double.toString`); print `(int)` or `(long)` casts, or the bits from `Double.doubleToLongBits`, instead. Do not
print `doubleToRawLongBits` of a NaN: the JVMS leaves NaN bit patterns open; HotSpot on x86-64 returns
`0xFFF8000000000000` for an invalid operation (`0.0/0.0`) and flips the sign bit on negation, while the model
always gives the canonical `0x7FF8000000000000`.

## Corpus (`difftest/src`): 42 programs, 42 MATCH

| Program | Covers |
|---|---|
| Arith | int/long arithmetic over edge values: + - * / % shifts, comparisons, narrowing casts, `/ by zero` |
| Coll | ArrayList, HashMap counts, LinkedHashMap entry iteration, TreeMap keys, interface dispatch, iterator exceptions |
| Dec | BigDecimal: toString/toPlainString, scale, precision, all rounding modes, add/subtract/multiply/divide (scale, MathContext, exact), remainder |
| Exc | try/catch/finally, custom exceptions, ClassCastException, NullPointerException, array and negative-size exceptions |
| Strs | String methods, StringBuilder, enums, abstract classes, static initializer, parseInt, Math exact operations, switch on int and String |
| Iface | interface default and static methods, `Greeter.super.greet()`, abstract classes, `super` calls, most specific default method |
| Ctors | `this(...)`/`super(...)` chains, field and instance initializers, static initializer order, lazy class initialization |
| Nested | static nested, inner (and inner-of-inner), local and anonymous classes, synthetic accessors to private members |
| Enums | enum fields/constructors, constant-specific bodies, values/valueOf/ordinal/compareTo, switch on enum (`$SwitchMap`) |
| Loops | labeled break/continue, nested loops, sieve, do-while, matrix product, switch fall-through |
| Chars | char arithmetic and compound assignment, Character helpers, char arrays, Caesar cipher, letter counts |
| Mixed | int/long mixing and overflow, shifts, narrowing, compound assignment on byte/short/char, float/double to integer casts, radix strings |
| Arrays2D | jagged and 3-D arrays, arrays of objects, clone, covariant stores (ArrayStoreException), java.util.Arrays |
| Varargs | varargs with zero, one, many and array arguments, `Object...` with boxing, overload choice |
| Boxing | autoboxing in List/TreeMap/LinkedHashMap/LinkedList/TreeSet, box equality and hashCode, null unboxing |
| BigInt | BigInteger factorial and Fibonacci, signs of divide/remainder/mod, gcd, pow, shifts, bits, radix strings, modPow |
| Invoice | BigDecimal business math: invoice lines, tax with HALF_UP/HALF_EVEN, ties, MathContext, interest, divideAndRemainder, sorting |
| Builders | StringBuilder/StringBuffer insert, delete, deleteCharAt, replace, reverse, setLength (truncate/pad), setCharAt, substring |
| Excs | exception hierarchies and causes, finally overriding return, nested try/finally, try-with-resources with failing close |
| Recur | Fibonacci (naive/memoised), gcd, Ackermann, Hanoi, mutual recursion, permutations by backtracking, depth 2000 |
| Maps | TreeMap/LinkedHashMap/TreeSet orders, TreeMap navigation, legal Iterator.remove on lists, sets and entry sets |
| Bank | accounts in a LinkedHashMap, BigDecimal money, fees and interest, custom checked exceptions, audit log |
| Shapes | polymorphism, abstract classes and interfaces, instanceof and casts, overloading vs overriding, equals/hashCode |
| Models | edge cases of the library models added with the corpus (StringBuilder, Iterator.remove, Collections, Arrays, TreeMap, radix helpers, BigInteger) |
| AppKeys | library collections calling application equals/compareTo (lists, hash and tree maps/sets, sorting, exceptions from callbacks), `println(char[])` |
| Parse | `new BigDecimal(String)`, `Integer/Long.parseInt` (edge values, invalid input, null), `BigInteger(String)`, strings with surrogates |
| Surrogates | StringBuilder.reverse with surrogate pairs and lone surrogates, other operations on surrogate code units |
| Bits | Integer/Long rotateLeft/Right, bitCount, numberOfLeading/TrailingZeros, highest/lowestOneBit on edge values |
| TreeChecks | JDK 17 key checks of TreeMap/TreeSet: `compareTo(key, key)` on the first insertion into an empty tree (put, putIfAbsent, add, addAll, copy constructor), ClassCastException for non-`Comparable` keys in lookups even on empty trees, NPE for `null`, exceptions from `compareTo` |
| Records | (`--release 17`) records: generated toString/hashCode/equals over int, long, char, boolean, byte, short, String, BigDecimal, boxes, nested and generic records, enums, lists, NaN and -0.0 components; empty, local, compact-constructor and interface-implementing records, overridden toString and accessors, records as HashMap keys; the order of component calls in equals (last first), hashCode and toString |
| Jup5 | (JUnit 5.10.2) `Assertions.assertTrue/False/Null/NotNull/Same/NotSame/Equals` (primitives, boxes, Object, application equals/toString), `assertThrows` (lambdas, subclasses, wrong type with cause, nothing thrown, `null` executable), `fail` variants; String and Supplier messages, blank messages, `AssertionFailedError.toString` |
| AsList | `Arrays.asList`: writes through both ways (array and `set`), live iterator, `UnsupportedOperationException`s of `add`/`remove`/`clear`/`addAll` (with and without effect), `get` out of range, element-wise `equals` both ways with `ArrayList` (application `equals` called back), `toArray`, `forEach`, copy constructor, rendering of sublists and `Collections.emptySet()` |
| StreamsLite | `Stream.of`/`empty`/`skip`/`limit`, `noneMatch`/`anyMatch`/`allMatch` with lambdas, `collect` with an application `Collector` (the order of its calls), single use, negative `skip`, `StringJoiner` (`add`, `null` elements, `setEmptyValue`, `length`, `null` delimiter), `Collections.emptySet()` |
| SplitFast | `String.split` with a single literal separator (the JDK's fast path, modelled natively): limits, leading and trailing empty segments, empty input, no separator |
| Jup5Arr | (JUnit 5.10.2, `--release 17`) `assertNotEquals` (primitives, boxes, Object, application equals), `assertArrayEquals` for every primitive array kind and Object arrays: index paths in nested arrays, lengths, `null` arrays and elements, application equals called back, lists as elements; arrays and lists in `assertEquals` messages |
| Ju4Arr | (JUnit 4.13.2) `assertNotEquals` (long, Object), `assertArrayEquals` (primitive, String, application and nested arrays): `ArrayComparisonFailure` messages and causes, length differences with "end of array" and nested-array placeholders, the `deepEquals` pass before the element pass (visible in equals callbacks), its `toString` |
| Ju4 | (JUnit 4.13.2) `Assert.assertTrue/False/Null/NotNull/Same/NotSame/Equals`, `fail`, `assertThrows`; messages including `ComparisonFailure`'s compaction (prefix/suffix elision, empty diffs), class names for equal renderings; `new AssertionError(Object)` |
| Fmt | (`--release 17`) `String.format`/`formatted` and `printf`: the modelled conversions, flags, widths and argument indices, and the JDK's exceptions for bad formats |
| Uni | Unicode character properties and case mappings beyond ASCII (`Character` on `char` and code points, `String.toUpperCase`/`toLowerCase`, `equalsIgnoreCase`) |
| CharFamily | `java.lang.Character` (D2): its static methods on `char` and `int` over a sweep of code points, invalid code points, surrogates, `toChars`, `codePointAt`/`codePointCount` on `CharSequence` and `char[]` with their exceptions, `compare`, the box |
| CharSeqIface | (`--release 17`) calls through `java.lang.CharSequence` (D2) on String, StringBuilder, StringBuffer and an application class: `length`, `charAt`, `subSequence`, `toString`, with their exceptions |
| FloatSem | floating-point semantics through `Double.doubleToLongBits` (NaN canonical): double and float `+ - * / %` and comparisons over NaN, zeros, infinities and subnormals, `Double.compare`, narrowing and widening conversions, int/long to float/double, negation, run-time literals |

## Libraries from bytecode (`difftest/regex`): 3 programs, 3 MATCH

`tools/difftest.sh -s difftest/regex` runs programs whose library classes are loaded from Jimple
instead of being modelled (see "Libraries from bytecode" in `LIBRARY_MODELS.md`).

| Program | Covers |
|---|---|
| RegexPilot | the JDK 17 `java.util.regex` package from bytecode: `find`/`group`/`start`/`end`, alternation, empty matches, optional and named groups, lazy and greedy quantifiers, anchors, `(?i)`, `\b`, back references, lookahead, negated classes, `\p{Upper}`, class intersection, `split` with and without limit, `replaceAll`/`replaceFirst` with `$n`, `appendReplacement`/`appendTail`, `quote`, `quoteReplacement`, regions, `lookingAt`/`hitEnd`, `PatternSyntaxException`, `IllegalStateException` (31 lines; 0.2 s) |
| StringRegex | `String.matches`, `split` (regex and fast path, limits), `replaceAll`, `replaceFirst` through the bytecode `Pattern`: zero-width splits, lookbehind, `$n` and `\\$` in replacements, a `null` replacement without match, `PatternSyntaxException`, `split(null)`, `No group 3` |
| StrUtilsPilot | commons-lang3 3.14.0 `StringUtils` from its Jimple with the regex package: the static initializer's `Pattern.compile("\\p{InCombiningDiacriticalMarks}+")`, 36 methods (`isBlank`, `capitalize`, `leftPad`, `replacePattern`, `removePattern` (via `ObjectUtils.anyNull`'s `Stream.of(...).noneMatch`), `split`, `abbreviate`, `center`, `reverse`, `countMatches`, `substringBetween`, `strip`, `containsIgnoreCase`, `difference`, `swapCase`, `normalizeSpace`, `replaceEach`, `splitByCharacterTypeCamelCase`, `lastIndexOfIgnoreCase`, `join` of `Object[]` (stream pipeline with lang3's `Collector` and `StringJoiner`) and `int[]`, ...) |

Not yet: `stripAccents` (`java.text.Normalizer`), non-ASCII character classes.

## Repros (`difftest/repro`): 6 MATCH, 3 DIFF

| Repro | Status | Explanation |
|---|---|---|
| ReproDefault | MATCH | default-method selection picks the maximally specific interface method (fixed in `Program.lean`) |
| ReproIfaceInit | MATCH | class initialization also initializes superinterfaces with default methods (fixed in `Semantics.lean`) |
| ReproNoClassDef | MATCH | `NoClassDefFoundError` message `Could not initialize class X` (fixed in `Semantics.lean`) |
| ReproAppEquals | MATCH | library collections call application `equals` (callbacks in `Native.lean`) |
| ReproCharArrays | MATCH | `println(char[])` and `String.valueOf(char[])` print the characters |
| ReproSurrogateReverse | MATCH | `StringBuilder.reverse` keeps surrogate pairs in order |
| ReproNpeMessage | DIFF (by design) | JDK 14+ "helpful" NullPointerException messages are not specified by the JLS; the model's message is `null` |
| ReproSootCast | DIFF (front end) | Soot types an `Object[]` local holding a `String[]` as `String[]` and inserts a `(String)` cast, so the Jimple throws ClassCastException where the bytecode throws ArrayStoreException; not a semantics issue |
| ReproUnicodeDigits | DIFF (by design) | the JDK parses non-ASCII Unicode digits (`Integer.parseInt("١٢")` = 12); the model goes `wrong` ("non-ASCII numeric text is not modelled") |

## Front-end scale check (2026-10-23)

Real libraries from Maven Central (checksums verified; their code was never run on the JVM):

| | commons-codec 1.16.0 | commons-lang3 3.14.0 |
|---|---|---|
| classes in the jar / Jimple classes (incl. Soot's lambda classes) | 109 / 133 | 404 / 675 |
| methods / bodies / statements / traps | 1,116 / 1,095 / 21,473 / 55 | 5,386 / 5,258 / 51,525 / 146 |
| Soot (wall, peak RSS) | 1.9 s, 0.66 GB | 3.4 s, 0.77 GB |
| `jimple-run --stats` parse (native) | 0.19 s, 0 parse failures | 0.52 s, 0 parse failures |
| `jimple_import` of the whole directory (wall, peak RSS) | 12.2 s, 1.07 GB | 26.3 s, 1.36 GB |

Driver programs run with `jimple-run` (results checked against independent Python implementations
or by hand): commons-codec `Base64` encode/decode, `MurmurHash3.hash32x86` (two seeds),
`MurmurHash2.hash32/hash64`; commons-lang3 `ArrayUtils.reverse/contains/indexOf/lastIndexOf` and
`NumberUtils.max/toInt/compare/toLong` all agree. Stopped as `wrong` (library parts with no model):
`Hex` (its initializer reads `StandardCharsets.UTF_8`), `Soundex`/`Metaphone` (`Locale.ENGLISH`),
`StringUtils` (its initializer compiles a `java.util.regex.Pattern`), `ArrayUtils.isEmpty/add`
(reflection: `java.lang.reflect.Array`, `Long.TYPE`).
