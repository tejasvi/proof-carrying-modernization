# Library models

Generated from `Jimple/Native.lean` by `tools/gen_library_models.py` (do not edit by hand; rerun the
script after changing the models). Each row is one match arm of a model; parameter types are read
from the arm's pattern or from how it reads the argument (`?` = any type, `T` = the static type of the
argument, which selects the rendering).

How the models behave:
* A library call that matches no row has no model: the outcome is `wrong` ("no model for library
  method C.m"), so a proof never assumes behaviour that is not modelled. The same holds for unknown
  library classes and static fields ("no model for static field").
* "wrong:" in the notes lists the cases a modelled method still leaves unmodelled.
* Nondeterministic behaviour (the JDK leaves it unspecified) is a `Res.choose`: the semantics allows
  every value. The interpreter (`jimple-run`, `runMain`) always picks choice 0: identity hash codes and
  times are 0, hash-based collections iterate in insertion order, `==` between distinct value objects
  with equal contents (strings, boxes, BigDecimal, BigInteger, MathContext) is `true`.
* "calls application ..." marks models that call back into application code (`toString` when rendering
  objects as text, `equals`/`compareTo` in collections, sorting and searching).
* A `null` receiver, or a `null` argument where the model needs an object, throws NullPointerException.
* Floating-point values cannot be converted to text (`Double.toString`, string concatenation and
  `println` of `float`/`double`): such calls go `wrong`.
* `String.format`, `String.formatted`, `PrintStream.printf`/`format` (`formatK`): `%s %S` (width, `-`,
  precision), `%d` on Integer/Long/Short/Byte/BigInteger with the flags `-` `0` `+` space `,` `(`,
  `%x %X %o` on Integer/Long, `%c`, `%b %B`, `%f` on BigDecimal (rounded HALF_UP, same flags as
  `%d`), `%n`, `%%`, explicit (`2$`) and relative (`<`) argument indices, in the en_US locale.
  Missing arguments, unknown conversions and arguments of the wrong class throw the JDK's
  exceptions with its messages; floating-point arguments, `%e %g %a %h %t`, `#` and other flag
  combinations go `wrong`.

Not modelled at all (outcome `wrong`): reflection (`java.lang.reflect`, `Class` beyond `getName`,
`getSimpleName` and `getCanonicalName`), threads and synchronization beyond monitors, regular expressions, character sets and
locales (`String.getBytes`, `StandardCharsets`, `Locale`), I/O other than `System.out`,
streams and lambdas' library side (`java.util.function` interfaces can be implemented by application
classes, including the classes Soot generates for lambdas).


## java.lang.String

A `String` is its list of UTF-16 code units (`Obj.str`). Case conversion and `equalsIgnoreCase` are modelled for ASCII text only (other text goes `wrong`: the JDK result is locale dependent). `intern` returns the receiver; `==` between distinct strings with equal contents is nondeterministic.

| Constructor | Notes |
|---|---|
| `new String()` |  |
| `new String(String)` |  |
| `new String(char[])` |  |
| `new String(char[], int, int)` | throws StringIndexOutOfBoundsException |
| `new String(int[], int, int)` | throws IllegalArgumentException, StringIndexOutOfBoundsException |

| Static method | Notes |
|---|---|
| `String.valueOf(T)` | calls application toString; wrong: float/double arguments: floating-point to string conversion is not modelled |
| `String.format(String, ?)` | throws NullPointerException |
| `String.join(CharSequence, ?[])` | throws NullPointerException |
| `String.join(CharSequence, List)` | throws NullPointerException; wrong: String.join of this Iterable is not modelled |

| Instance method (`stringInst`) | Notes |
|---|---|
| `length()` |  |
| `formatted(Object)` |  |
| `isEmpty()` |  |
| `charAt(int)` | throws StringIndexOutOfBoundsException |
| `equals(Object)` |  |
| `equalsIgnoreCase(String)` | wrong: equalsIgnoreCase with surrogates is not modelled |
| `hashCode()` |  |
| `compareTo(String)` |  |
| `compareToIgnoreCase(String)` |  |
| `concat(String)` |  |
| `substring(int)` | throws StringIndexOutOfBoundsException |
| `substring(int, int)` | throws StringIndexOutOfBoundsException |
| `indexOf(String)` |  |
| `indexOf(int)` |  |
| `contains(CharSequence)` |  |
| `startsWith(String)` |  |
| `endsWith(String)` |  |
| `trim()` |  |
| `toUpperCase()` |  |
| `toLowerCase()` | wrong: toLowerCase of a capital sigma is not modelled |
| `toString()` |  |
| `intern()` |  |
| `replace(char, char)` |  |
| `repeat(int)` | throws IllegalArgumentException |
| `toCharArray()` |  |
| `codePointAt(int)` | throws StringIndexOutOfBoundsException |
| `codePointBefore(int)` |  |
| `codePointCount(int, int)` | throws IndexOutOfBoundsException |
| `subSequence(int, int)` | throws StringIndexOutOfBoundsException |
| `indexOf(String, int)` |  |
| `indexOf(int, int)` |  |
| `lastIndexOf(int)` | wrong: lastIndexOf of a supplementary code point is not modelled |
| `lastIndexOf(int, int)` | wrong: lastIndexOf of a supplementary code point is not modelled |
| `lastIndexOf(String)` |  |
| `lastIndexOf(String, int)` |  |
| `matches(Object)` |  |
| `replaceAll(Object, Object)` |  |
| `replaceFirst(Object, Object)` |  |
| `split(Object)` |  |
| `split(Object, int)` |  |
| `regionMatches(int, String, int, int)` |  |
| `regionMatches(boolean, int, String, int, int)` | wrong: regionMatches ignoring case on non-ASCII text is not modelled |

## java.lang.StringBuilder, java.lang.StringBuffer

Both classes share one model (`Obj.builder`); mutators update the object in place and return it.

| Constructor | Notes |
|---|---|
| `new StringBuilder()` |  |
| `new StringBuilder(int)` | throws NegativeArraySizeException |
| `new StringBuilder(CharSequence)` |  |
| `new StringBuffer()` |  |
| `new StringBuffer(int)` | throws NegativeArraySizeException |
| `new StringBuffer(CharSequence)` |  |

| Instance method (`builderInst`) | Notes |
|---|---|
| `append(T)` | calls application toString; wrong: float/double arguments: floating-point to string conversion is not modelled |
| `toString()` |  |
| `length()` |  |
| `charAt(int)` | throws StringIndexOutOfBoundsException |
| `reverse()` |  |
| `setLength(int)` | throws IndexOutOfBoundsException |
| `insert(int, T)` | throws StringIndexOutOfBoundsException; calls application toString; wrong: float/double arguments: floating-point to string conversion is not modelled |
| `deleteCharAt(int)` | throws StringIndexOutOfBoundsException |
| `setCharAt(int, char)` | throws StringIndexOutOfBoundsException |
| `indexOf(String)` |  |
| `isEmpty()` |  |
| `delete(int, int)` | throws StringIndexOutOfBoundsException |
| `replace(int, int, String)` | throws StringIndexOutOfBoundsException |
| `substring(int)` | throws StringIndexOutOfBoundsException |
| `substring(int, int)` | throws StringIndexOutOfBoundsException |
| `subSequence(int, int)` | throws StringIndexOutOfBoundsException |
| `lastIndexOf(String)` |  |
| `appendCodePoint(int)` | wrong: appendCodePoint of an invalid code point is not modelled |
| `append(CharSequence, int, int)` | throws IndexOutOfBoundsException |

## java.lang.CharSequence

A call through the interface runs the receiver's method: the `String` model for strings, the builder model for `StringBuilder` and `StringBuffer` (their sections give each method's exceptions), and its own method for an object of an application class. Other library implementations of `CharSequence` have no model. The rows are the interface's abstract methods; its default methods (isEmpty, chars, codePoints) are not listed: on an application class they have no model.

| Interface method | Notes |
|---|---|
| `length()` | String, StringBuilder, StringBuffer; application classes: their own method |
| `charAt(int)` | String, StringBuilder, StringBuffer; application classes: their own method |
| `toString()` | String, StringBuilder, StringBuffer; application classes: their own method |
| `subSequence(int, int)` | String, StringBuilder, StringBuffer; application classes: their own method |

## Boxed primitives (Integer, Long, Short, Byte, Boolean, Double, Float)

`valueOf` allocates a box (`Obj.boxed`); the JDK box caches are not modelled, so `==` between equal boxes is nondeterministic (the interpreter answers `true`). `toString` of `Double`/`Float` boxes, and every other conversion of a floating-point value to text, goes `wrong`. `Character`: see java.lang.Character.

| Static method | Notes |
|---|---|
| `Integer.valueOf(int)` |  |
| `Long.valueOf(long)` |  |
| `Short.valueOf(short)` |  |
| `Byte.valueOf(byte)` |  |
| `Boolean.valueOf(boolean)` |  |
| `Double.valueOf(double)` |  |
| `Float.valueOf(float)` |  |
| `Integer.parseInt(String)` | throws NumberFormatException; wrong: non-ASCII numeric text is not modelled |
| `Integer.valueOf(String)` | throws NumberFormatException; wrong: non-ASCII numeric text is not modelled |
| `Long.parseLong(String)` | throws NumberFormatException; wrong: non-ASCII numeric text is not modelled |
| `Integer.toString(int)` |  |
| `Long.toString(long)` |  |
| `Integer.compare(int, int)` |  |
| `Long.compare(long, long)` |  |
| `Integer.max(int, int)` |  |
| `Integer.min(int, int)` |  |
| `Integer.sum(int, int)` |  |
| `Integer.signum(int)` |  |
| `Boolean.parseBoolean(String)` |  |
| `Double.isNaN(double)` |  |
| `Float.isNaN(float)` |  |
| `Double.compare(double, double)` |  |
| `Double.doubleToLongBits(double)` |  |
| `Double.doubleToRawLongBits(double)` |  |
| `Double.longBitsToDouble(long)` |  |
| `Long.signum(long)` |  |
| `Integer.toBinaryString(int)` |  |
| `Integer.toHexString(int)` |  |
| `Integer.toOctalString(int)` |  |
| `Long.toBinaryString(long)` |  |
| `Long.toHexString(long)` |  |
| `Long.toOctalString(long)` |  |
| `Integer.toString(int, int)` |  |
| `Integer.parseInt(String, int)` | throws NumberFormatException; wrong: Integer.parseInt with a radix out of range is not modelled; non-ASCII numeric text is not modelled |
| `Integer.rotateLeft(int, int)` |  |
| `Integer.rotateRight(int, int)` |  |
| `Long.rotateLeft(long, int)` |  |
| `Long.rotateRight(long, int)` |  |
| `Integer.bitCount(int)` |  |
| `Long.bitCount(long)` |  |
| `Integer.numberOfLeadingZeros(int)` |  |
| `Long.numberOfLeadingZeros(long)` |  |
| `Integer.numberOfTrailingZeros(int)` |  |
| `Long.numberOfTrailingZeros(long)` |  |
| `Integer.highestOneBit(int)` |  |
| `Long.highestOneBit(long)` |  |
| `Integer.lowestOneBit(int)` |  |
| `Long.lowestOneBit(long)` |  |

| Static field | Notes |
|---|---|
| `Boolean.TRUE` |  |
| `Boolean.FALSE` |  |
| `Integer.MAX_VALUE` |  |
| `Integer.MIN_VALUE` |  |
| `Long.MAX_VALUE` |  |
| `Long.MIN_VALUE` |  |

| Instance method (`boxedInst`) | Notes |
|---|---|
| `intValue()` |  |
| `longValue()` |  |
| `shortValue()` |  |
| `byteValue()` |  |
| `doubleValue()` |  |
| `booleanValue()` |  |
| `charValue()` |  |
| `equals(Object)` |  |
| `hashCode()` |  |
| `compareTo(Object)` | throws NullPointerException |
| `floatValue()` |  |
| `toString()` |  |

## java.lang.Character

A `Character` box is an `Obj.boxed`, as the other boxes. Every predicate `isX(char c)` is `isX((int) c)`, as in the JDK. Exact on all code points: `charCount`, `codePointAt`/`codePointBefore`/`codePointCount` (`CharSequence` = `String` or `StringBuilder`, or a `char[]`), `toChars(int)`, `toCodePoint`, `compare`, `isHighSurrogate`, `isLowSurrogate`, `isSurrogate`, `isSurrogatePair`, `isSupplementaryCodePoint`, `isBmpCodePoint`, `isValidCodePoint`, `isISOControl`. On `char` and `int` code points: `getType`, `toUpperCase`, `toLowerCase`, `toTitleCase` and the predicates `isUpperCase`, `isLowerCase`, `isTitleCase`, `isLetter`, `isAlphabetic`, `isDigit`, `isLetterOrDigit`, `isWhitespace`, `isSpaceChar`, `isIdeographic`, `isDefined`, `isMirrored`, `isJavaIdentifierStart`, `isJavaIdentifierPart`, `isUnicodeIdentifierStart`, `isUnicodeIdentifierPart`, `isIdentifierIgnorable`; an invalid code point (negative or above U+10FFFF) satisfies no predicate and has type 0. Beyond ASCII, `getType`, the case mappings, `getNumericValue`, `digit` and the predicates `isUpperCase`, `isLowerCase`, `isTitleCase`, `isLetter`, `isAlphabetic`, `isDigit`, `isLetterOrDigit`, `isWhitespace`, `isSpaceChar`, `isIdeographic`, `isDefined` come from JDK 17 tables (`Jimple/Unicode.lean`, dumped by `data/UniDump.java`) for every code point; the identifier and `isMirrored` predicates go `wrong` there. `String.toUpperCase()`/`toLowerCase()` map code points as the English locale does, with the multi-character mappings (`ß` → `SS`, `İ` → `i̇`); a capital sigma in `toLowerCase` (the final-sigma rule) and surrogates in `equalsIgnoreCase`/`compareToIgnoreCase` go `wrong`. `Character.UnicodeBlock.forName`/`of` know the blocks up to Greek (U+0000-U+03FF), one object per block (blocks compare by identity).

| Static method | Notes |
|---|---|
| `Character.valueOf(char)` |  |
| `Character.isDigit(char)` |  |
| `Character.isLetter(char)` |  |
| `Character.isUpperCase(char)` |  |
| `Character.isLowerCase(char)` |  |
| `Character.isWhitespace(char)` |  |
| `Character.isLetterOrDigit(char)` |  |
| `Character.toUpperCase(char)` |  |
| `Character.toLowerCase(char)` |  |
| `Character.toString(char)` |  |
| `Character.forDigit(int, int)` |  |
| `Character.digit(char, int)` |  |
| `Character.getNumericValue(int)` |  |
| `Character.digit(int, int)` |  |
| `Character.getNumericValue(char)` |  |
| `Character.getType(char)` |  |
| `Character.charCount(int)` |  |
| `Character.isHighSurrogate(char)` |  |
| `Character.isLowSurrogate(char)` |  |
| `Character.isSurrogate(char)` |  |
| `Character.isSurrogatePair(int, int)` |  |
| `Character.toCodePoint(int, int)` |  |
| `Character.isSupplementaryCodePoint(int)` |  |
| `Character.isBmpCodePoint(int)` |  |
| `Character.isValidCodePoint(int)` |  |
| `Character.isISOControl(char)` |  |
| `Character.isISOControl(int)` |  |
| `Character.codePointAt(CharSequence, int)` | throws StringIndexOutOfBoundsException |
| `Character.codePointBefore(CharSequence, int)` | throws StringIndexOutOfBoundsException |
| `Character.getType(int)` |  |
| `Character.toUpperCase(int)` |  |
| `Character.toTitleCase(char)` |  |
| `Character.toTitleCase(int)` |  |
| `Character.toLowerCase(int)` |  |
| `Character.compare(char, char)` |  |
| `Character.toChars(int)` | throws IllegalArgumentException |
| `Character.codePointAt(char[], int)` | throws ArrayIndexOutOfBoundsException |
| `Character.codePointCount(CharSequence, int, int)` | throws IndexOutOfBoundsException |
| `Character.codePointCount(char[], int, int)` | throws IndexOutOfBoundsException |

| Instance method (`boxedInst`) | Notes |
|---|---|
| `charValue()` |  |
| `equals(Object)` |  |
| `hashCode()` |  |
| `compareTo(Object)` | throws NullPointerException |
| `toString()` |  |

## java.lang.Math

`int`/`long` methods and `Math.abs(double)`; other floating-point functions have no model.

| Static method | Notes |
|---|---|
| `Math.max(int, int)` |  |
| `Math.min(int, int)` |  |
| `Math.max(long, long)` |  |
| `Math.min(long, long)` |  |
| `Math.abs(int)` |  |
| `Math.abs(long)` |  |
| `Math.abs(double)` |  |
| `Math.addExact(int, int)` | throws ArithmeticException |
| `Math.subtractExact(int, int)` | throws ArithmeticException |
| `Math.multiplyExact(int, int)` | throws ArithmeticException |
| `Math.addExact(long, long)` | throws ArithmeticException |
| `Math.subtractExact(long, long)` | throws ArithmeticException |
| `Math.multiplyExact(long, long)` | throws ArithmeticException |
| `Math.toIntExact(long)` | throws ArithmeticException |
| `Math.floorDiv(int, int)` | throws ArithmeticException |
| `Math.floorMod(int, int)` | throws ArithmeticException |

## java.util.Objects

| Static method | Notes |
|---|---|
| `Objects.equals(Object, Object)` | calls application equals |
| `Objects.requireNonNull(Object)` | throws NullPointerException |
| `Objects.requireNonNull(Object, String)` | throws NullPointerException |
| `Objects.isNull(Object)` |  |
| `Objects.nonNull(Object)` |  |
| `Objects.toString(Object)` | calls application toString |
| `Objects.toString(Object, Object)` | calls application toString |
| `Objects.checkFromToIndex(int, int, int)` | throws IndexOutOfBoundsException |

## java.lang.reflect.Array

| Static method | Notes |
|---|---|
| `Array.newInstance(Class, int)` | throws NegativeArraySizeException |
| `Array.getLength(Object)` | throws IllegalArgumentException |

## java.util.stream.Stream (Stream.of), StringJoiner, Collections.emptySet

What commons-lang3 needs (`ObjectUtils.anyNull`/`allNotNull`, `StringUtils.join(Object[], ...)`): `Stream.of(values)`/`Stream.empty()` over the source array, read at the terminal operation; `skip` and `limit` (new stages; the old one becomes linked, `skip(0)` returns the stream itself; negative counts throw IllegalArgumentException); `noneMatch`, `anyMatch`, `allMatch` (the predicate called back in order until the result is decided); `collect(Collector)` with an application collector, called in the JDK's order: `supplier()`, `accumulator()`, `combiner()`, then the single-use check, `characteristics()`, `get()`, the accumulator on each element, `characteristics()`, `finisher()` and `apply` (characteristics must be empty sets). A second terminal operation throws IllegalStateException; other stream operations (`map`, `filter`, `forEach`, `Collectors.*`, primitive streams) go `wrong`. `java.util.StringJoiner` (plain objects): `add`, `toString`, `length`, `setEmptyValue`. `Collections.emptySet()` is one shared object (`size`, `isEmpty`, `contains`, `remove`, `clear`, `hashCode`, `add` throws UnsupportedOperationException). Sublists, `Arrays.asList` lists and the empty set render as `[a, b]`; `ArrayList.equals` of a sublist has no model, and generic equality (in collections, `Objects.equals`) of these objects is never decided by identity.

| Constructor | Notes |
|---|---|
| `new StringJoiner(CharSequence)` |  |
| `new StringJoiner(CharSequence, CharSequence, CharSequence)` |  |

| Static method | Notes |
|---|---|
| `Stream.empty()` |  |
| `Stream.of(?[])` | throws NullPointerException |
| `Stream.of(Object)` |  |

## Libraries from bytecode: java.util.regex

`java.util.regex` is not modelled: `tools/jdkregex.sh` converts the JDK 17 package from its bytecode (java.base.jmod) to Jimple (139 classes including Soot's lambda classes), which is loaded as application classes next to the program (`jimple-run PROGRAM_DIR:jdkregex/jimple MAIN`, difftest option `// difftest-jimple: jdkregex`). It runs on the models of this file (strings, code points, ASCII character classes, `StringBuilder`, `ArrayList`/`subList`/`toArray`, `HashMap`, `Objects.checkFromToIndex`, `Class.desiredAssertionStatus` (false: assertions are disabled), the internal `ArraysSupport.newLength` below). `String.matches`, `split`, `replaceAll` and `replaceFirst` call the bytecode `Pattern` as the JDK does (`Pattern.matches(regex, this)`, `Pattern.compile(regex).matcher(this).replaceAll(r)`, `Pattern.compile(regex).split(this, limit)`; the static call initializes `Pattern` first) when the regex classes are in the program, and have no model otherwise; `split`'s fast path (a single literal separator character) is modelled natively and needs no regex classes. Not available: `CANON_EQ` (`java.text.Normalizer`), Unicode scripts and categories beyond ASCII, `splitAsStream`/`results` (streams).

| Static method | Notes |
|---|---|
| `ArraysSupport.newLength(int, int, int)` | throws OutOfMemoryError |

## java.lang.System

`System.out` is the only output: text printed to `System.err` is discarded. Times and identity hash codes are nondeterministic (any value; the interpreter returns 0).

| Static method | Notes |
|---|---|
| `System.currentTimeMillis()` | nondeterministic: unspecified value |
| `System.nanoTime()` | nondeterministic: unspecified value |
| `System.identityHashCode(Object)` | nondeterministic: unspecified value |
| `System.lineSeparator()` |  |
| `System.arraycopy(Object, int, Object, int, int)` | throws ArrayIndexOutOfBoundsException, ArrayStoreException; wrong: arraycopy with element store checks is not modelled |

| Static field | Notes |
|---|---|
| `System.out` |  |
| `System.err` |  |

## java.util.Arrays

Arrays are `Obj.array` (element type + values). Sorting uses natural ordering; floating-point arrays are not sorted by the model.

| Static method | Notes |
|---|---|
| `Arrays.toString(T[])` | calls application toString; wrong: floating-point to string conversion is not modelled |
| `Arrays.sort(T[])` | throws ClassCastException (not mutually comparable), NullPointerException (null element); calls application compareTo; wrong: sorting floating-point arrays is not modelled |
| `Arrays.fill(?[], ?)` | throws ArrayStoreException |
| `Arrays.equals(?[], ?[])` | calls application equals |
| `Arrays.copyOf(?[], int)` | throws NegativeArraySizeException |
| `Arrays.copyOfRange(?[], int, int)` | throws ArrayIndexOutOfBoundsException, IllegalArgumentException |
| `Arrays.asList(?[])` | throws NullPointerException |

## java.util.Collections

| Static method | Notes |
|---|---|
| `Collections.emptyList()` |  |
| `Collections.sort(List)` | throws ClassCastException (not mutually comparable), NullPointerException (null element), UnsupportedOperationException; calls application compareTo; wrong: Collections.sort of this collection kind is not modelled |
| `Collections.max(Collection)` | throws ClassCastException (not mutually comparable), NoSuchElementException, NullPointerException (null element); calls application compareTo; wrong: Collections.max of this collection kind is not modelled |
| `Collections.min(Collection)` | throws ClassCastException (not mutually comparable), NoSuchElementException, NullPointerException (null element); calls application compareTo; wrong: Collections.min of this collection kind is not modelled |
| `Collections.reverse(List)` | throws UnsupportedOperationException; wrong: Collections.reverse of this collection kind is not modelled |
| `Collections.emptySet()` |  |

## java.util.List: ArrayList, LinkedList, List.of, Collections.emptyList

A list is `Obj.list kind values modCount`. `ArrayList.subList` returns a read-only view (a plain `java.util.ArrayList$SubList` object: `size`, `isEmpty`, `get`, `toArray`, `subList` read through to the list, with ConcurrentModificationException after a structural change of the list; writes and other methods go `wrong`). `Arrays.asList` returns a fixed-size list backed by the array (a plain `java.util.Arrays$ArrayList` object): `get`/`set` read and write the array, so changes show both ways; `size`, `indexOf`, `contains` (application `equals` called back), `toArray`, `iterator` (reads the array live; `remove` throws UnsupportedOperationException "remove"), `forEach`, `equals` (element-wise, as `AbstractList.equals`; `ArrayList.equals` of such a list too), `toString`; `add`, `remove(int)`, and `remove(Object)`/`clear`/`addAll` when they would change the list throw UnsupportedOperationException as `AbstractList`/`AbstractCollection` do; `hashCode`, `sort`, `replaceAll` go `wrong`. `List.of` and `Collections.emptyList` lists are immutable (mutators throw UnsupportedOperationException). Structural modifications increment the modification count; using an iterator after a modification that did not go through it is `wrong` (the JDK throws ConcurrentModificationException on a best-effort basis).

| Constructor | Notes |
|---|---|
| `new ArrayList()` |  |
| `new ArrayList(int)` | throws IllegalArgumentException |
| `new ArrayList(Collection)` | wrong: copy constructor from this collection kind is not modelled |
| `new LinkedList()` |  |
| `new LinkedList(int)` | throws IllegalArgumentException |
| `new LinkedList(Collection)` | wrong: copy constructor from this collection kind is not modelled |

| Static method | Notes |
|---|---|
| `List.of(Object...)` | throws NullPointerException |

| Instance method (`listInst`) | Notes |
|---|---|
| `size()` |  |
| `isEmpty()` |  |
| `get(int)` | throws IndexOutOfBoundsException |
| `add(Object)` | throws UnsupportedOperationException |
| `add(int, Object)` | throws IndexOutOfBoundsException, UnsupportedOperationException |
| `set(int, Object)` | throws IndexOutOfBoundsException, UnsupportedOperationException |
| `remove(int)` | throws IndexOutOfBoundsException, UnsupportedOperationException |
| `remove(Object)` | throws UnsupportedOperationException; calls application equals |
| `contains(Object)` | calls application equals |
| `indexOf(Object)` | calls application equals |
| `clear()` | throws UnsupportedOperationException |
| `addAll(Collection)` | throws UnsupportedOperationException; wrong: addAll from this collection kind is not modelled |
| `iterator()` |  |
| `toString()` | wrong: toString of these list elements is not modelled |
| `addFirst(Object)` | throws UnsupportedOperationException |
| `addLast(Object)` | throws UnsupportedOperationException |
| `getFirst()` | throws NoSuchElementException |
| `getLast()` | throws NoSuchElementException |
| `removeFirst()` | throws NoSuchElementException, UnsupportedOperationException |
| `equals(Object)` | calls application equals; wrong: equals with an ArrayList.subList view is not modelled; malformed Arrays.asList |
| `toArray()` |  |
| `toArray(?[])` |  |
| `subList(int, int)` | wrong: subList of this list kind is not modelled |

## java.util.Map: HashMap, LinkedHashMap, TreeMap

A map is `Obj.map kind entries modCount` with unique keys. Iteration order: insertion order (LinkedHashMap), ascending natural order (TreeMap), unspecified for HashMap (every permutation is allowed; the interpreter uses insertion order). Keys are compared with `equals` (hash maps; `hashCode` is never called) or `compareTo` (tree maps); application `equals`/`compareTo` are called back. TreeMap comparators are not modelled. Tree keys are checked as in JDK 17: `null` throws NullPointerException; lookups (`get`, `getOrDefault`, `containsKey`, `remove`) cast the key to `Comparable` before searching, so a key that is not `Comparable` throws ClassCastException even in an empty map; the first insertion into an empty tree compares the key with itself (`TreeMap.addEntryToEmptyMap`), calling an application `compareTo`. Beyond that, the number of `equals`/`compareTo` calls differs from the JDK's (hash buckets, red-black trees).

| Constructor | Notes |
|---|---|
| `new HashMap()` |  |
| `new HashMap(int)` |  |
| `new LinkedHashMap()` |  |
| `new LinkedHashMap(int)` |  |
| `new TreeMap()` |  |
| `new TreeMap(int)` |  |

| Instance method (`mapInst`) | Notes |
|---|---|
| `size()` |  |
| `isEmpty()` |  |
| `get(Object)` | throws ClassCastException, NullPointerException; calls application equals |
| `getOrDefault(Object, Object)` | throws ClassCastException, NullPointerException; calls application equals |
| `containsKey(Object)` | throws ClassCastException, NullPointerException; calls application equals |
| `put(Object, Object)` | throws NullPointerException; calls application equals |
| `putIfAbsent(Object, Object)` | throws NullPointerException; calls application equals |
| `remove(Object)` | throws ClassCastException, NullPointerException; calls application equals |
| `clear()` |  |
| `keySet()` |  |
| `values()` |  |
| `entrySet()` |  |
| `firstKey()` | throws NoSuchElementException |
| `lastKey()` | throws NoSuchElementException |
| `ceilingKey(Object)` | calls application compareTo |
| `higherKey(Object)` | calls application compareTo |
| `floorKey(Object)` | calls application compareTo |
| `lowerKey(Object)` | calls application compareTo |
| `containsValue(Object)` | calls application equals |

## java.util.Set: HashSet, LinkedHashSet, TreeSet

A set is `Obj.set kind elements modCount`; orders, equality and the tree key checks as for maps (`contains`, `remove`, `add`, `addAll` and the copy constructors of `TreeSet`).

| Constructor | Notes |
|---|---|
| `new HashSet()` |  |
| `new HashSet(int)` |  |
| `new HashSet(Collection)` | throws NullPointerException; calls application equals; wrong: copy constructor from this collection kind is not modelled |
| `new LinkedHashSet()` |  |
| `new LinkedHashSet(int)` |  |
| `new LinkedHashSet(Collection)` | throws NullPointerException; calls application equals; wrong: copy constructor from this collection kind is not modelled |
| `new TreeSet()` |  |
| `new TreeSet(int)` |  |
| `new TreeSet(Collection)` | throws NullPointerException; calls application equals; wrong: copy constructor from this collection kind is not modelled |
| `new TreeSet(SortedSet)` | wrong: TreeSet(SortedSet) from this collection kind is not modelled |

| Instance method (`setInst`) | Notes |
|---|---|
| `size()` |  |
| `isEmpty()` |  |
| `contains(Object)` | throws ClassCastException, NullPointerException; calls application equals |
| `add(Object)` | throws NullPointerException; calls application equals |
| `remove(Object)` | throws ClassCastException, NullPointerException; calls application equals |
| `clear()` |  |
| `iterator()` | nondeterministic: hash iteration order |
| `first()` | throws NoSuchElementException |
| `last()` | throws NoSuchElementException |
| `addAll(Collection)` | throws NullPointerException; calls application equals; wrong: addAll from this collection kind is not modelled |

## Iterator, map views (keySet, values, entrySet), Map.Entry

Views are live (`Obj.view`); a map or set iterator takes a snapshot of the key order when it is created, a list iterator reads the list by position. `Iterator.remove` follows the JDK, including IllegalStateException for a second `remove`. An entry or iterator used after a structural change of its source (not through the iterator) is `wrong`.

| Instance method (`viewInst`) | Notes |
|---|---|
| `size()` |  |
| `isEmpty()` |  |
| `iterator()` | nondeterministic: hash iteration order |

| Instance method (`iterInst`) | Notes |
|---|---|
| `hasNext()` |  |
| `next()` | throws NoSuchElementException |
| `remove()` | throws IllegalStateException, UnsupportedOperationException |

| Instance method (`entryInst`) | Notes |
|---|---|
| `getKey()` |  |
| `getValue()` | wrong: map entry used after a structural modification |

## java.math.BigDecimal

An exact decimal `unscaled * 10^-scale` (`Obj.dec`, `Jimple/Decimal.lean`), with the JDK's scale and rounding rules. `new BigDecimal(String)` with non-ASCII text goes `wrong`.

| Constructor | Notes |
|---|---|
| `new BigDecimal(String)` | throws NumberFormatException; wrong: non-ASCII numeric text is not modelled |
| `new BigDecimal(int)` |  |
| `new BigDecimal(long)` |  |
| `new BigDecimal(double)` | throws NumberFormatException |
| `new BigDecimal(BigInteger)` |  |
| `new BigDecimal(BigInteger, int)` |  |

| Static method | Notes |
|---|---|
| `BigDecimal.valueOf(long)` |  |
| `BigDecimal.valueOf(long, int)` |  |

| Static field | Notes |
|---|---|
| `BigDecimal.ZERO` |  |
| `BigDecimal.ONE` |  |
| `BigDecimal.TWO` |  |
| `BigDecimal.TEN` |  |

| Instance method (`decInst`) | Notes |
|---|---|
| `add(BigDecimal)` |  |
| `subtract(BigDecimal)` |  |
| `multiply(BigDecimal)` |  |
| `add(BigDecimal, MathContext)` | throws ArithmeticException; wrong: add(MathContext) with a zero operand is not modelled |
| `subtract(BigDecimal, MathContext)` | throws ArithmeticException; wrong: subtract(MathContext) with a zero operand is not modelled |
| `multiply(BigDecimal, MathContext)` | throws ArithmeticException |
| `divide(BigDecimal)` | throws ArithmeticException |
| `divide(BigDecimal, int, RoundingMode)` | throws ArithmeticException |
| `divide(BigDecimal, int, int)` | throws ArithmeticException |
| `divide(BigDecimal, RoundingMode)` | throws ArithmeticException |
| `divide(BigDecimal, int)` | throws ArithmeticException |
| `divide(BigDecimal, MathContext)` | throws ArithmeticException |
| `divideToIntegralValue(BigDecimal)` | throws ArithmeticException |
| `remainder(BigDecimal)` | throws ArithmeticException |
| `setScale(int, RoundingMode)` | throws ArithmeticException |
| `setScale(int, int)` | throws ArithmeticException |
| `setScale(int)` | throws ArithmeticException |
| `round(MathContext)` | throws ArithmeticException |
| `negate()` |  |
| `abs()` |  |
| `plus()` |  |
| `signum()` |  |
| `scale()` |  |
| `precision()` |  |
| `unscaledValue()` |  |
| `compareTo(BigDecimal)` |  |
| `equals(Object)` |  |
| `hashCode()` |  |
| `max(BigDecimal)` |  |
| `min(BigDecimal)` |  |
| `stripTrailingZeros()` |  |
| `toString()` |  |
| `toPlainString()` |  |
| `intValue()` |  |
| `longValue()` |  |
| `intValueExact()` | throws ArithmeticException |
| `longValueExact()` | throws ArithmeticException |
| `doubleValue()` |  |
| `floatValue()` |  |
| `toBigInteger()` |  |
| `pow(int)` | throws ArithmeticException |
| `movePointLeft(int)` |  |
| `movePointRight(int)` |  |
| `scaleByPowerOfTen(int)` |  |
| `divideAndRemainder(BigDecimal)` | throws ArithmeticException |

## java.math.BigInteger

An unbounded integer (`Obj.bigInt`).

| Constructor | Notes |
|---|---|
| `new BigInteger(String)` | throws NumberFormatException; wrong: non-ASCII numeric text is not modelled |
| `new BigInteger(String, int)` | throws NumberFormatException; wrong: non-ASCII numeric text is not modelled |

| Static method | Notes |
|---|---|
| `BigInteger.valueOf(long)` |  |

| Static field | Notes |
|---|---|
| `BigInteger.ZERO` |  |
| `BigInteger.ONE` |  |
| `BigInteger.TWO` |  |
| `BigInteger.TEN` |  |

| Instance method (`bigIntInst`) | Notes |
|---|---|
| `add(BigInteger)` |  |
| `subtract(BigInteger)` |  |
| `multiply(BigInteger)` |  |
| `divide(BigInteger)` | throws ArithmeticException |
| `remainder(BigInteger)` | throws ArithmeticException |
| `mod(BigInteger)` | throws ArithmeticException |
| `negate()` |  |
| `abs()` |  |
| `signum()` |  |
| `compareTo(BigInteger)` |  |
| `equals(Object)` |  |
| `hashCode()` |  |
| `pow(int)` | throws ArithmeticException |
| `gcd(BigInteger)` |  |
| `max(BigInteger)` |  |
| `min(BigInteger)` |  |
| `toString()` |  |
| `intValue()` |  |
| `longValue()` |  |
| `shiftLeft(int)` | wrong: BigInteger shift by more than 2^20 bits is not modelled |
| `shiftRight(int)` | wrong: BigInteger shift by more than 2^20 bits is not modelled |
| `testBit(int)` | throws ArithmeticException |
| `bitLength()` |  |
| `toString(int)` |  |
| `modPow(BigInteger, BigInteger)` | throws ArithmeticException; wrong: BigInteger.modPow with a negative exponent is not modelled |

## java.math.RoundingMode

| Static method | Notes |
|---|---|
| `RoundingMode.valueOf(int)` | throws IllegalArgumentException |
| `RoundingMode.valueOf(String)` | throws IllegalArgumentException |

| Static field | Notes |
|---|---|
| `RoundingMode.(every constant)` |  |

| Instance method | Notes |
|---|---|
| `ordinal()` |  |
| `name()` |  |
| `toString()` |  |
| `equals(Object)` |  |

## java.math.MathContext

| Constructor | Notes |
|---|---|
| `new MathContext(int)` | throws IllegalArgumentException |
| `new MathContext(int, RoundingMode)` | throws IllegalArgumentException |

| Static field | Notes |
|---|---|
| `MathContext.DECIMAL32` |  |
| `MathContext.DECIMAL64` |  |
| `MathContext.DECIMAL128` |  |
| `MathContext.UNLIMITED` |  |

| Instance method | Notes |
|---|---|
| `getPrecision()` |  |
| `getRoundingMode()` |  |

## Throwable and the library exceptions

Library exceptions are plain objects with the fields `detailMessage` and `cause` of `java.lang.Throwable` (application exception classes inherit them). The classes known to the model are those of `tools/prelude.tsv`. `addSuppressed` does not record (`getSuppressed` has no model); `printStackTrace` prints nothing; `toString` of an exception whose class overrides `getMessage` is `wrong`.

| Constructor | Notes |
|---|---|
| `new AssertionError(Object)` | calls application toString |

| Constructor of a library exception class `E` (also via `super(...)`) | Notes |
|---|---|
| `new E()` |  |
| `new E(String)` |  |
| `new E(String, Throwable)` |  |
| `new E(String, Throwable, boolean, boolean)` |  |
| `new E(Throwable)` |  |

| Instance method (`plainInst`) | Notes |
|---|---|
| `getMessage()` |  |
| `getLocalizedMessage()` |  |
| `getCause()` |  |
| `initCause(Throwable)` | throws IllegalArgumentException, IllegalStateException |
| `printStackTrace()` |  |
| `fillInStackTrace()` |  |
| `addSuppressed(Throwable)` | throws IllegalArgumentException, NullPointerException |

## java.lang.Enum

Enum constants are plain objects with the fields `name` and `ordinal` of `java.lang.Enum`; `values()` and `valueOf(String)` are the compiler-generated application methods (the latter calls `Enum.valueOf`). `hashCode` is the identity hash (nondeterministic).

| Constructor | Notes |
|---|---|
| `new Enum(String, int)` |  |

| Static method | Notes |
|---|---|
| `Enum.valueOf(Class, String)` | throws IllegalArgumentException, NullPointerException; wrong: Enum.valueOf on an enum class that is not initialized is not modelled |

| Instance method (`plainInst`) | Notes |
|---|---|
| `name()` |  |
| `ordinal()` |  |
| `compareTo(Object)` | wrong: Enum.compareTo across enum classes |

## java.lang.Object (any object)

`getClass()` is modelled for every object. `hashCode` (identity) and the hash part of `Object.toString` are nondeterministic (the interpreter uses 0). The rows under "arrays" are the methods of array objects.

| Constructor | Notes |
|---|---|
| `new Object()` |  |

| Instance method (`plainInst`) | Notes |
|---|---|
| `equals(Object)` |  |
| `hashCode()` | nondeterministic: unspecified value |
| `toString()` | calls application toString |
| `getClass()` |  |

| Method of arrays | Notes |
|---|---|
| `clone()` |  |
| `equals(Object)` |  |

## java.lang.Record (Java 16+ records)

Records are application classes extending `java.lang.Record`. Their `toString`, `hashCode` and `equals` are `invokedynamic` call sites of `java.lang.runtime.ObjectMethods.bootstrap` (last section), computed from the component names and getter handles (that is, from the fields, not the accessors): `toString` is `Name[a=1, b=x]` (simple class name, components by `String.valueOf`, application `toString` called back; `float`/`double` components go `wrong`); `hashCode` is `31 * h + hash(c)` over the components from `h = 0` (`Objects.hashCode`, application `hashCode` called back, primitives as `Integer.hashCode` etc.); `equals` is true for the same object, false unless the argument is an instance of the record class, otherwise componentwise from the last component to the first, the order of the JDK's method handle chain (`Objects.equals` with application `equals` called back; primitives by `==`, floating-point by `Float.compare`/`Double.compare`). Jimple has no `InnerClasses` attribute, so the simple name of a nested class whose own name contains `$` comes out shorter.

| Constructor | Notes |
|---|---|
| `new Record()` |  |

## JUnit 5: org.junit.jupiter.api.Assertions (5.10)

Validated against junit-jupiter-api 5.10.2 with opentest4j 1.3.0 (difftest programs `Jup5`, `Jup5Arr`). Modelled: `assertTrue`/`assertFalse(boolean)`, `assertNull`/`assertNotNull(Object)`, `assertSame`/`assertNotSame(Object, Object)`, `assertEquals` and `assertNotEquals` for `byte`, `short`, `char`, `int`, `long`, `float`, `double` (bit patterns for floating-point), the boxed mixes and `Object` (`expected.equals(actual)` with application `equals` called back, lists by their `equals` model; `null` equals only `null`), `assertArrayEquals` for arrays of `boolean`, `char`, `byte`, `short`, `int`, `long`, `float`, `double` and `Object` (nested arrays recursively, elements by `Objects.equals`; messages with the index path, `array lengths differ, expected: <2> but was: <3>`), `assertThrows(Class, Executable)` (calls back `execute()`; returns the exception if it is an instance of the class) and `fail` (no arguments, `String`, `String` and `Throwable`, `Throwable`, `Supplier`); each with an optional last argument `String` or `Supplier<String>` (`get()` called back on failure only). Failures throw `org.opentest4j.AssertionFailedError` with JUnit's message: `msg ==> ` (for a non-blank message) and then `expected: <e> but was: <a>` (values by `toString`, classes by canonical name), `expected: not <null>`, `expected: not same but was: <a>`, `Unexpected exception type thrown, expected: <E> but was: <A>` (the thrown exception as cause) or `Expected E to be thrown, but nothing was thrown.`. When `e` and `a` render alike, JUnit adds class names and identity hash codes (any value in the model); a `toString` that throws is replaced by `Class@hash`, as in JUnit; arrays are rendered by `Arrays.toString`/`Arrays.deepToString`. Not modelled (`wrong`): messages that show `float`/`double` values, the delta overloads, `BooleanSupplier`, `assertIterableEquals`, `assertAll`, `assertDoesNotThrow`, `assertTimeout`, `assertInstanceOf`, `assertThrowsExactly`, `getExpected`/`getActual`.

## JUnit 4: org.junit.Assert (4.13)

Validated against junit 4.13.2 (difftest programs `Ju4`, `Ju4Arr`). Modelled, each with an optional first argument `String message`: `assertTrue`, `assertFalse`, `fail`, `assertNull`, `assertNotNull`, `assertSame`, `assertNotSame`, `assertEquals` and `assertNotEquals` for `long` (also `int` arguments) and `Object` (application `equals` called back, lists by their `equals` model), the deprecated `assertEquals(double, double)` (always fails), `assertArrayEquals` for arrays of `boolean`, `char`, `byte`, `short`, `int`, `long` and `Object` (also the deprecated `assertEquals(Object[], Object[])`: a `deepEquals` pass, then the first difference as `org.junit.internal.ArrayComparisonFailure`, `array lengths differed, expected.length=2 actual.length=3; arrays first differed at element [2]; expected:<end of array> but was:<3>`, whose cause is the element's `AssertionError` or `ComparisonFailure`; an application `equals` compared with the end-of-array marker receives a plain `java.lang.Object`) and `assertThrows(Class, ThrowingRunnable)`. Failures throw `java.lang.AssertionError` (message `null` for `assertTrue`, `assertFalse`, `assertNotNull` and `fail` without a message) with JUnit's messages (`msg expected:<e> but was:<a>`, `expected null, but was:<a>`, `expected same:<e> was not:<a>`, `expected not same`, `unexpected exception type thrown; expected:<E> but was:<A>` with the cause, `expected E to be thrown, but nothing was thrown`); two different `String`s throw `org.junit.ComparisonFailure` with the compacted message (`expected:<ab[c]> but was:<ab[d]>`, common parts beyond 20 characters elided). Not modelled: the delta overloads (also of `assertArrayEquals`), `assertThat`, `ComparisonFailure.getExpected`/`getActual`, arrays in `assertEquals(Object, Object)` messages (JUnit 4 prints identity hashes).

## java.io.PrintStream (System.out, System.err)

| Instance method | Notes |
|---|---|
| `println()` |  |
| `println(T)` | calls application toString; wrong: float/double arguments: floating-point to string conversion is not modelled |
| `print(T)` | calls application toString; wrong: float/double arguments: floating-point to string conversion is not modelled |
| `flush()` |  |
| `printf(String, Object)` | throws NullPointerException |
| `format(String, Object)` | throws NullPointerException |

## java.lang.Class

Class objects come from class constants (`Foo.class`) and `getClass()`; reflection has no model.

| Instance method | Notes |
|---|---|
| `getName()` |  |
| `desiredAssertionStatus()` |  |
| `getSimpleName()` |  |
| `getCanonicalName()` |  |
| `equals(Object)` |  |

## invokedynamic: string concatenation and records

Modelled in `Jimple/Semantics.lean` (`evalDynamic`): `StringConcatFactory.makeConcatWithConstants`
(recipe: `\u0001` takes the next argument, `\u0002` the next bootstrap constant, other characters are
copied) and `makeConcat` (all arguments). Each argument is rendered with `String.valueOf` of its static
type (application `toString` is called; `float`/`double` arguments go `wrong`). For other bootstrap
methods `evalDynamic` asks `Native.dynCall`, which models `java.lang.runtime.ObjectMethods.bootstrap`
(the `toString`, `hashCode` and `equals` of records, see java.lang.Record). Every other
`invokedynamic` goes `wrong`; lambdas compiled with `invokedynamic` are turned into ordinary classes by
Soot (`Name$lambda_...`). Java 8 bytecode (`javac --release 8`) concatenates with `StringBuilder`.
