import java.util.*;

// Dump the JDK's Unicode character properties for the JimpleLean Character models.
// Output lines:
//   R start end type flags          property runs (flags: 1 upper, 2 lower, 4 whitespace, 8 spaceChar,
//                                   16 alphabetic, 32 ideographic)
//   U cp mapped                     Character.toUpperCase(cp) != cp
//   L cp mapped                     Character.toLowerCase(cp) != cp
//   T cp mapped                     Character.toTitleCase(cp) != cp
//   N cp value                      Character.getNumericValue(cp) (≠ -1, cp ≥ 128)
//   D cp value                      Character.digit(cp, 36) for cp ≥ 128 (≠ -1)
//   SU c s1 s2 ...                  String.valueOf(c).toUpperCase() when it is not the char mapping
//   SL c s1 s2 ...                  String.valueOf(c).toLowerCase() likewise
public class UniDump {
    public static void main(String[] a) {
        StringBuilder out = new StringBuilder();
        int runStart = 0; long runKey = key(0);
        for (int cp = 1; cp <= 0x110000; cp++) {
            long k = cp <= 0x10FFFF ? key(cp) : -1;
            if (k != runKey) {
                out.append("R ").append(runStart).append(' ').append(cp - 1).append(' ')
                   .append(runKey >> 8).append(' ').append(runKey & 255).append('\n');
                runStart = cp; runKey = k;
            }
        }
        for (int cp = 0; cp <= 0x10FFFF; cp++) {
            int u = Character.toUpperCase(cp), l = Character.toLowerCase(cp), t = Character.toTitleCase(cp);
            if (u != cp) out.append("U ").append(cp).append(' ').append(u).append('\n');
            if (l != cp) out.append("L ").append(cp).append(' ').append(l).append('\n');
            if (t != cp) out.append("T ").append(cp).append(' ').append(t).append('\n');
            if (cp >= 128) {
                int nv = Character.getNumericValue(cp);
                if (nv != -1) out.append("N ").append(cp).append(' ').append(nv).append('\n');
                int dv = Character.digit(cp, 36);
                if (dv != -1) out.append("D ").append(cp).append(' ').append(dv).append('\n');
            }
        }
        for (int c = 0; c < 0x10000; c++) {
            if (Character.isSurrogate((char) c)) continue;
            String s = String.valueOf((char) c);
            String su = s.toUpperCase(Locale.ROOT), sl = s.toLowerCase(Locale.ROOT);
            if (!su.equals(String.valueOf((char) Character.toUpperCase(c))) || su.length() != 1) {
                out.append("SU ").append(c);
                for (char x : su.toCharArray()) out.append(' ').append((int) x);
                out.append('\n');
            }
            if (!sl.equals(String.valueOf((char) Character.toLowerCase(c))) || sl.length() != 1) {
                out.append("SL ").append(c);
                for (char x : sl.toCharArray()) out.append(' ').append((int) x);
                out.append('\n');
            }
        }
        System.out.print(out);
    }
    static long key(int cp) {
        int f = (Character.isUpperCase(cp) ? 1 : 0) | (Character.isLowerCase(cp) ? 2 : 0)
            | (Character.isWhitespace(cp) ? 4 : 0) | (Character.isSpaceChar(cp) ? 8 : 0)
            | (Character.isAlphabetic(cp) ? 16 : 0) | (Character.isIdeographic(cp) ? 32 : 0);
        return ((long) Character.getType(cp) << 8) | f;
    }
}
