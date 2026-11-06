// switch on strings: grouped cases, default in the middle, return inside switch.
function classify(s: string): string {
  switch (s) {
    case "a":
    case "e":
    case "i":
      return "vowel";
    default:
      return "other";
    case "y":
      return "sometimes";
  }
}
for (const c of ["a", "b", "y", "i", "z"]) console.log(`${c}: ${classify(c)}`);
function describe(n: bigint): string {
  let out = "";
  switch (n) {
    case 1n:
      out = "one";
      break;
    case 2n: {
      const t = "two";
      out = t;
      break;
    }
    case 3n:
      out = "three";
      if (n > 2n) break;
      out = "never";
      break;
    default:
      out = "many";
  }
  return out;
}
for (const n of [1n, 2n, 3n, 4n]) console.log(describe(n));
