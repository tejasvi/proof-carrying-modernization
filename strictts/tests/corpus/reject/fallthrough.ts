// @reject switch-fallthrough
function f(n: bigint): string {
  let s = "";
  switch (n) {
    case 1n:
      s += "one";
    case 2n:
      s += "two";
      break;
  }
  return s;
}
console.log(f(1n));
