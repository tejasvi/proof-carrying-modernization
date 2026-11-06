export function clean(s: string): string {
  let a = 0;
  let b = s.length;
  while (a < b && s.charAt(a) === " ") a++;
  while (b > a && s.charAt(b - 1) === " ") b--;
  return s.substring(a, b);
}
