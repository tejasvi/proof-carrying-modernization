export function reversed(s: string): string {
  let r = "";
  for (let i = s.length - 1; i >= 0; i--) {
    r += s.charAt(i);
  }
  return r;
}
