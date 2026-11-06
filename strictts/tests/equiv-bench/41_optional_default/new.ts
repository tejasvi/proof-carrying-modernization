export function repeatWord(w: string, times: number = 2): string {
  let s = "";
  for (let i = 0; i < times && i < 20; i++) s += w;
  return s;
}
