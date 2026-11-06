export function repeatWord(w: string, times?: number): string {
  const n = times === undefined ? 2 : times;
  let s = "";
  for (let i = 0; i < n && i < 20; i++) s += w;
  return s;
}
