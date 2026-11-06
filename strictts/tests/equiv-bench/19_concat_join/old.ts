export function csv(cells: string[]): string {
  let s = "";
  for (let i = 0; i < cells.length; i++) {
    if (i > 0) s += ",";
    s += cells[i];
  }
  return s;
}
