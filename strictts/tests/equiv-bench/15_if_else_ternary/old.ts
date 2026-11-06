export function label(score: number): string {
  let l: string;
  if (score >= 90) {
    l = "A";
  } else if (score >= 75) {
    l = "B";
  } else {
    l = "C";
  }
  return l;
}
