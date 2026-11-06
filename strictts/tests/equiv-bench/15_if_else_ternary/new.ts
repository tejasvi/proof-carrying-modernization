export function label(score: number): string {
  return score >= 90 ? "A" : score >= 75 ? "B" : "C";
}
