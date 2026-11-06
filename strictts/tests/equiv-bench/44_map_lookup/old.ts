export function weight(size: string): number {
  if (size === "s") return 1;
  if (size === "m") return 2;
  if (size === "l") return 4;
  return 0;
}
