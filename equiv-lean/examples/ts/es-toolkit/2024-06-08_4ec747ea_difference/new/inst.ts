// equiv-lean instantiation of es-toolkit's generic `difference` at T = number (the pinned
// StrictTS translator monomorphises generics at their call sites).
import { difference } from "./src/array/difference";

export function differenceNum(firstArr: number[], secondArr: number[]): number[] {
  return difference(firstArr, secondArr);
}
