// equiv-lean instantiation of es-toolkit's generic `intersection` at T = number (the pinned
// StrictTS translator monomorphises generics at their call sites).
import { intersection } from "./src/array/intersection";

export function intersectionNum(firstArr: number[], secondArr: number[]): number[] {
  return intersection(firstArr, secondArr);
}
