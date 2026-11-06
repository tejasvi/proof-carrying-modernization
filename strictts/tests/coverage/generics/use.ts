// The use-site monomorphizations of src/lib.ts (a whole-program translation of this file): the
// instances that `--emit-generics number` emits in coverage mode must be the same definitions.
import { chunkBy, firstOr, longest, clampAll } from './src/lib';
const parts = chunkBy<number>([1, 2, 3, 4, 5], 2);
console.log(`${parts.length} ${firstOr<number>([], 7)} ${longest<string>(["a", "bb"]) ?? "-"} ${clampAll<number>([1, 5], 3).join(",")}`);
