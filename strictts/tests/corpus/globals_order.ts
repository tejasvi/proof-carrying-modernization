// Module-level variables read and written by functions; initialisation order.
let count = 0n;
const names: string[] = [];
function register(n: string): bigint {
  names.push(n);
  count++;
  return count;
}
register("first");
const second = register("second");
console.log(`${count} ${second} ${names.join(",")}`);
function readLater(): string { return later; }
const later = "initialised later";
console.log(readLater());
function useBeforeInit(): string {
  try { return notYet; } catch (e) { return `caught ${(e as Error).name}`; }
}
console.log(useBeforeInit());
const notYet = "now set";
console.log(useBeforeInit());
