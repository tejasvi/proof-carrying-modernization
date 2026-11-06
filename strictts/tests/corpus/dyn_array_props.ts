// @panic read of an inherited Array.prototype property
// Keys of an array or tuple held as an unknown. A read gives the element at an array index
// ("0", "1"; not "01", "-1", "1.5" or "4294967295", which are not indices), the length at
// "length", and undefined at any other key the array does not inherit. `in` is true for its
// indices and "length", for the keys it inherits from Array.prototype ("push", "map",
// "constructor") and Object.prototype ("hasOwnProperty", "__proto__"), false otherwise. Reading an
// inherited key stops the program (the last line, where Node prints "function"): methods are not
// values of the model.
function get(x: unknown, k: string): unknown { return (x as any)[k]; }
function has(x: unknown, k: string): boolean { return k in (x as object); }
const a: unknown = [1, "b"];
const pair: [number, string] = [2, "c"];
const t: unknown = pair;
const keys = ["0", "1", "2", "01", "-1", "1.5", "4294967295", "", "t", "NaN"];
console.log(keys.map((k) => String(get(a, k))).join(" ") + ` ${String(get(a, "length"))}`);
console.log(keys.map((k) => String(get(t, k))).join(" ") + ` ${String(get(t, "length"))}`);
const inKeys = ["0", "1", "2", "length", "push", "map", "constructor", "hasOwnProperty", "__proto__", "toString", "t", "01", "-1"];
console.log(inKeys.map((k) => `${k}:${has(a, k)}`).join(" "));
console.log(inKeys.map((k) => `${k}:${has(t, k)}`).join(" "));
console.log(typeof get(a, "push"));
