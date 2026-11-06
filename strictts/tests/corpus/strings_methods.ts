// @numbers
// String methods (UTF-16 semantics) with JavaScript's argument defaults.
const s = "Hello, World";
console.log(`${s.length} ${s.charAt(4)} ${s.charCodeAt(0)} ${s.indexOf("o")} ${s.indexOf("o", 5)} ${s.lastIndexOf("o")} ${s.indexOf("z")}`);
console.log(`[${s.slice(7)}] [${s.slice(-5, -1)}] [${s.substring(5, 0)}] [${s.slice(3, 1)}]`);
console.log(`${s.includes("World")} ${s.startsWith("Hell")} ${s.endsWith("World")} ${s.startsWith("World", 7)} ${s.endsWith("Hello", 5)}`);
console.log(`[${"  pad ".trim()}] [${"  pad ".trimStart()}] [${"  pad ".trimEnd()}]`);
console.log(`[${"7".padStart(3, "0")}] [${"ab".padEnd(5, "xy")}] [${"x".padStart(3)}] [${"ab".repeat(3)}]`);
console.log(`${"a-b-c".replace("-", "+")} ${"a-b-c".replaceAll("-", "+")} ${"MiXeD".toUpperCase()} ${"MiXeD".toLowerCase()}`);
console.log(`${"a,b,,c".split(",").join("|")} ${"abc".split("").join(".")} ${"".split(",").length} ${"".split("").length}`);
const emoji = "a😀b";
console.log(`${emoji.length} ${emoji.codePointAt(1) ?? -1} ${emoji.at(-1) ?? "?"} ${[...emoji].length}`);
console.log(`${String.fromCharCode(72, 105)} ${"abc".localeCompare("abd")} ${"b" > "a"}`);
console.log(`${"x".concat("y", "z")} ${s.at(0) ?? ""} ${"abc".at(5) === undefined}`);
