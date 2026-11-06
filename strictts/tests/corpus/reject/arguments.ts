// @reject no-arguments
function f(): bigint { return BigInt(arguments.length); }
console.log(`${f()}`);
