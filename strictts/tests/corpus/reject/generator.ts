// @reject no-generators
function* gen(): Generator<bigint> { yield 1n; }
for (const x of gen()) console.log(`${x}`);
