// @reject top-level-await
const v = await Promise.resolve(1n);
console.log(`${v}`);
export {};
