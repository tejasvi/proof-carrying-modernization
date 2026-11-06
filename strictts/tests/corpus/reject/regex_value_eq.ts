// @reject no-regexp
// regular expressions are objects compared by identity; regex values have none (Node prints true)
const a = /x/;
const b = a;
console.log(String(a === b));
