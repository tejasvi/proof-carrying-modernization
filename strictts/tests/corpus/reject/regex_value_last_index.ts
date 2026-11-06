// @reject no-regexp
// lastIndex, the matching state of a regex, is not modelled
function at(re: RegExp): number { return re.lastIndex; }
console.log(String(at(/x/g)));
