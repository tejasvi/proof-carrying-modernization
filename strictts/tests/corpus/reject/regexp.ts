// @reject no-regexp
// a replacer function is called with the groups of the pattern, which a regex value does not tell
function upper(s: string, re: RegExp): string { return s.replace(re, (m) => m.toUpperCase()); }
console.log(upper("ab", /a/));
