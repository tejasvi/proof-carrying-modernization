// @reject no-regexp
// test on a global regex bound to a name depends on its lastIndex (not modelled)
const re = /a/g;
console.log(String(re.test("aa")) + String(re.test("aa")));
