// Block scoping and shadowing of let/const in nested blocks, loops and closures.
const x = "outer";
let y = 1n;
{
  const x = "block";
  let y = 100n;
  y++;
  console.log(`${x} ${y}`);
}
console.log(`${x} ${y}`);
for (const x of ["loop1", "loop2"]) {
  const y = x + "!";
  console.log(y);
}
function f(x: string): string {
  const g = () => x + "-g";
  {
    const x = "inner";
    return `${g()} ${x}`;
  }
}
console.log(f("param"));
if (y === 1n) {
  let y = "shadow in if";
  y += "!";
  console.log(y);
}
console.log(`${y}`);
