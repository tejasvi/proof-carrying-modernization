// A `let` without initialiser that a closure reads and the code assigns later (a box that
// holds undefined until the first assignment).
function makeTimerLike(): { fire: () => string; set: (s: string) => void } {
  let label: string;
  const fire = (): string => `fired ${label}`;
  const set = (s: string): void => { label = s; };
  return { fire, set };
}
const t = makeTimerLike();
t.set("first");
console.log(t.fire());
t.set("second");
console.log(t.fire());
function counter(): () => bigint {
  let n: bigint;
  n = 10n;
  function next(): bigint { n += 1n; return n; }
  return next;
}
const c = counter();
c();
console.log(`${c()}`);
