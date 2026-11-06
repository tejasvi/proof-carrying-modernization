// Functions compared by identity (Set elements, Map keys, ===, indexOf): a JavaScript function is
// an object, so subscribing and unsubscribing the same function works, two evaluations of one
// arrow are two functions, and one declared function is one function wherever it is referenced.
const listeners = new Set<() => void>();
const log: string[] = [];
function subscribe(fn: () => void): () => void {
  listeners.add(fn);
  return () => { listeners.delete(fn); };
}
function emit(): void { for (const l of listeners) l(); }
const unsubA = subscribe(() => log.push("a"));
subscribe(() => log.push("b"));
emit();
unsubA();
emit();
console.log(`${log.join(",")} size=${listeners.size}`);
function onTick(): void { log.push("tick"); }
listeners.add(onTick);
listeners.add(onTick);
console.log(`after re-adding the same declared function: ${listeners.size}`);
const make = () => () => { log.push("m"); };
listeners.add(make());
listeners.add(make());
console.log(`two evaluations of one arrow: ${listeners.size}`);
listeners.delete(onTick);
log.length = 0;
emit();
console.log(`${log.join(",")} ${listeners.has(onTick)}`);
