// @reject any-type
// @strict
// In the strict subset the default TReturn of Iterator<T> (any) is represented by undefined: reading
// a done result's value, of type any, is rejected, so no program observes that representation.
function lastValue(it: Iterator<number>): string {
  for (;;) {
    const r = it.next();
    if (r.done) return String(r.value);
  }
}
console.log(lastValue({ next: () => ({ value: undefined, done: true }) }));
