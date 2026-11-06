// Static fields and methods, instance counters.
class Id {
  static next = 1n;
  static prefix = "id";
  readonly value: string;
  constructor() {
    this.value = `${Id.prefix}${Id.next}`;
    Id.next++;
  }
  static reset(to: bigint): void { Id.next = to; }
}
const a = new Id();
const b = new Id();
Id.reset(10n);
const c = new Id();
Id.prefix = "x";
const d = new Id();
console.log([a.value, b.value, c.value, d.value].join(","));
console.log(`next=${Id.next}`);
