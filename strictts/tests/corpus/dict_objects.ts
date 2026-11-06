// Dictionaries as parameters, results and class fields; entries sorted by value.
interface Score { name: string; points: number }
function tally(scores: Score[]): Record<string, number> {
  const out: Record<string, number> = {};
  for (const s of scores) out[s.name] = (out[s.name] ?? 0) + s.points;
  return out;
}
const t = tally([{ name: "bo", points: 3 }, { name: "al", points: 5 }, { name: "bo", points: 4 }, { name: "7", points: 1 }]);
console.log(Object.entries(t).sort((a, b) => b[1] - a[1]).map(([n, p]) => `${n}:${p}`).join(" "));
class Registry {
  private items: { [id: string]: Score } = {};
  add(id: string, s: Score): boolean {
    if (id in this.items) return false;
    this.items[id] = s;
    return true;
  }
  remove(id: string): void { delete this.items[id]; }
  names(): string { return Object.values(this.items).map((s) => s.name).join(","); }
  get(id: string): Score | undefined { return this.items[id]; }
}
const r = new Registry();
console.log(`${r.add("x", { name: "X", points: 1 })} ${r.add("x", { name: "Y", points: 2 })} ${r.add("1", { name: "One", points: 3 })}`);
r.remove("x");
r.add("x", { name: "X2", points: 4 });
console.log(`${r.names()} ${r.get("1")?.points ?? -1} ${r.get("nope")?.points ?? -1}`);
const same = tally([]);
console.log(`${Object.keys(same).length} ${same === same}`);
