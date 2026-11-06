// A state machine: enum states, transition table in a Map keyed by template strings,
// history kept in a class, exhaustive switch with never-returning helper.
type State = "idle" | "running" | "paused" | "stopped";
type Event = "start" | "pause" | "resume" | "stop";
const table = new Map<string, State>([
  ["idle:start", "running"],
  ["running:pause", "paused"],
  ["paused:resume", "running"],
  ["running:stop", "stopped"],
  ["paused:stop", "stopped"],
]);
function fail(msg: string): never { throw new Error(msg); }
function label(s: State): string {
  switch (s) {
    case "idle": return "⏸ idle";
    case "running": return "▶ running";
    case "paused": return "⏯ paused";
    case "stopped": return "⏹ stopped";
  }
}
class Machine {
  state: State = "idle";
  history: State[] = [];
  send(e: Event): boolean {
    const next = table.get(`${this.state}:${e}`);
    if (next === undefined) return false;
    this.history.push(this.state);
    this.state = next;
    return true;
  }
}
const m = new Machine();
const events: Event[] = ["pause", "start", "pause", "start", "resume", "stop", "start"];
for (const e of events) console.log(`${e.padEnd(6)} -> ${m.send(e) ? "ok " : "bad"} ${label(m.state)}`);
console.log(m.history.join(" > "));
try { fail("explicit failure"); } catch (e) { console.log((e as Error).message); }
