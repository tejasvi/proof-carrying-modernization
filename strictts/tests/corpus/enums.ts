// String-literal unions (enums): switch, comparison, conversion to string, maps keyed by them.
type Dir = "north" | "east" | "south" | "west";
function turnRight(d: Dir): Dir {
  switch (d) {
    case "north": return "east";
    case "east": return "south";
    case "south": return "west";
    case "west": return "north";
  }
}
let d: Dir = "north";
const seen: string[] = [];
for (let i = 0n; i < 5n; i++) {
  seen.push(d);
  d = turnRight(d);
}
console.log(seen.join(" "));
const opposite = new Map<Dir, Dir>([["north", "south"], ["east", "west"]]);
console.log(`opposite of north: ${opposite.get("north") ?? "?"}`);
function isVertical(x: Dir): boolean { return x === "north" || x === "south"; }
console.log(`${isVertical("north")} ${isVertical("west")}`);
type Level = "low" | "high";
const lv: Level = "high";
const msg: string = lv;
console.log(`${msg} ${msg.length === 4} ${lv < "low"}`);
