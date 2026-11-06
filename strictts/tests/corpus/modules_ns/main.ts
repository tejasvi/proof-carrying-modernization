// Namespace imports (import * as g), `as const` objects used as enums, async callbacks
// passed where void functions are expected.
import * as g from "./geometry";
const Color = { Red: "red", Green: "green", Blue: "blue" } as const;
type Color = (typeof Color)[keyof typeof Color];
function paint(c: Color): string {
  switch (c) {
    case "red": return "R";
    case "green": return "G";
    case "blue": return "B";
  }
}
const p = g.add({ x: 1n, y: 2n }, { x: 10n, y: 20n });
console.log(`${g.ORIGIN_NAME} ${g.show(p)}`);
const path = new g.Path().push(p).push({ x: 0n, y: 0n });
console.log(path.describe());
console.log([Color.Red, Color.Blue, Color.Green].map(paint).join(""));
const log: string[] = [];
["a", "b"].forEach(async (s) => {
  await null;
  log.push(s);
});
Promise.resolve().then(() => Promise.resolve()).then(() => console.log(`async callbacks ran: ${log.join(",")}`));
