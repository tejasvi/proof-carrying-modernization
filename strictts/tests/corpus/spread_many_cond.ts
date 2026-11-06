// Many conditional spreads, each of a record with one field: every field of the result comes
// from the one spread that can have it. (A case split on every spread for every field made the
// value grow as 2^spreads; the Lean compiler ran out of heartbeats on such definitions.)
interface Row { uid?: string; a?: string; b?: string; c?: string; d?: string; e?: string; f?: string; g?: string; h?: string; n?: number; on?: boolean }
interface Card { uid: string; a?: string; b?: string; c?: string; d?: string; e?: string; f?: string; g?: string; h?: string; n?: number; on?: boolean }
function card(r: Row & { uid: string }): Card {
  return {
    uid: r.uid,
    ...(r.a ? { a: r.a } : {}),
    ...(r.b ? { b: r.b } : {}),
    ...(r.c ? { c: r.c } : {}),
    ...(r.d ? { d: r.d } : {}),
    ...(r.e ? { e: r.e } : {}),
    ...(r.f ? { f: r.f } : {}),
    ...(r.g ? { g: r.g } : {}),
    ...(r.h ? { h: r.h } : {}),
    ...(typeof r.n === "number" ? { n: r.n } : {}),
    ...(r.on ? { on: true } : {}),
  };
}
const rows: Row[] = [{ uid: "x", a: "1", c: "3", h: "8", n: 0 }, { uid: "y", b: "2", f: "6", on: true }, { a: "lost" }];
const cards = rows.filter((r): r is Row & { uid: string } => !!r.uid).map(card);
console.log(cards.map((c) => `${c.uid}:${c.a ?? "-"}${c.b ?? "-"}${c.c ?? "-"}${c.d ?? "-"}${c.e ?? "-"}${c.f ?? "-"}${c.g ?? "-"}${c.h ?? "-"}${c.n ?? "-"}${c.on ?? "-"}`).join(" "));
