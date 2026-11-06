// Discriminated unions: narrowing with if, switch and early returns.
type Shape =
  | { kind: "circle"; r: bigint }
  | { kind: "rect"; w: bigint; h: bigint }
  | { kind: "tri"; a: bigint; b: bigint; c: bigint };
function area3(s: Shape): bigint {
  switch (s.kind) {
    case "circle": return 3n * s.r * s.r;
    case "rect": return s.w * s.h;
    case "tri": return 0n;
  }
}
function perimeter(s: Shape): bigint {
  if (s.kind === "circle") return 6n * s.r;
  if (s.kind === "rect") return 2n * (s.w + s.h);
  return s.a + s.b + s.c;
}
function name(s: Shape): string {
  if (s.kind !== "tri") {
    return s.kind === "rect" ? `rect ${s.w}x${s.h}` : `circle ${s.r}`;
  }
  return `tri ${s.a},${s.b},${s.c}`;
}
const shapes: Shape[] = [
  { kind: "circle", r: 2n },
  { kind: "rect", w: 3n, h: 4n },
  { kind: "tri", a: 3n, b: 4n, c: 5n },
];
for (const s of shapes) console.log(`${name(s)}: area~${area3(s)} perimeter~${perimeter(s)}`);
