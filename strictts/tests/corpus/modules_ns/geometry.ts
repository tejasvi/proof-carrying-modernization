export const ORIGIN_NAME = "origin";
export interface Pt { x: bigint; y: bigint }
export function add(a: Pt, b: Pt): Pt { return { x: a.x + b.x, y: a.y + b.y }; }
export function show(p: Pt): string { return `(${p.x}, ${p.y})`; }
export class Path {
  points: Pt[] = [];
  push(p: Pt): Path { this.points.push(p); return this; }
  describe(): string { return this.points.map(show).join(" -> "); }
}
