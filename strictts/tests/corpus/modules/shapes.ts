import { label } from "./util";
export class Square {
  constructor(public side: bigint) {}
  area(): bigint { return this.side * this.side; }
  describe(): string { return label(`square ${this.side}`); }
}
console.log("shapes module body runs");
