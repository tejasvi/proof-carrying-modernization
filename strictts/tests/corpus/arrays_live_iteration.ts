// for-of over an array that grows during iteration sees the new elements (live).
const queue: string[] = ["start"];
let steps = 0n;
for (const item of queue) {
  steps++;
  if (item === "start") queue.push("a", "b");
  if (item === "a") queue.push("c");
  console.log(`visit ${item}`);
}
console.log(`steps ${steps}`);
const xs = ["p", "q", "r"];
const seen: string[] = [];
xs.forEach((x) => { seen.push(x); if (x === "p") xs.push("added"); });
console.log(`${seen.join(",")} / ${xs.join(",")}`);
