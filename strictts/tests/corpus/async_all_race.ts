// Promise.all and Promise.race ordering.
async function delayValue(name: string, ticks: bigint): Promise<string> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`${name} resolved`);
  return name;
}
Promise.all([delayValue("x", 3n), delayValue("y", 1n), delayValue("z", 2n)]).then((vs) => console.log(`all: ${vs.join(",")}`));
Promise.race([delayValue("slow", 4n), delayValue("fast", 1n)]).then((v) => console.log(`race: ${v}`));
const none: Promise<bigint>[] = [];
Promise.all(none).then((vs) => console.log(`empty all: ${vs.length === 0}`));
console.log("started");
