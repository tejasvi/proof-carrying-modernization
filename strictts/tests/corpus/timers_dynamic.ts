// @numbers
// Timers with computed delays (clamped like Node) and timers scheduled from promises.
// delays are far apart: Node measures real time, so timers created later (here: from a
// promise job, after the synchronous code) must not be due within a few ms of earlier ones
const delays = [300, 0, 100, -5, 200];
delays.forEach((d, i) => setTimeout(() => console.log(`timer ${i} (delay ${d})`), d));
Promise.resolve().then(() => setTimeout(() => console.log("from promise (1ms)"), 1));
let ticks = 0;
function tick(): void {
  ticks++;
  console.log(`tick ${ticks}`);
  if (ticks < 3) setTimeout(tick, 400);
}
setTimeout(tick, 400);
console.log("scheduled");
