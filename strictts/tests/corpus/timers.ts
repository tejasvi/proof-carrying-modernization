// setTimeout ordering (Node clamps 0 to 1 ms) interleaved with microtasks.
setTimeout(() => console.log("timeout 200"), 200);
setTimeout(() => {
  console.log("timeout 1 (a)");
  Promise.resolve().then(() => console.log("microtask inside timer a"));
}, 1);
setTimeout(() => console.log("timeout 0 (b), same list as 1"), 0);
setTimeout(() => {
  console.log("timeout 100");
  setTimeout(() => console.log("nested timeout +50 (due 150)"), 50);
}, 100);
Promise.resolve().then(() => console.log("microtask 1"));
queueMicrotask(() => console.log("queueMicrotask"));
console.log("sync");
