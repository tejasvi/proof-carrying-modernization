// Microtask queue order: queueMicrotask vs promise reactions vs await continuations.
async function f(): Promise<void> {
  console.log("f start");
  await undefined;
  console.log("f after await 1");
  await undefined;
  console.log("f after await 2");
}
queueMicrotask(() => console.log("qm 1"));
f();
Promise.resolve().then(() => console.log("then 1")).then(() => console.log("then 2"));
queueMicrotask(() => {
  console.log("qm 2");
  queueMicrotask(() => console.log("qm nested"));
});
console.log("sync");
