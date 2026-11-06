// An async arrow called at once, its promise discarded (as an expression statement and under
// `void`): the translation gives the lambda's result type, which Lean cannot infer there.
let state = "idle";
const log: string[] = [];
function start(): void {
  state = "loading";
  (async () => {
    try {
      await Promise.resolve();
      state = "done";
    } finally {
      log.push(`finally ${state}`);
    }
  })();
  void (async () => { log.push("second"); })();
}
start();
log.push(`sync ${state}`);
setTimeout(() => { console.log(`${log.join(", ")}; ${state}`); }, 0);
