// A rejected promise without a handler: Node (and the semantics) report it and end the run
// after the microtask queue drains, so the timer never fires.
Promise.reject(new Error("nobody handles this"));
setTimeout(() => console.log("timer still runs"), 10);
console.log("sync");
