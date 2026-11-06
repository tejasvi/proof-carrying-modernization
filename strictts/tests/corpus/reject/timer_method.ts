// @reject timer-handle
// the methods of Node's timer handle (unref keeps the process from waiting for it) are not modelled
declare namespace NodeJS { interface Timeout { ref(): Timeout; unref(): Timeout; hasRef(): boolean; refresh(): Timeout } }
declare const timer: NodeJS.Timeout;
timer.unref();
console.log("unref");
