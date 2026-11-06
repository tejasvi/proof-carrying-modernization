// @reject timer-handle
// Node's timer handle is an object whose string is its id (Symbol.toPrimitive); the semantics'
// setTimeout gives a number, held in the handle, which must not show (Node prints "timer 1")
declare namespace NodeJS { interface Timeout { ref(): Timeout; unref(): Timeout; hasRef(): boolean; refresh(): Timeout } }
declare const timer: NodeJS.Timeout;
console.log(`timer ${timer}`);
