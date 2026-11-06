// @reject timer-handle
// two Node timer handles are compared by identity; only comparisons with null / undefined are
// supported (Node prints false)
declare namespace NodeJS { interface Timeout { ref(): Timeout; unref(): Timeout; hasRef(): boolean; refresh(): Timeout } }
declare const first: NodeJS.Timeout;
declare const second: NodeJS.Timeout;
console.log(String(first === second));
