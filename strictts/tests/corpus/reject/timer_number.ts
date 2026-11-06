// @reject timer-handle
// unary plus converts Node's timer handle to its id (Symbol.toPrimitive)
declare namespace NodeJS { interface Timeout { ref(): Timeout; unref(): Timeout; hasRef(): boolean; refresh(): Timeout } }
declare const timer: NodeJS.Timeout;
console.log(String(+timer));
