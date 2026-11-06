// @reject timer-handle
// a Node timer handle as an unknown value would show the semantics' number where Node has an
// object (String(x), property reads)
declare namespace NodeJS { interface Timeout { ref(): Timeout; unref(): Timeout; hasRef(): boolean; refresh(): Timeout } }
declare const timer: NodeJS.Timeout;
const anything: unknown = timer;
console.log(String(anything));
