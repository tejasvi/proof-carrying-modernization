// Host environment of StrictTS programs (used when a program does not bring @types/node or
// the DOM library). Only what the semantics models is declared.
interface Console {
  /** Print one string and a newline (only strings are printed by StrictTS programs). */
  log(message?: string): void;
  /** The same as `log` (standard output). */
  info(message?: string): void;
  debug(message?: string): void;
  /** Write to standard error, outside the modelled output (external calls). */
  warn(...data: unknown[]): void;
  error(...data: unknown[]): void;
}
declare var console: Console;
/** Node clamps the delay to [1, 2^31 - 1] (anything else, including 0, becomes 1). */
declare function setTimeout(callback: () => void, ms?: number): void;
declare function queueMicrotask(callback: () => void): void;
