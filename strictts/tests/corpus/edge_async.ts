// Async: methods, arrow functions capturing this, await in try/finally inside loops,
// awaiting already-settled promises, then on async results.
class Fetcher {
  calls = 0n;
  constructor(public prefix: string) {}
  async get(key: string): Promise<string> {
    this.calls++;
    await null;
    if (key === "bad") throw new Error(`no ${key}`);
    return `${this.prefix}:${key}`;
  }
  async getAll(keys: string[]): Promise<string[]> {
    const out: string[] = [];
    for (const k of keys) {
      try {
        out.push(await this.get(k));
      } catch (e) {
        out.push(`error(${(e as Error).message})`);
      } finally {
        out.push("|");
      }
    }
    return out;
  }
  later(): Promise<string> {
    return Promise.resolve().then(() => `${this.prefix} later, calls=${this.calls}`);
  }
}
const f = new Fetcher("api");
f.getAll(["a", "bad", "c"]).then((r) => console.log(r.join(" ")));
f.later().then((s) => console.log(s));
const settled = Promise.resolve("ready");
async function useSettled(): Promise<void> {
  console.log("before await settled");
  const v = await settled;
  console.log(`after await settled: ${v}`);
}
useSettled();
console.log("sync end");
