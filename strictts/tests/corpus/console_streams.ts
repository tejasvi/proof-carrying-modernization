// @extern
// console.warn and console.error write to standard error, outside the modelled output: externs
// with no result, given their arguments (strings, numbers, objects, arrays); console.info and
// console.debug write to standard output like console.log.
interface Job { id: string; tries: number }
function run(job: Job): string {
  if (job.tries > 2) { console.warn("giving up", job.id, job.tries); return "dropped"; }
  if (job.id === "") { console.error("empty id", { job }); return "invalid"; }
  console.debug(`running ${job.id}`);
  return "ok";
}
const results = [{ id: "a", tries: 0 }, { id: "b", tries: 3 }, { id: "", tries: 1 }].map(run);
console.warn("summary", results, results.length);
console.info(results.join(","));
