// Returning a promise from an async function takes extra ticks (resolve with a thenable).
async function direct(): Promise<string> { return "direct"; }
async function viaPromise(): Promise<string> { return Promise.resolve("viaPromise"); }
async function viaAwait(): Promise<string> { return await Promise.resolve("viaAwait"); }
viaPromise().then((v) => console.log(v));
viaAwait().then((v) => console.log(v));
direct().then((v) => console.log(v));
Promise.resolve().then(() => console.log("tick 1")).then(() => console.log("tick 2")).then(() => console.log("tick 3")).then(() => console.log("tick 4"));
const arrow = async (): Promise<string> => Promise.resolve("arrow");
arrow().then((v) => console.log(v));
