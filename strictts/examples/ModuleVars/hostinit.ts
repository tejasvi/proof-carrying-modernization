// A module whose initialisation calls the host: `normalize` is answered by the world's oracle
// for external calls. With the default oracle (every external call throws) the initialisation
// never ends normally; `World.ModuleInit` quantifies over the oracles, so that worlds satisfying
// it exist (`HostInitProofs.lean`).

const LIGATURE = "ﬁ".normalize("NFKC");

export function ligatureLength(): number {
  return LIGATURE.length;
}

console.log(`${ligatureLength()}`);
