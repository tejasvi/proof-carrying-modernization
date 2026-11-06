export function countDown(n: number): string {
  let out = "";
  for (let i = Math.min(Math.floor(n), 50); i > 0; i--) {
    out += `${i} `;
  }
  return out;
}
