export interface Address { city: string; zip?: string }
export interface Person { name: string; address?: Address }
export function cityOf(p: Person): string | undefined {
  if (p.address === undefined) {
    return undefined;
  }
  return p.address.city;
}
