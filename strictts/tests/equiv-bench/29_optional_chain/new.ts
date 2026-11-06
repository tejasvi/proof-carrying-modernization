export interface Address { city: string; zip?: string }
export interface Person { name: string; address?: Address }
export function cityOf(p: Person): string | undefined {
  return p.address?.city;
}
