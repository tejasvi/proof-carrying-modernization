export interface User { name: string; age: number }
export function firstAdult(users: User[]): User | undefined {
  for (const u of users) {
    if (u.age >= 18) {
      return u;
    }
  }
  return undefined;
}
