export interface User { name: string; age: number }
export function firstAdult(users: User[]): User | undefined {
  return users.find((u) => u.age >= 18);
}
