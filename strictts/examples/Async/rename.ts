// Renames a document if it exists: two awaited calls of an external database library.
import { Db, getDoc, setName } from "fakedb";

export async function rename(db: Db, id: string, name: string): Promise<boolean> {
  const doc = await getDoc(db, id);
  if (doc === undefined) return false;
  await setName(db, id, name);
  return true;
}
