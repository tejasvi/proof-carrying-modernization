// An external tokenizer that returns a fresh array: the program can read it like its own.
import { splitWords } from "fakestr";

export function countWords(s: string): number {
  const parts = splitWords(s);
  return parts.length;
}

export function firstWord(s: string): string {
  const parts = splitWords(s);
  return parts[0];
}
