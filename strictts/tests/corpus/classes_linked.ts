// A mutable linked list (class with a self-referential optional field).
class ListNode {
  next: ListNode | undefined = undefined;
  constructor(public value: string) {}
}
class LinkedList {
  head: ListNode | undefined = undefined;
  tail: ListNode | undefined = undefined;
  size = 0n;
  append(v: string): void {
    const node = new ListNode(v);
    if (this.tail === undefined) {
      this.head = node;
    } else {
      this.tail.next = node;
    }
    this.tail = node;
    this.size++;
  }
  toArray(): string[] {
    const out: string[] = [];
    let cur = this.head;
    while (cur !== undefined) {
      out.push(cur.value);
      cur = cur.next;
    }
    return out;
  }
  reverse(): void {
    let prev: ListNode | undefined = undefined;
    let cur = this.head;
    this.tail = cur;
    while (cur) {
      const nxt: ListNode | undefined = cur.next;
      cur.next = prev;
      prev = cur;
      cur = nxt;
    }
    this.head = prev;
  }
}
const l = new LinkedList();
for (const w of ["one", "two", "three"]) l.append(w);
console.log(`${l.toArray().join(" -> ")} (size ${l.size})`);
l.reverse();
console.log(l.toArray().join(" -> "));
