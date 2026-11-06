/* Loops over a linked list: a traversal and a loop that frees every node
   (Examples/Lists.lean). */
#include <stdlib.h>
typedef struct node { struct node *next; int val; } node;
int list_len(const node *p) {
  int n = 0;
  while (p != NULL) { n++; p = p->next; }
  return n;
}
void free_list(node *p) {
  node *next = NULL;
  while (p != NULL) { next = p->next; free(p); p = next; }
}
