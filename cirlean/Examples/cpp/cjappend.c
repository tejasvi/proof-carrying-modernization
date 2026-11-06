#include <stdlib.h>
#include <string.h>
/* cJSON 1.7.19: the item record, cJSON_New_Item (malloc for the allocate
   hook) and the list building of parse_array: items appended at the tail,
   prev of the head set to the tail at the end. Each item is a number. */
typedef struct cJSON {
  struct cJSON *next;
  struct cJSON *prev;
  struct cJSON *child;
  int type;
  char *valuestring;
  int valueint;
  double valuedouble;
  char *string;
} cJSON;
#define cJSON_Number (1 << 3)
#define cJSON_Array (1 << 5)

static cJSON *cJSON_New_Item(void) {
  cJSON *node = (cJSON *)malloc(sizeof(cJSON));
  if (node) {
    memset(node, '\0', sizeof(cJSON));
  }
  return node;
}

/* n numbers 0, 1, ..., n-1 as the children of `item` (an array); 0 on an
   allocation failure (the items built so far stay allocated). */
int build_array(cJSON *item, int n) {
  cJSON *head = NULL;
  cJSON *current_item = NULL;
  int i = 0;
  while (i < n) {
    cJSON *new_item = cJSON_New_Item();
    if (new_item == NULL) {
      return 0;
    }
    if (head == NULL) {
      current_item = head = new_item;
    } else {
      current_item->next = new_item;
      new_item->prev = current_item;
      current_item = new_item;
    }
    current_item->type = cJSON_Number;
    current_item->valueint = i;
    i++;
  }
  if (head != NULL) {
    head->prev = current_item;
  }
  item->type = cJSON_Array;
  item->child = head;
  return 1;
}
