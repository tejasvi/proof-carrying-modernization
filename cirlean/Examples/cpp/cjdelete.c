#include <stdlib.h>
/* cJSON 1.7.19: the item record and cJSON_Delete (cJSON.c), with free for the
   global_hooks.deallocate call; Examples/CJDelete.lean */
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
#define cJSON_IsReference 256
#define cJSON_StringIsConst 512
void cJSON_Delete(cJSON *item) {
  cJSON *next = NULL;
  while (item != NULL) {
    next = item->next;
    if (!(item->type & cJSON_IsReference) && (item->child != NULL)) cJSON_Delete(item->child);
    if (!(item->type & cJSON_IsReference) && (item->valuestring != NULL)) free(item->valuestring);
    if (!(item->type & cJSON_StringIsConst) && (item->string != NULL)) free(item->string);
    free(item);
    item = next;
  }
}
