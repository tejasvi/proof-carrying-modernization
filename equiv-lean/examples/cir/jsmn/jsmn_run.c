/* Run harness of equiv-lean's jsmn proof (not part of jsmn): one jsmn_parse call from a freshly
 * initialised parser, in jsmn's default configuration (neither JSMN_PARENT_LINKS nor JSMN_STRICT).
 * With JSMN_STATIC, jsmn_init and jsmn_parse have internal linkage, and this caller makes clang
 * emit them. */
#define JSMN_STATIC
#include "jsmn.h"

int jsmn_run(jsmn_parser *parser, const char *js, size_t len, jsmntok_t *tokens,
             unsigned int num_tokens) {
  jsmn_init(parser);
  return jsmn_parse(parser, js, len, tokens, num_tokens);
}
