/* The scan for the closing quote in cJSON's parse_string (cJSON.c, 1.7.19),
   as a function of its own: the loop and the checks around it are copied
   unchanged; the allocation and the copy loop that follow in parse_string
   are left out, and the allocation length is returned instead
   (Examples/CJStrings.lean, `string_scan_spec`). */
#include <stddef.h>

#define CJSON_CDECL

typedef struct internal_hooks
{
    void *(CJSON_CDECL *allocate)(size_t size);
    void (CJSON_CDECL *deallocate)(void *pointer);
    void *(CJSON_CDECL *reallocate)(void *pointer, size_t size);
} internal_hooks;

typedef struct
{
    const unsigned char *content;
    size_t length;
    size_t offset;
    size_t depth; /* How deeply nested (in arrays/objects) is the input at the current offset. */
    internal_hooks hooks;
} parse_buffer;

/* get a pointer to the buffer at the position */
#define buffer_at_offset(buffer) ((buffer)->content + (buffer)->offset)

/* returns the length of the unescaped string (an overestimate) after the opening quote, 0 if it is not terminated */
size_t string_scan(parse_buffer * const input_buffer)
{
    const unsigned char *input_end = buffer_at_offset(input_buffer) + 1;
    size_t allocation_length = 0;
    size_t skipped_bytes = 0;

    /* not a string */
    if (buffer_at_offset(input_buffer)[0] != '\"')
    {
        goto fail;
    }

    {
        /* calculate approximate size of the output (overestimate) */
        while (((size_t)(input_end - input_buffer->content) < input_buffer->length) && (*input_end != '\"'))
        {
            /* is escape sequence */
            if (input_end[0] == '\\')
            {
                if ((size_t)(input_end + 1 - input_buffer->content) >= input_buffer->length)
                {
                    /* prevent buffer overflow when last input character is a backslash */
                    goto fail;
                }
                skipped_bytes++;
                input_end++;
            }
            input_end++;
        }
        if (((size_t)(input_end - input_buffer->content) >= input_buffer->length) || (*input_end != '\"'))
        {
            goto fail; /* string ended unexpectedly */
        }

        /* This is at most how much we need for the output */
        allocation_length = (size_t) (input_end - buffer_at_offset(input_buffer)) - skipped_bytes;
    }

    return allocation_length;

fail:
    return 0;
}
