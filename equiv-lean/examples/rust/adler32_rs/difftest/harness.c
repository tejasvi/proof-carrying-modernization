/* C side of the adler32 differential test: zlib 1.3.1's adler32.c, unmodified, compiled separately
   and linked with this file.
   usage: c_harness CASES      (CASES from gen_cases.py)
   Prints one line per case: "<index> <kind> <result as 16 hex digits>". */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "zlib.h"

/* defined in adler32.c; zlib.h declares it only with Z_LARGE64 or Z_WANT64 (here z_off64_t is
   z_off_t, 64 bits on LP64) */
uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off_t len2);

static unsigned char *data;
static size_t size, pos;

static void need(size_t n) {
    if (n > size - pos) {
        fprintf(stderr, "truncated case file\n");
        exit(2);
    }
}

static uint64_t rd64(void) {
    uint64_t v;
    need(8);
    memcpy(&v, data + pos, 8);
    pos += 8;
    return v;
}

static uint32_t rd32(void) {
    uint32_t v;
    need(4);
    memcpy(&v, data + pos, 4);
    pos += 4;
    return v;
}

static uint8_t rd8(void) {
    need(1);
    return data[pos++];
}

static const Bytef *rdbuf(uint8_t is_null, uint64_t len) {
    const Bytef *b;
    if (is_null)
        return Z_NULL;
    need(len);
    b = data + pos;
    pos += len;
    return b;
}

int main(int argc, char **argv) {
    FILE *f;
    long fsize;
    uint32_t count, i;
    if (argc != 2) {
        fprintf(stderr, "usage: c_harness CASES\n");
        return 2;
    }
    f = fopen(argv[1], "rb");
    if (!f || fseek(f, 0, SEEK_END) != 0 || (fsize = ftell(f)) < 0 || fseek(f, 0, SEEK_SET) != 0) {
        fprintf(stderr, "cannot read %s\n", argv[1]);
        return 2;
    }
    size = (size_t)fsize;
    data = malloc(size ? size : 1);
    if (!data || fread(data, 1, size, f) != size) {
        fprintf(stderr, "cannot read %s\n", argv[1]);
        return 2;
    }
    fclose(f);
    need(4);
    if (memcmp(data, "ADL1", 4) != 0) {
        fprintf(stderr, "bad magic\n");
        return 2;
    }
    pos = 4;
    count = rd32();
    for (i = 0; i < count; i++) {
        uint8_t kind = rd8();
        uLong r;
        if (kind == 0) {
            uint64_t adler = rd64();
            uint8_t is_null = rd8();
            uint64_t len = rd64();
            const Bytef *b = rdbuf(is_null, len);
            r = adler32_z((uLong)adler, b, (z_size_t)len);
        } else if (kind == 1) {
            uint64_t adler = rd64();
            uint8_t is_null = rd8();
            uint32_t len = rd32();
            const Bytef *b = rdbuf(is_null, len);
            r = adler32((uLong)adler, b, (uInt)len);
        } else if (kind == 2 || kind == 3) {
            uint64_t a1 = rd64();
            uint64_t a2 = rd64();
            int64_t l2 = (int64_t)rd64();
            r = kind == 2 ? adler32_combine((uLong)a1, (uLong)a2, (z_off_t)l2)
                          : adler32_combine64((uLong)a1, (uLong)a2, (z_off_t)l2);
        } else {
            fprintf(stderr, "bad kind %u at case %u\n", kind, i);
            return 2;
        }
        printf("%u %u %016lx\n", i, kind, (unsigned long)r);
    }
    if (pos != size) {
        fprintf(stderr, "trailing bytes in case file\n");
        return 2;
    }
    return 0;
}
