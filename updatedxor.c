#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#define TABLE_SIZE 256
#define GOLDEN 0x9E3779B97F4A7C15ULL
#define FNV_OFFSET 14695981039346656037ULL
#define FNV_PRIME 1099511628211ULL
#define MAX_TEXT 10000

uint8_t xor_filter[TABLE_SIZE] = {0};

/* ---------- Hash Utilities ---------- */

static inline uint64_t mix64(uint64_t x) {
    x ^= x >> 30;
    x *= 0xBF58476D1CE4E5B9ULL;
    x ^= x >> 27;
    x *= 0x94D049BB133111EBULL;
    x ^= x >> 31;
    return x;
}

uint64_t fnv1a_64(const uint8_t *data, size_t len) {
    uint64_t h = FNV_OFFSET;
    for (size_t i = 0; i < len; i++) {
        h ^= data[i];
        h *= FNV_PRIME;
    }
    return h;
}

void derive_hashes(uint64_t h, uint32_t *h0, uint32_t *h1, uint32_t *h2, uint8_t *fp) {
    *h0 = mix64(h) % TABLE_SIZE;
    *h1 = mix64(h + GOLDEN) % TABLE_SIZE;
    *h2 = mix64(h + 2 * GOLDEN) % TABLE_SIZE;
    *fp = (uint8_t)mix64(h);
}

/* ---------- XOR Filter ---------- */

void xor_filter_insert(const char *key) {
    uint64_t h = fnv1a_64((uint8_t *)key, strlen(key));
    uint32_t a, b, c;
    uint8_t fp;

    derive_hashes(h, &a, &b, &c, &fp);

    xor_filter[a] ^= fp;
    xor_filter[b] ^= fp;
    xor_filter[c] ^= fp;
}

int xor_filter_maybe_contains(const char *key) {
    uint64_t h = fnv1a_64((uint8_t *)key, strlen(key));
    uint32_t a, b, c;
    uint8_t fp;

    derive_hashes(h, &a, &b, &c, &fp);

    return (xor_filter[a] ^ xor_filter[b] ^ xor_filter[c]) == fp;
}

/* ---------- Rabin–Karp (Exact) ---------- */

int rabin_karp(const char *txt, const char *pat) {
    int n = strlen(txt);
    int m = strlen(pat);

    for (int i = 0; i <= n - m; i++) {
        if (memcmp(txt + i, pat, m) == 0)
            return i;
    }
    return -1;
}

/* ---------- Read file ---------- */

void read_file(const char *filename, char *buffer) {
    FILE *fp = fopen(filename, "r");
    if (!fp) {
        printf("Error opening file\n");
        exit(1);
    }

    size_t len = fread(buffer, 1, MAX_TEXT - 1, fp);
    buffer[len] = '\0';
    fclose(fp);
}

/* ---------- Main ---------- */

int main() {
    char text[MAX_TEXT];
    char pattern[100];

    // Read file
    read_file("input.txt", text);

    // Patterns to index in XOR filter
    const char *patterns[] = {"abc", "def", "xyz"};
    for (int i = 0; i < 3; i++)
        xor_filter_insert(patterns[i]);

    printf("Enter pattern to search: ");
    scanf("%s", pattern);

    if (xor_filter_maybe_contains(pattern)) {
        printf("XOR Filter: maybe present\n");

        int pos = rabin_karp(text, pattern);
        if (pos != -1)
            printf("Rabin–Karp: FOUND at index %d\n", pos);
        else
            printf("Rabin–Karp: false positive\n");
    } else {
        printf("XOR Filter: definitely not present\n");
    }

    return 0;
}
