// xor_rk.c
// Compile: gcc -std=c99 -O2 xor_rk.c -o xor_rk
// Usage: ./xor_rk
// Expects input.txt in working directory (or modify filename in main).

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>
#include <ctype.h>
#include <math.h>

/* ----------------------- Config / typedefs ----------------------- */

typedef uint8_t  byte;
typedef uint64_t u64;
typedef uint32_t u32;

#define FNV_OFFSET 14695981039346656037ULL
#define FNV_PRIME 1099511628211ULL
#define GOLDEN 0x9E3779B97F4A7C15ULL

// Simple XOR filter (8-bit fingerprints)
typedef struct {
    u32 capacity;    // number of buckets (≈1.23 * nkeys)
    byte *finger;    // fingerprint array (capacity bytes)
} xor8_t;

/* ----------------------- Utilities ----------------------- */

static void *xmalloc(size_t n) {
    void *p = malloc(n);
    if (!p) { fprintf(stderr, "malloc failed\n"); exit(1); }
    return p;
}

char *read_text_file(const char *fn, size_t *out_len) {
    FILE *f = fopen(fn, "rb");
    if (!f) { perror(fn); exit(1); }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    if (sz < 0) { perror("ftell"); exit(1); }
    rewind(f);
    char *buf = xmalloc((size_t)sz + 1);
    size_t r = fread(buf, 1, (size_t)sz, f);
    buf[r] = '\0';
    fclose(f);
    if (out_len) *out_len = r;
    return buf;
}

void to_lowercase(char *s) {
    for (; *s; ++s) *s = (char)tolower((unsigned char)*s);
}

/* ----------------------- Hashing ----------------------- */

// 64-bit FNV-1a
u64 fnv1a_64(const byte *data, size_t len) {
    u64 h = FNV_OFFSET;
    for (size_t i = 0; i < len; ++i) {
        h ^= (u64)data[i];
        h *= FNV_PRIME;
    }
    return h;
}

// SplitMix-like mix for deriving independent hashes
static inline u64 mix64(u64 x) {
    x ^= x >> 30;
    x *= 0xBF58476D1CE4E5B9ULL;
    x ^= x >> 27;
    x *= 0x94D049BB133111EBULL;
    x ^= x >> 31;
    return x;
}

// From one 64-bit hash produce 3 indices and 8-bit fingerprint
void derive_hashes(u64 h, u32 *o0, u32 *o1, u32 *o2, byte *fp, u32 capacity) {
    u64 a = mix64(h);
    u64 b = mix64(h + GOLDEN);
    u64 c = mix64(h + 2 * GOLDEN);
    *o0 = (u32)(a % capacity);
    *o1 = (u32)(b % capacity);
    *o2 = (u32)(c % capacity);
    *fp = (byte)(mix64(h) & 0xFF);
}

/* ----------------------- Rabin–Karp (64-bit rolling) ----------------------- */

// Rolling hash using 64-bit wrap-around (fast, acceptable for verification)
u64 rk_hash(const byte *s, size_t m, u64 base) {
    u64 h = 0;
    for (size_t i = 0; i < m; ++i) h = h * base + (u64)s[i];
    return h;
}

// Find first occurrence of pattern in text using rolling RK + memcmp verify.
// Returns index >=0 or -1 if not found.
int rabin_karp_search(const char *text, size_t n, const char *pat, size_t m) {
    if (m == 0 || n < m) return -1;
    const u64 base = 911382323; // odd base
    u64 pat_h = rk_hash((const byte*)pat, m, base);
    u64 pow_m = 1;
    for (size_t i = 0; i < m - 1; ++i) pow_m *= base;

    u64 window = rk_hash((const byte*)text, m, base);
    if (window == pat_h && memcmp(text, pat, m) == 0) return 0;
    for (size_t i = 1; i + m <= n; ++i) {
        // remove text[i-1], add text[i+m-1]
        window = window - (u64)text[i-1] * pow_m;
        window = window * base + (u64)text[i + m - 1];
        if (window == pat_h) {
            if (memcmp(text + i, pat, m) == 0) return (int)i;
        }
    }
    return -1;
}

/* ----------------------- XOR filter: simplified implementation ----------------------- */

/*
 Build strategy:
 - capacity = ceil(1.23 * nkeys) + safety
 - For each key we already have its 3 bucket indices and fp (we compute from hashes)
 - Build degree[] and per-bucket list of keys (two-pass: count then fill)
 - Peel: find buckets with degree==1, pop them, record (key, assigned_bucket)
 - If all keys peeled, reverse-assign fingerprint bytes to buckets
 - contains() checks fp == F[i0]^F[i1]^F[i2]
*/

typedef struct {
    u32 i0, i1, i2;
    byte fp;
} keyinfo_t;

void xor8_init(xor8_t *xf, u32 capacity) {
    xf->capacity = capacity;
    xf->finger = xmalloc((size_t)capacity);
    memset(xf->finger, 0, capacity);
}
void xor8_free(xor8_t *xf) { free(xf->finger); xf->finger = NULL; xf->capacity = 0; }

// Helper to compute capacity from nkeys (returns at least 3)
u32 xor8_capacity_for_n(u32 nkeys) {
    // 1.23 is empirical; add small padding
    u32 cap = (u32)ceil(1.5 * (double)nkeys) + 16; // earlier: 1.23, 3
    if (cap < 3) cap = 3;
    return cap;
}

// Build XOR filter from keys[] array (already hashed u64 keys representing substrings).
// Returns 1 on success, 0 on failure (peeling failed).
int xor8_populate_from_keys(xor8_t *xf, const u64 *keys, u32 nkeys) {
    if (nkeys == 0) return 1;
    u32 capacity = xor8_capacity_for_n(nkeys);
    xor8_init(xf, capacity);

    // Prepare keyinfo
    keyinfo_t *kinfo = xmalloc((size_t)nkeys * sizeof(keyinfo_t));
    for (u32 i = 0; i < nkeys; ++i) {
        derive_hashes(keys[i], &kinfo[i].i0, &kinfo[i].i1, &kinfo[i].i2, &kinfo[i].fp, capacity);
    }

    // Degree counting & bucket list sizes
    u32 *degree = xmalloc((size_t)capacity * sizeof(u32));
    memset(degree, 0, capacity * sizeof(u32));
    u32 *bucket_counts = xmalloc((size_t)capacity * sizeof(u32));
    memset(bucket_counts, 0, capacity * sizeof(u32));
    for (u32 i = 0; i < nkeys; ++i) {
        bucket_counts[kinfo[i].i0]++;
        bucket_counts[kinfo[i].i1]++;
        bucket_counts[kinfo[i].i2]++;
    }
    // allocate per-bucket lists (flattened arrays)
    u32 **bucket_lists = xmalloc((size_t)capacity * sizeof(u32*));
    for (u32 b = 0; b < capacity; ++b) {
        if (bucket_counts[b] == 0) bucket_lists[b] = NULL;
        else bucket_lists[b] = xmalloc(bucket_counts[b] * sizeof(u32));
        degree[b] = 0; // will refill as we add
    }
    // fill lists
    // temp fill positions
    u32 *fill_pos = xmalloc((size_t)capacity * sizeof(u32));
    memset(fill_pos, 0, capacity * sizeof(u32));
    for (u32 i = 0; i < nkeys; ++i) {
        u32 b0 = kinfo[i].i0, b1 = kinfo[i].i1, b2 = kinfo[i].i2;
        bucket_lists[b0][fill_pos[b0]++] = i;
        bucket_lists[b1][fill_pos[b1]++] = i;
        bucket_lists[b2][fill_pos[b2]++] = i;
        degree[b0]++; degree[b1]++; degree[b2]++;
    }
    free(fill_pos);

    // peel structures
    u32 *bucket_stack = xmalloc((size_t)capacity * sizeof(u32));
    u32 stack_top = 0;
    for (u32 b = 0; b < capacity; ++b) if (degree[b] == 1) bucket_stack[stack_top++] = b;

    // track if key is removed
    byte *key_removed = xmalloc((size_t)nkeys);
    memset(key_removed, 0, nkeys);
    // record peel order: pair (key index, assigned bucket)
    u32 *peel_key = xmalloc((size_t)nkeys * sizeof(u32));
    u32 *peel_bucket = xmalloc((size_t)nkeys * sizeof(u32));
    u32 peel_top = 0;

    // Peeling loop
    while (stack_top > 0) {
        u32 b = bucket_stack[--stack_top];
        if (degree[b] != 1) continue; // stale
        // find the single remaining key in bucket_lists[b] that's not removed
        u32 found_key = UINT32_MAX;
        u32 cnt = bucket_counts[b];
        for (u32 j = 0; j < cnt; ++j) {
            u32 k = bucket_lists[b][j];
            if (!key_removed[k]) { found_key = k; break; }
        }
        if (found_key == UINT32_MAX) continue; // nothing
        // remove key
        key_removed[found_key] = 1;
        peel_key[peel_top] = found_key;
        peel_bucket[peel_top] = b;
        peel_top++;

        // decrement degrees of other buckets for this key
        u32 b0 = kinfo[found_key].i0;
        u32 b1 = kinfo[found_key].i1;
        u32 b2 = kinfo[found_key].i2;
        u32 others[2]; int idx = 0;
        if (b0 != b) others[idx++] = b0;
        if (b1 != b) others[idx++] = b1;
        if (b2 != b) others[idx++] = b2;
        for (int t = 0; t < idx; ++t) {
            u32 ob = others[t];
            if (degree[ob] > 0) {
                degree[ob]--;
                if (degree[ob] == 1) bucket_stack[stack_top++] = ob;
            }
        }
    }

    int success = 1;
    if (peel_top != nkeys) {
        // failed to peel all keys
        success = 0;
    } else {
        // reverse assign fingerprints
        // F[] currently zeroed
        for (int p = (int)peel_top - 1; p >= 0; --p) {
            u32 kidx = peel_key[p];
            u32 assign_bucket = peel_bucket[p];
            u32 i0 = kinfo[kidx].i0;
            u32 i1 = kinfo[kidx].i1;
            u32 i2 = kinfo[kidx].i2;
            byte fp = kinfo[kidx].fp;
            // other two buckets
            byte v0 = xf->finger[i0];
            byte v1 = xf->finger[i1];
            byte v2 = xf->finger[i2];
            // compute value for assign_bucket so that xor of three equals fp
            byte other_xor = 0;
            if (assign_bucket == i0) other_xor = v1 ^ v2;
            else if (assign_bucket == i1) other_xor = v0 ^ v2;
            else other_xor = v0 ^ v1;
            xf->finger[assign_bucket] = fp ^ other_xor;
        }
    }

    // cleanup
    for (u32 b = 0; b < capacity; ++b) if (bucket_lists[b]) free(bucket_lists[b]);
    free(bucket_lists);
    free(bucket_counts);
    free(degree);
    free(bucket_stack);
    free(key_removed);
    free(peel_key);
    free(peel_bucket);
    free(kinfo);

    if (!success) {
        xor8_free(xf);
        return 0;
    }
    return 1;
}

// Helper: try populate with a few retries increasing capacity if needed
int xor8_build_with_retries(xor8_t *xf, const u64 *keys, u32 nkeys) {
    const int max_attempts = 5;
    for (int attempt = 0; attempt < max_attempts; ++attempt) {
        if (xor8_populate_from_keys(xf, keys, nkeys)) return 1;
        // else increase capacity factor slightly by realloc strategy inside populate requires change;
        // for simplicity, we retry after adding a small random perturbation by shuffling keys
        // (here: naive fallback: sleep-ish strategy not implemented; simply retry)
    }
    return 0;
}

// membership by u64 key-hash
int xor8_contains_hash(const xor8_t *xf, u64 keyhash) {
    if (!xf || xf->capacity == 0) return 1; // conservative: maybe present
    u32 i0, i1, i2; byte fp;
    derive_hashes(keyhash, &i0, &i1, &i2, &fp, xf->capacity);
    byte x = xf->finger[i0] ^ xf->finger[i1] ^ xf->finger[i2];
    return x == fp;
}

/* ----------------------- Helpers: build keys from text ----------------------- */

// build array of u64 hashes for every substrings of length m in text.
// returns allocated array (caller must free) and sets out_nkeys.
u64 *build_substring_keys(const char *text, size_t text_len, size_t m, u32 *out_nkeys) {
    if (text_len < m) { *out_nkeys = 0; return NULL; }
    u32 nkeys = (u32)(text_len - m + 1);
    u64 *keys = xmalloc((size_t)nkeys * sizeof(u64));
    for (u32 i = 0; i < nkeys; ++i) {
        keys[i] = fnv1a_64((const byte*)(text + i), m);
    }
    *out_nkeys = nkeys;
    return keys;
}

/* ----------------------- Main / demo ----------------------- */

int main() {
    // === Config ===
    const char *filename = "input.txt";
    size_t text_len;
    char *text = read_text_file(filename, &text_len);
    // lower-case to make matching case-insensitive (optional)
    to_lowercase(text);

    // Example patterns (you can replace with file input)
    const char *patterns_arr[] = {
        "apple", "quick", "brown", "quantum", "lazy", "data", "science", "pattern",
        "filter", "rabin", "karp", "algorithm", "substr", "match", "hello"
    };
    size_t n_patterns_all = sizeof(patterns_arr) / sizeof(patterns_arr[0]);

    // Group patterns by length using simple two-pass
    // Find max pattern length
    size_t max_m = 0;
    for (size_t i = 0; i < n_patterns_all; ++i) {
        size_t L = strlen(patterns_arr[i]);
        if (L > max_m) max_m = L;
    }

    // Create buckets for lengths 1..max_m
    // For ease, store vector of indices per length using dynamic arrays
    u32 *counts = xmalloc((max_m + 1) * sizeof(u32));
    memset(counts, 0, (max_m + 1) * sizeof(u32));
    for (size_t i = 0; i < n_patterns_all; ++i) {
        counts[strlen(patterns_arr[i])] ++;
    }
    // allocate index lists
    u32 **lists = xmalloc((max_m + 1) * sizeof(u32*));
    for (size_t m = 0; m <= max_m; ++m) {
        if (counts[m] == 0) lists[m] = NULL;
        else lists[m] = xmalloc(counts[m] * sizeof(u32));
    }
    // fill
    u32 *pos = xmalloc((max_m + 1) * sizeof(u32));
    memset(pos, 0, (max_m + 1) * sizeof(u32));
    for (u32 i = 0; i < (u32)n_patterns_all; ++i) {
        size_t L = strlen(patterns_arr[i]);
        lists[L][pos[L]++] = i;
    }

    // For each length m that has patterns, build XOR filter on m-substrings and query
    for (size_t m = 1; m <= max_m; ++m) {
        if (counts[m] == 0) continue;
        if (text_len < m) {
            printf("Text shorter than m=%zu, skipping length\n", m);
            continue;
        }
        printf("\n=== Processing patterns of length %zu (count=%u) ===\n", m, counts[m]);
        // build keys
        u32 nkeys;
        u64 *keys = build_substring_keys(text, text_len, m, &nkeys);
        printf("Built %u substring keys for m=%zu\n", nkeys, m);

        xor8_t filter;
        if (!xor8_build_with_retries(&filter, keys, nkeys)) {
            fprintf(stderr, "Failed to build XOR filter for m=%zu\n", m);
            free(keys);
            continue;
        }
        printf("XOR filter built: capacity=%u\n", filter.capacity);

        // query each pattern of this length
        u32 maybe_count = 0, confirmed = 0;
        for (u32 idx = 0; idx < counts[m]; ++idx) {
            u32 pat_index = lists[m][idx];
            const char *pat = patterns_arr[pat_index];
            u64 ph = fnv1a_64((const byte*)pat, m);
            if (xor8_contains_hash(&filter, ph)) {
                maybe_count++;
                int pos_found = rabin_karp_search(text, text_len, pat, m);
                if (pos_found >= 0) {
                    confirmed++;
                    printf("Pattern \"%s\" => FOUND at %d\n", pat, pos_found);
                } else {
                    printf("Pattern \"%s\" => XOR maybe but RK false positive\n", pat);
                }
            } else {
                printf("Pattern \"%s\" => XOR says definitely NOT present\n", pat);
            }
        }
        printf("Summary for length %zu: maybe=%u, confirmed=%u\n", m, maybe_count, confirmed);
        xor8_free(&filter);
        free(keys);
    }

    // cleanup
    for (size_t m = 0; m <= max_m; ++m) if (lists[m]) free(lists[m]);
    free(lists); free(counts); free(pos);
    free(text);
    return 0;
}
