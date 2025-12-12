/* * xor_rk_presentation.c
 * * enhanced Rabin-Karp with XOR Filter.
 * - Prints the first few match Indices and Words to demonstrate correctness.
 * - Benchmarks the rest silently to demonstrate speed.
 * * Compile: gcc -O3 xor_rk_presentation.c -o xor_rk_demo
 * Run:     ./xor_rk_demo
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>
#include <time.h>
#include <math.h>

// =============================================================
// 1. CONFIGURATION
// =============================================================

typedef uint8_t  u8;
typedef uint32_t u32;
typedef uint64_t u64;

#define PATTERN_LEN 6
#define MAX_RETRIES 100
#define PRINT_LIMIT 10  // Only print the first 10 matches to save time

// =============================================================
// 2. TIMING & FILE UTILS
// =============================================================

double get_time_ms() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

char *read_file(const char *filename, size_t *len) {
    FILE *f = fopen(filename, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    rewind(f);
    char *buf = malloc(sz + 1);
    if (buf) {
        size_t r = fread(buf, 1, sz, f);
        buf[r] = '\0';
        if (len) *len = r;
    } else {
        if (len) *len = 0;
    }
    fclose(f);
    return buf;
}

// =============================================================
// 3. HASHING (Murmur3 / FNV)
// =============================================================

static inline u64 murmur64(u64 h) {
    h ^= h >> 33;
    h *= 0xff51afd7ed558ccdULL;
    h ^= h >> 33;
    h *= 0xc4ceb9fe1a85ec53ULL;
    h ^= h >> 33;
    return h;
}

static inline void get_hashes(u64 key, u64 seed, u32 capacity, u32 *h0, u32 *h1, u32 *h2) {
    u64 r = murmur64(key + seed);
    u32 blockLength = capacity / 3;
    *h0 = (u32)((r) % blockLength);
    *h1 = (u32)((r >> 21) % blockLength) + blockLength;
    *h2 = (u32)((r >> 42) % blockLength) + 2 * blockLength;
}

static inline u8 get_fingerprint(u64 key, u64 seed) {
    return (u8)(murmur64(key ^ seed) & 0xFF);
}

u64 fnv1a(const char *str, size_t n) {
    u64 hash = 14695981039346656037ULL;
    for (size_t i = 0; i < n; i++) {
        hash ^= (u8)str[i];
        hash *= 1099511628211ULL;
    }
    return hash;
}

// =============================================================
// 4. XOR FILTER IMPLEMENTATION
// =============================================================

typedef struct {
    u8 *fingerprints;
    u32 capacity;
    u64 seed;
} xorfilter_t;

int xorfilter_build(xorfilter_t *filter, u64 *keys, size_t count) {
    u32 capacity = (u32)(1.23 * count + 32);
    if (capacity % 3 != 0) capacity += (3 - (capacity % 3));
    
    filter->capacity = capacity;
    filter->fingerprints = malloc(capacity);
    
    u32 *counts = calloc(capacity, sizeof(u32));
    u64 *xor_masks = calloc(capacity, sizeof(u64));
    
    typedef struct { u64 key; u32 pivot; } stack_item;
    stack_item *stack = malloc(count * sizeof(stack_item));
    u32 stack_pos = 0;

    int success = 0;
    u32 *q = malloc(capacity * sizeof(u32));

    for (int attempt = 0; attempt < MAX_RETRIES; attempt++) {
        filter->seed = (u64)rand();
        memset(counts, 0, capacity * sizeof(u32));
        memset(xor_masks, 0, capacity * sizeof(u64));
        stack_pos = 0;
        
        for (size_t i = 0; i < count; i++) {
            u32 h0, h1, h2;
            get_hashes(keys[i], filter->seed, capacity, &h0, &h1, &h2);
            xor_masks[h0] ^= keys[i]; counts[h0]++;
            xor_masks[h1] ^= keys[i]; counts[h1]++;
            xor_masks[h2] ^= keys[i]; counts[h2]++;
        }
        
        u32 q_head = 0, q_tail = 0;
        for (u32 i = 0; i < capacity; i++) {
            if (counts[i] == 1) q[q_tail++] = i;
        }
        
        while (q_head < q_tail) {
            u32 idx = q[q_head++];
            if (counts[idx] != 1) continue; 
            
            u64 k = xor_masks[idx]; 
            stack[stack_pos].key = k;
            stack[stack_pos].pivot = idx;
            stack_pos++;
            
            u32 h0, h1, h2;
            get_hashes(k, filter->seed, capacity, &h0, &h1, &h2);
            
            counts[h0]--; xor_masks[h0] ^= k; if (counts[h0] == 1) q[q_tail++] = h0;
            counts[h1]--; xor_masks[h1] ^= k; if (counts[h1] == 1) q[q_tail++] = h1;
            counts[h2]--; xor_masks[h2] ^= k; if (counts[h2] == 1) q[q_tail++] = h2;
        }
        
        if (stack_pos == count) {
            success = 1;
            break;
        }
    }
    
    free(q); free(counts); free(xor_masks);

    if (!success) {
        free(stack); free(filter->fingerprints);
        return 0;
    }

    memset(filter->fingerprints, 0, capacity);
    for (int i = stack_pos - 1; i >= 0; i--) {
        u64 k = stack[i].key;
        u32 pivot = stack[i].pivot;
        u32 h0, h1, h2;
        get_hashes(k, filter->seed, capacity, &h0, &h1, &h2);
        u8 fp = get_fingerprint(k, filter->seed);
        filter->fingerprints[pivot] = fp ^ filter->fingerprints[h0] ^ filter->fingerprints[h1] ^ filter->fingerprints[h2];
    }
    free(stack);
    return 1;
}

void xorfilter_free(xorfilter_t *filter) {
    if (filter->fingerprints) free(filter->fingerprints);
    filter->fingerprints = NULL;
}

int xorfilter_contain(xorfilter_t *filter, u64 key) {
    u32 h0, h1, h2;
    get_hashes(key, filter->seed, filter->capacity, &h0, &h1, &h2);
    u8 fp = get_fingerprint(key, filter->seed);
    return (filter->fingerprints[h0] ^ filter->fingerprints[h1] ^ filter->fingerprints[h2]) == fp;
}

// =============================================================
// 5. HELPER: PATTERN LOADING
// =============================================================

int compare_u64(const void *a, const void *b) {
    u64 arg1 = *(const u64 *)a;
    u64 arg2 = *(const u64 *)b;
    if (arg1 < arg2) return -1;
    if (arg1 > arg2) return 1;
    return 0;
}

u64* load_and_deduplicate_patterns(const char* fname, size_t *out_count) {
    size_t len;
    char *buf = read_file(fname, &len);
    if (!buf) return NULL;
    size_t count = 0;
    for (size_t i = 0; i < len; i++) if (isspace((unsigned char)buf[i])) count++;
    count += 1;
    u64 *hashes = malloc(count * sizeof(u64));
    size_t idx = 0;
    char *ptr = buf;
    while (*ptr) {
        while (*ptr && isspace((unsigned char)*ptr)) ptr++;
        if (!*ptr) break;
        char *start = ptr;
        while (*ptr && !isspace((unsigned char)*ptr)) ptr++;
        if ((size_t)(ptr - start) == PATTERN_LEN) hashes[idx++] = fnv1a(start, PATTERN_LEN);
    }
    free(buf);
    qsort(hashes, idx, sizeof(u64), compare_u64);
    size_t unique_count = 0;
    if (idx > 0) {
        size_t write = 1;
        for (size_t read = 1; read < idx; read++) {
            if (hashes[read] != hashes[read-1]) hashes[write++] = hashes[read];
        }
        unique_count = write;
    } else if (idx == 1) unique_count = 1;
    *out_count = unique_count;
    return hashes;
}

// =============================================================
// 6. MAIN & BENCHMARK
// =============================================================

int main() {
    printf("==========================================\n");
    printf("   XOR Filter + Rabin Karp Presentation   \n");
    printf("==========================================\n");

    size_t n_patterns = 0;
    u64 *pat_hashes = load_and_deduplicate_patterns("patterns.txt", &n_patterns);
    if (!pat_hashes || n_patterns == 0) return 1;
    printf("[*] Loaded %zu patterns.\n", n_patterns);

    xorfilter_t filter;
    if (!xorfilter_build(&filter, pat_hashes, n_patterns)) return 1;
    printf("[*] XOR Filter Built (Capacity: %u).\n", filter.capacity);

    size_t text_len = 0;
    char *text = read_file("benchmark_input.txt", &text_len);
    if (!text) return 1;
    printf("[*] Input Text Loaded (%.2f MB).\n", text_len / 1024.0 / 1024.0);
    
    // ----------------------------------------------------------------
    // DEMONSTRATION: Baseline Rabin-Karp
    // ----------------------------------------------------------------
    printf("\n--- 1. Baseline Rabin-Karp Search ---\n");
    printf("(Showing first %d matches to prove correctness)\n", PRINT_LIMIT);
    
    size_t matches_naive = 0;
    double t_start = get_time_ms();
    
    if (text_len >= PATTERN_LEN) {
        u64 current_hash = fnv1a(text, PATTERN_LEN); 
        for (size_t i = 0; i <= text_len - PATTERN_LEN; i++) {
            u64 *item = bsearch(&current_hash, pat_hashes, n_patterns, sizeof(u64), compare_u64);
            if (item) {
                // PRINTING LOGIC HERE
                if (matches_naive < PRINT_LIMIT) {
                    printf("   [Baseline] Found \"%.*s\" at index %zu\n", PATTERN_LEN, text+i, i);
                }
                matches_naive++;
            }
            if (i < text_len - PATTERN_LEN) current_hash = fnv1a(text + i + 1, PATTERN_LEN);
        }
    }
    double t_naive = get_time_ms() - t_start;
    printf("... (Remaining output suppressed for speed)\n");
    printf("Total Matches: %zu | Time: %.2f ms\n", matches_naive, t_naive);

    // ----------------------------------------------------------------
    // DEMONSTRATION: Enhanced Rabin-Karp
    // ----------------------------------------------------------------
    printf("\n--- 2. Enhanced XOR+Rabin-Karp Search ---\n");
    printf("(Showing first %d matches to prove correctness)\n", PRINT_LIMIT);

    size_t matches_enhanced = 0;
    size_t filter_hits = 0; 
    t_start = get_time_ms();
    
    if (text_len >= PATTERN_LEN) {
        u64 current_hash = fnv1a(text, PATTERN_LEN);
        for (size_t i = 0; i <= text_len - PATTERN_LEN; i++) {
            
            // 1. Query XOR Filter
            if (xorfilter_contain(&filter, current_hash)) {
                filter_hits++;
                
                // 2. If Filter says "Yes", Verify with Binary Search
                u64 *item = bsearch(&current_hash, pat_hashes, n_patterns, sizeof(u64), compare_u64);
                if (item) {
                    // PRINTING LOGIC HERE
                    if (matches_enhanced < PRINT_LIMIT) {
                        printf("   [Enhanced] Found \"%.*s\" at index %zu\n", PATTERN_LEN, text+i, i);
                    }
                    matches_enhanced++;
                }
            }
            
            if (i < text_len - PATTERN_LEN) current_hash = fnv1a(text + i + 1, PATTERN_LEN);
        }
    }
    double t_enhanced = get_time_ms() - t_start;

    printf("... (Remaining output suppressed for speed)\n");
    printf("Total Matches: %zu | Time: %.2f ms\n", matches_enhanced, t_enhanced);
    
    double skip_percent = 100.0 * (1.0 - (double)filter_hits / (text_len - PATTERN_LEN));
    printf("Filter Skipped: %.2f%% of expensive checks.\n", skip_percent);
    
    printf("\n==========================================\n");
    if (t_enhanced < t_naive) {
        printf("FINAL RESULT: Enhanced is %.2fx FASTER\n", t_naive / t_enhanced);
    } else {
        printf("FINAL RESULT: Speeds are similar (overhead matches gains).\n");
    }
    printf("==========================================\n");

    xorfilter_free(&filter);
    free(pat_hashes);
    free(text);
    return 0;
}