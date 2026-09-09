#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <lean/lean.h>

extern lean_obj_res mergesort_sort_u64(lean_obj_arg xs);   /* @[export] from MergeSort/Export.lean */
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_mergesort_MergeSort_Export(uint8_t builtin, lean_object *w);

static uint64_t next(uint64_t *s) { *s ^= *s >> 12; *s ^= *s << 25; *s ^= *s >> 27; return *s * 0x2545F4914F6CDD1DULL; }

int main(int argc, char **argv) {
  size_t n = argc > 1 ? strtoull(argv[1], 0, 10) : 1000000;
  lean_initialize_runtime_module();
  lean_object *res = initialize_mergesort_MergeSort_Export(1, lean_io_mk_world());
  if (!lean_io_result_is_ok(res)) { lean_io_result_show_error(res); lean_dec(res); return 1; }
  lean_dec_ref(res);
  lean_io_mark_end_initialization();

  /* A UInt64Array is a Lean scalar array with 8-byte elements: fill it directly from C. */
  lean_object *arr = lean_alloc_sarray(8, n, n);
  uint64_t *data = (uint64_t *)lean_sarray_cptr(arr);
  uint64_t s = 42;
  for (size_t i = 0; i < n; i++) data[i] = next(&s);

  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  lean_object *sorted = mergesort_sort_u64(arr);   /* consumes arr; sorts in place (refcount 1) */
  clock_gettime(CLOCK_MONOTONIC, &t1);

  uint64_t *out = (uint64_t *)lean_sarray_cptr(sorted);
  int ok = 1;
  for (size_t i = 1; i < lean_sarray_size(sorted); i++) if (out[i-1] > out[i]) { ok = 0; break; }
  printf("sorted %zu u64 from C via verified Lean merge sort: %.1f ms, %s, in place: %s\n", n,
         (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6, ok ? "sorted" : "NOT SORTED",
         out == data ? "yes (same buffer)" : "no (new buffer)");
  lean_dec(sorted);
  return ok ? 0 : 1;
}
