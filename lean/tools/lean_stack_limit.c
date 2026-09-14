#include <stddef.h>

/*
 * Lean 4.33's native executables reserve 1 GiB for each runtime thread by
 * default. Lake has no equivalent of the compiler's `-s` option. This is the
 * same process-local setter called by `lean -s8192`; it changes only thread
 * stack reservation, never the kernel, import artifacts, or proof checking.
 */
extern void *lean_internal_set_thread_stack_size(size_t bytes);

__attribute__((constructor))
static void limit_lean_thread_stack(void) {
    lean_internal_set_thread_stack_size(8 * 1024 * 1024);
}
