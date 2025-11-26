#ifndef CERTIJSON_MEMORY_H
#define CERTIJSON_MEMORY_H

#include <stdint.h>
#include <stddef.h>

uintptr_t cj_ptr_to_uintptr(const void* p);
void* cj_uintptr_to_ptr(uintptr_t v);
void* cj_ptr_offset(void* p, size_t bytes);
int32_t cj_load_int32(const void* p);
void cj_store_int32(void* p, int32_t v);

// Safe Memory
void* cj_stack_alloc(size_t n, void* callback);
void* cj_as_view(void* handle, void* callback);
int32_t cj_view_get_int32(void* view, int64_t idx);
void cj_view_set_int32(void* view, int64_t idx, int32_t val);
int64_t cj_int32_to_int64(int32_t x);

#endif
