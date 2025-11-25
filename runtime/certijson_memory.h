#ifndef CERTIJSON_MEMORY_H
#define CERTIJSON_MEMORY_H

#include <stdint.h>
#include <stddef.h>

uintptr_t cj_ptr_to_uintptr(const void* p);
void* cj_uintptr_to_ptr(uintptr_t v);
void* cj_ptr_offset(void* p, size_t bytes);
int32_t cj_load_int32(const void* p);
void cj_store_int32(void* p, int32_t v);

#endif
