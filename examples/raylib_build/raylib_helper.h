#ifndef RAYLIB_HELPER_H
#define RAYLIB_HELPER_H

#include <stdint.h>
#include <stdbool.h>
#include <raylib.h>

Color MakeColor_Wrapper(int32_t r, int32_t g, int32_t b, int32_t a);

int32_t int32_add(int32_t a, int32_t b);
int32_t int32_sub(int32_t a, int32_t b);
int32_t int32_mul(int32_t a, int32_t b);
int32_t int32_div(int32_t a, int32_t b);
bool int32_lt(int32_t a, int32_t b);
bool int32_gt(int32_t a, int32_t b);
bool int32_eq(int32_t a, int32_t b);
char* IntToString(int32_t val);

#endif
