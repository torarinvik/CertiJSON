#include "raylib_helper.h"
#include <stdio.h>
#include <stdlib.h>

Color MakeColor_Wrapper(int32_t r, int32_t g, int32_t b, int32_t a) {
    Color c = {(unsigned char)r, (unsigned char)g, (unsigned char)b, (unsigned char)a};
    return c;
}

int32_t int32_add(int32_t a, int32_t b) { return a + b; }
int32_t int32_sub(int32_t a, int32_t b) { return a - b; }
int32_t int32_mul(int32_t a, int32_t b) { return a * b; }
int32_t int32_div(int32_t a, int32_t b) { return b == 0 ? 0 : a / b; }
bool int32_lt(int32_t a, int32_t b) { return a < b; }
bool int32_gt(int32_t a, int32_t b) { return a > b; }
bool int32_eq(int32_t a, int32_t b) { return a == b; }

char* IntToString(int32_t val) {
    static char buffer[16];
    snprintf(buffer, 16, "%d", val);
    return buffer;
}
