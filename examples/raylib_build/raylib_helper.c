#include "raylib_helper.h"
#include <stdio.h>
#include <stdlib.h>

Color MakeColor_Wrapper(int32_t r, int32_t g, int32_t b, int32_t a) {
    Color c = {(unsigned char)r, (unsigned char)g, (unsigned char)b, (unsigned char)a};
    return c;
}

char* IntToString(int32_t val) {
    static char buffer[16];
    snprintf(buffer, 16, "%d", val);
    return buffer;
}
