#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <certijson_io.h>
#include "raylib_helper.h"
#include <raylib.h>


void loop(int32_t ball_x, int32_t ball_y, int32_t ball_dx, int32_t ball_dy, int32_t p1_y, int32_t p2_y, int32_t s1, int32_t s2) {
bool should_close;should_close = WindowShouldClose();
if (should_close) {

} else {
bool key_w;key_w = IsKeyDown(87);bool key_s;key_s = IsKeyDown(83);
bool key_up;key_up = IsKeyDown(265);bool key_down;key_down = IsKeyDown(264);
BeginDrawing();ClearBackground(MakeColor_Wrapper(0, 0, 0, 255));
DrawRectangle(10, (key_w ? (p1_y - 5) : (key_s ? (p1_y + 5) : p1_y)), 20, 100, MakeColor_Wrapper(255, 255, 255, 255));
DrawRectangle(770, (key_up ? (p2_y - 5) : (key_down ? (p2_y + 5) : p2_y)), 20, 100, MakeColor_Wrapper(255, 255, 255, 255));
DrawRectangle((((ball_x + ball_dx) < 0) ? 400 : (((ball_x + ball_dx) > 800) ? 400 : (ball_x + ball_dx))), (((ball_x + ball_dx) < 0) ? 225 : (((ball_x + ball_dx) > 800) ? 225 : (ball_y + ball_dy))), 20, 20, MakeColor_Wrapper(255, 255, 255, 255));
DrawText(IntToString((((ball_x + ball_dx) > 800) ? (s1 + 1) : s1)), 200, 20, 40, MakeColor_Wrapper(255, 255, 255, 255));
DrawText(IntToString((((ball_x + ball_dx) < 0) ? (s2 + 1) : s2)), 600, 20, 40, MakeColor_Wrapper(255, 255, 255, 255));
EndDrawing();
loop((((ball_x + ball_dx) < 0) ? 400 : (((ball_x + ball_dx) > 800) ? 400 : (ball_x + ball_dx))), (((ball_x + ball_dx) < 0) ? 225 : (((ball_x + ball_dx) > 800) ? 225 : (ball_y + ball_dy))), ((((ball_x + ball_dx) < 20) ? (((ball_y + ball_dy) > (key_w ? (p1_y - 5) : (key_s ? (p1_y + 5) : p1_y))) ? ((ball_y + ball_dy) < ((key_w ? (p1_y - 5) : (key_s ? (p1_y + 5) : p1_y)) + 100)) : false) : false) ? (0 - ball_dx) : ((((ball_x + ball_dx) > 760) ? (((ball_y + ball_dy) > (key_up ? (p2_y - 5) : (key_down ? (p2_y + 5) : p2_y))) ? ((ball_y + ball_dy) < ((key_up ? (p2_y - 5) : (key_down ? (p2_y + 5) : p2_y)) + 100)) : false) : false) ? (0 - ball_dx) : ball_dx)), (((ball_y + ball_dy) < 0) ? (0 - ball_dy) : (((ball_y + ball_dy) > 430) ? (0 - ball_dy) : ball_dy)), (key_w ? (p1_y - 5) : (key_s ? (p1_y + 5) : p1_y)), (key_up ? (p2_y - 5) : (key_down ? (p2_y + 5) : p2_y)), (((ball_x + ball_dx) > 800) ? (s1 + 1) : s1), (((ball_x + ball_dx) < 0) ? (s2 + 1) : s2));
}
}

int32_t main() {
InitWindow(800, 450, "CertiJSON Pong");SetTargetFPS(60);
loop(400, 225, 5, 5, 175, 175, 0, 0);CloseWindow();
return 0;
}

