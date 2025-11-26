#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <certijson_io.h>
#include <certijson_atexit.h>
#include <certijson_memory.h>
#include <raylib.h>
#include <raymath.h>
#include <stdlib.h>
#include <string.h>


int32_t get_i_x(int32_t rot, int32_t idx);
int32_t get_i_y(int32_t rot, int32_t idx);
int32_t get_o_x(int32_t idx);
int32_t get_o_y(int32_t idx);
int32_t get_t_x(int32_t rot, int32_t idx);
int32_t get_t_y(int32_t rot, int32_t idx);
int32_t get_s_x(int32_t rot, int32_t idx);
int32_t get_s_y(int32_t rot, int32_t idx);
int32_t get_z_x(int32_t rot, int32_t idx);
int32_t get_z_y(int32_t rot, int32_t idx);
int32_t get_j_x(int32_t rot, int32_t idx);
int32_t get_j_y(int32_t rot, int32_t idx);
int32_t get_l_x(int32_t rot, int32_t idx);
int32_t get_l_y(int32_t rot, int32_t idx);
int32_t get_offset_x(int32_t ptype, int32_t rot, int32_t idx);
int32_t get_offset_y(int32_t ptype, int32_t rot, int32_t idx);
int32_t check_block_bounds(int32_t px, int32_t py, int32_t pt, int32_t pr, int32_t idx);
int32_t check_bounds(int32_t px, int32_t py, int32_t pt, int32_t pr);
int32_t get_color_hex(int32_t c);
void draw_block(int32_t x, int32_t y, int32_t c);
void draw_piece_block(int32_t px, int32_t py, int32_t pt, int32_t pr, int32_t idx);
void draw_piece(int32_t px, int32_t py, int32_t pt, int32_t pr);
void lock_block(void* grid, int32_t px, int32_t py, int32_t pt, int32_t pr, int32_t idx);
void lock_piece(void* grid, int32_t px, int32_t py, int32_t pt, int32_t pr);
void draw_cell(void* grid, int32_t i);
void draw_grid_rec(void* grid, int32_t i);
void draw_grid(void* grid);
int32_t random_piece(int32_t seed);
void read_cell(void* grid, int32_t x, int32_t y);
void loop(void* grid, int32_t px, int32_t py, int32_t pt, int32_t pr, int32_t timer, int32_t seed);
int32_t main();

int32_t get_i_x(int32_t rot, int32_t idx) {
bool horiz_1 = ((rot % 2) == 0);int32_t result_2 = (horiz_1 ? idx : 0);
return result_2;
}

int32_t get_i_y(int32_t rot, int32_t idx) {
bool horiz_1 = ((rot % 2) == 0);int32_t result_2 = (horiz_1 ? 0 : idx);
return result_2;
}

int32_t get_o_x(int32_t idx) {
int32_t result_1 = (idx % 2);
return result_1;
}

int32_t get_o_y(int32_t idx) {
int32_t result_1 = (idx / 2);
return result_1;
}

int32_t get_t_x(int32_t rot, int32_t idx) {
int32_t r_1 = (rot % 4);
int32_t x0_2 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 0 : 1)));
int32_t x1_3 = ((r_1 == 0) ? 0 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 1 : 0)));
int32_t x2_4 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 1 : ((r_1 == 2) ? 2 : 1)));
int32_t x3_5 = ((r_1 == 0) ? 2 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 1 : 2)));
int32_t result_6 = ((idx == 0) ? x0_2 : ((idx == 1) ? x1_3 : ((idx == 2) ? x2_4 : x3_5)));
return result_6;
}

int32_t get_t_y(int32_t rot, int32_t idx) {
int32_t r_1 = (rot % 4);
int32_t y0_2 = ((r_1 == 0) ? 0 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 1 : 0)));
int32_t y1_3 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 1 : ((r_1 == 2) ? 0 : 1)));
int32_t y2_4 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 0 : 1)));
int32_t y3_5 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 2 : ((r_1 == 2) ? 0 : 2)));
int32_t result_6 = ((idx == 0) ? y0_2 : ((idx == 1) ? y1_3 : ((idx == 2) ? y2_4 : y3_5)));
return result_6;
}

int32_t get_s_x(int32_t rot, int32_t idx) {
bool horiz_1 = ((rot % 2) == 0);int32_t x0_2 = (horiz_1 ? 1 : 0);
int32_t x1_3 = (horiz_1 ? 2 : 0);int32_t x2_4 = (horiz_1 ? 0 : 1);
int32_t x3_5 = (horiz_1 ? 1 : 1);
int32_t result_6 = ((idx == 0) ? x0_2 : ((idx == 1) ? x1_3 : ((idx == 2) ? x2_4 : x3_5)));
return result_6;
}

int32_t get_s_y(int32_t rot, int32_t idx) {
bool horiz_1 = ((rot % 2) == 0);int32_t y0_2 = (horiz_1 ? 0 : 0);
int32_t y1_3 = (horiz_1 ? 0 : 1);int32_t y2_4 = (horiz_1 ? 1 : 1);
int32_t y3_5 = (horiz_1 ? 1 : 2);
int32_t result_6 = ((idx == 0) ? y0_2 : ((idx == 1) ? y1_3 : ((idx == 2) ? y2_4 : y3_5)));
return result_6;
}

int32_t get_z_x(int32_t rot, int32_t idx) {
bool horiz_1 = ((rot % 2) == 0);int32_t x0_2 = (horiz_1 ? 0 : 1);
int32_t x1_3 = (horiz_1 ? 1 : 0);int32_t x2_4 = (horiz_1 ? 1 : 1);
int32_t x3_5 = (horiz_1 ? 2 : 0);
int32_t result_6 = ((idx == 0) ? x0_2 : ((idx == 1) ? x1_3 : ((idx == 2) ? x2_4 : x3_5)));
return result_6;
}

int32_t get_z_y(int32_t rot, int32_t idx) {
bool horiz_1 = ((rot % 2) == 0);int32_t y0_2 = (horiz_1 ? 0 : 0);
int32_t y1_3 = (horiz_1 ? 0 : 1);int32_t y2_4 = (horiz_1 ? 1 : 1);
int32_t y3_5 = (horiz_1 ? 1 : 2);
int32_t result_6 = ((idx == 0) ? y0_2 : ((idx == 1) ? y1_3 : ((idx == 2) ? y2_4 : y3_5)));
return result_6;
}

int32_t get_j_x(int32_t rot, int32_t idx) {
int32_t r_1 = (rot % 4);
int32_t x0_2 = ((r_1 == 0) ? 0 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 2 : 1)));
int32_t x1_3 = ((r_1 == 0) ? 0 : ((r_1 == 1) ? 1 : ((r_1 == 2) ? 0 : 0)));
int32_t x2_4 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 1 : 1)));
int32_t x3_5 = ((r_1 == 0) ? 2 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 2 : 1)));
int32_t result_6 = ((idx == 0) ? x0_2 : ((idx == 1) ? x1_3 : ((idx == 2) ? x2_4 : x3_5)));
return result_6;
}

int32_t get_j_y(int32_t rot, int32_t idx) {
int32_t r_1 = (rot % 4);
int32_t y0_2 = ((r_1 == 0) ? 0 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 0 : 0)));
int32_t y1_3 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 1 : 1)));
int32_t y2_4 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 1 : ((r_1 == 2) ? 1 : 1)));
int32_t y3_5 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 2 : ((r_1 == 2) ? 1 : 2)));
int32_t result_6 = ((idx == 0) ? y0_2 : ((idx == 1) ? y1_3 : ((idx == 2) ? y2_4 : y3_5)));
return result_6;
}

int32_t get_l_x(int32_t rot, int32_t idx) {
int32_t r_1 = (rot % 4);
int32_t x0_2 = ((r_1 == 0) ? 2 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 0 : 1)));
int32_t x1_3 = ((r_1 == 0) ? 0 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 2 : 1)));
int32_t x2_4 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 1 : ((r_1 == 2) ? 2 : 0)));
int32_t x3_5 = ((r_1 == 0) ? 2 : ((r_1 == 1) ? 1 : ((r_1 == 2) ? 2 : 1)));
int32_t result_6 = ((idx == 0) ? x0_2 : ((idx == 1) ? x1_3 : ((idx == 2) ? x2_4 : x3_5)));
return result_6;
}

int32_t get_l_y(int32_t rot, int32_t idx) {
int32_t r_1 = (rot % 4);
int32_t y0_2 = ((r_1 == 0) ? 0 : ((r_1 == 1) ? 0 : ((r_1 == 2) ? 1 : 0)));
int32_t y1_3 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 1 : ((r_1 == 2) ? 0 : 1)));
int32_t y2_4 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 1 : ((r_1 == 2) ? 0 : 1)));
int32_t y3_5 = ((r_1 == 0) ? 1 : ((r_1 == 1) ? 2 : ((r_1 == 2) ? 0 : 2)));
int32_t result_6 = ((idx == 0) ? y0_2 : ((idx == 1) ? y1_3 : ((idx == 2) ? y2_4 : y3_5)));
return result_6;
}

int32_t get_offset_x(int32_t ptype, int32_t rot, int32_t idx) {
int32_t result_1 = ((ptype == 1) ? get_i_x(rot, idx) : ((ptype == 2) ? get_o_x(idx) : ((ptype == 3) ? get_t_x(rot, idx) : ((ptype == 4) ? get_s_x(rot, idx) : ((ptype == 5) ? get_z_x(rot, idx) : ((ptype == 6) ? get_j_x(rot, idx) : get_l_x(rot, idx)))))));
return result_1;
}

int32_t get_offset_y(int32_t ptype, int32_t rot, int32_t idx) {
int32_t result_1 = ((ptype == 1) ? get_i_y(rot, idx) : ((ptype == 2) ? get_o_y(idx) : ((ptype == 3) ? get_t_y(rot, idx) : ((ptype == 4) ? get_s_y(rot, idx) : ((ptype == 5) ? get_z_y(rot, idx) : ((ptype == 6) ? get_j_y(rot, idx) : get_l_y(rot, idx)))))));
return result_1;
}

int32_t check_block_bounds(int32_t px, int32_t py, int32_t pt, int32_t pr, int32_t idx) {
int32_t bx_1 = (px + get_offset_x(pt, pr, idx));
int32_t by_2 = (py + get_offset_y(pt, pr, idx));
bool oob_3 = ((bx_1 < 0) || ((bx_1 > 9) || (by_2 > 19)));
int32_t result_4 = (oob_3 ? 1 : 0);
return result_4;
}

int32_t check_bounds(int32_t px, int32_t py, int32_t pt, int32_t pr) {
int32_t c0_1 = check_block_bounds(px, py, pt, pr, 0);
int32_t c1_2 = check_block_bounds(px, py, pt, pr, 1);
int32_t c2_3 = check_block_bounds(px, py, pt, pr, 2);
int32_t c3_4 = check_block_bounds(px, py, pt, pr, 3);
int32_t result_5 = (c0_1 + (c1_2 + (c2_3 + c3_4)));
return result_5;
}

int32_t get_color_hex(int32_t c) {
int32_t result_1 = ((c == 1) ? (0 - 16776961) : ((c == 2) ? 16711935 : ((c == 3) ? 65535 : ((c == 4) ? (0 - 256) : ((c == 5) ? (0 - 65281) : ((c == 6) ? (0 - 5963521) : ((c == 7) ? 1431655935 : 255)))))));
return result_1;
}

void draw_block(int32_t x, int32_t y, int32_t c) {
DrawRectangle((x * 30), (y * 30), 28, 28, GetColor(get_color_hex(c)));
}

void draw_piece_block(int32_t px, int32_t py, int32_t pt, int32_t pr, int32_t idx) {
int32_t bx_1 = (px + get_offset_x(pt, pr, idx));
int32_t by_2 = (py + get_offset_y(pt, pr, idx));
draw_block(bx_1, by_2, pt);
}

void draw_piece(int32_t px, int32_t py, int32_t pt, int32_t pr) {
draw_piece_block(px, py, pt, pr, 0);draw_piece_block(px, py, pt, pr, 1);
draw_piece_block(px, py, pt, pr, 2);
draw_piece_block(px, py, pt, pr, 3);
}

void lock_block(void* grid, int32_t px, int32_t py, int32_t pt, int32_t pr, int32_t idx) {
int32_t bx_1 = (px + get_offset_x(pt, pr, idx));
int32_t by_2 = (py + get_offset_y(pt, pr, idx));
bool valid_3 = ((bx_1 >= 0) && ((bx_1 < 10) && ((by_2 >= 0) && (by_2 < 20))));
if (valid_3) {
cj_store_int32(cj_ptr_offset(grid, ((bx_1 + (by_2 * 10)) * 4)), pt);
}
}

void lock_piece(void* grid, int32_t px, int32_t py, int32_t pt, int32_t pr) {
lock_block(grid, px, py, pt, pr, 0);lock_block(grid, px, py, pt, pr, 1);
lock_block(grid, px, py, pt, pr, 2);
lock_block(grid, px, py, pt, pr, 3);
}

void draw_cell(void* grid, int32_t i) {
int32_t cell_1;cell_1 = cj_load_int32(cj_ptr_offset(grid, (i * 4)));
if ((cell_1 != 0)) {
int32_t x_2 = (i % 10);int32_t y_3 = (i / 10);
draw_block(x_2, y_3, cell_1);
}
}

void draw_grid_rec(void* grid, int32_t i) {
if ((i >= 200)) {

} else {
draw_cell(grid, i);
draw_grid_rec(grid, (i + 1));
}
}

void draw_grid(void* grid) {
draw_grid_rec(grid, 0);
}

int32_t random_piece(int32_t seed) {
int32_t result_1 = ((seed % 7) + 1);
return result_1;
}

void read_cell(void* grid, int32_t x, int32_t y) {
if ((y < 0)) {

} else {
if (((x < 0) || ((x > 9) || (y > 19)))) {

}
}
}

void loop(void* grid, int32_t px, int32_t py, int32_t pt, int32_t pr, int32_t timer, int32_t seed) {
bool should_close_1;should_close_1 = WindowShouldClose();
if (should_close_1) {

} else {
bool key_left_2;key_left_2 = IsKeyPressed(263);bool key_right_3;
key_right_3 = IsKeyPressed(262);bool key_down_4;key_down_4 = IsKeyDown(264);
bool key_up_5;key_up_5 = IsKeyPressed(265);
int32_t dx_6 = (key_left_2 ? (0 - 1) : (key_right_3 ? 1 : 0));
int32_t new_px_7 = (px + dx_6);
int32_t new_pr_8 = (key_up_5 ? ((pr + 1) % 4) : pr);
int32_t h_coll_9 = check_bounds(new_px_7, py, pt, pr);
int32_t final_px_10 = ((h_coll_9 > 0) ? px : new_px_7);
int32_t r_coll_11 = check_bounds(px, py, pt, new_pr_8);
int32_t final_pr_12 = ((r_coll_11 > 0) ? pr : new_pr_8);
int32_t drop_rate_13 = (key_down_4 ? 5 : 30);
bool should_drop_14 = ((timer % drop_rate_13) == 0);
int32_t new_py_15 = (should_drop_14 ? (py + 1) : py);
int32_t v_coll_16 = check_bounds(final_px_10, new_py_15, pt, final_pr_12);
bool need_lock_17 = ((v_coll_16 > 0) && should_drop_14);
if (need_lock_17) {
lock_piece(grid, final_px_10, py, pt, final_pr_12);
int32_t new_seed_19 = ((seed * 1103515245) + 12345);
int32_t new_type_20 = random_piece(new_seed_19);BeginDrawing();
ClearBackground(GetColor(255));draw_grid(grid);
draw_piece(4, 0, new_type_20, 0);EndDrawing();
loop(grid, 4, 0, new_type_20, 0, 0, new_seed_19);
} else {
int32_t final_py_26 = ((v_coll_16 > 0) ? py : new_py_15);BeginDrawing();
ClearBackground(GetColor(255));draw_grid(grid);
draw_piece(final_px_10, final_py_26, pt, final_pr_12);EndDrawing();
loop(grid, final_px_10, final_py_26, pt, final_pr_12, (timer + 1), seed);
}
}
}

int32_t main() {
InitWindow(300, 600, "CertiJSON Tetris");SetTargetFPS(60);void* grid_3;
grid_3 = calloc(200LL, 4LL);int32_t start_type_4 = random_piece(42);
loop(grid_3, 4, 0, start_type_4, 0, 0, 42);free(grid_3);CloseWindow();
return 0;
}

