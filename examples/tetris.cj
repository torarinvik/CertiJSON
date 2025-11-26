import Std.IO
import Std.Bool
import Std.Memory
import Std.Int
import Raylib

# Refinement Types
def Nat() -> Type:
    {x: Int32 | x >= 0}

def Fin(n: Int32) -> Type:
    {x: Int32 | 0 <= x and x < n}

# Tetromino shapes
# Types: 1=I, 2=O, 3=T, 4=S, 5=Z, 6=J, 7=L

def get_i_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 0
        case 1:
            1 if horiz else 0
        case 2:
            2 if horiz else 0
        case 3:
            3 if horiz else 0

def get_i_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 0
        case 1:
            0 if horiz else 1
        case 2:
            0 if horiz else 2
        case 3:
            0 if horiz else 3

def get_o_x(idx: Int32) -> Int32:
    match idx:
        case 0:
            0
        case 1:
            1
        case 2:
            0
        case 3:
            1

def get_o_y(idx: Int32) -> Int32:
    match idx:
        case 0:
            0
        case 1:
            0
        case 2:
            1
        case 3:
            1

def get_t_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    1
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2
        case 1:
            match idx:
                case 0:
                    1
                case 1:
                    1
                case 2:
                    1
                case 3:
                    0
        case 2:
            match idx:
                case 0:
                    1
                case 1:
                    2
                case 2:
                    1
                case 3:
                    0
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    0
                case 3:
                    1

def get_t_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    1
                case 3:
                    1
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    1
        case 2:
            match idx:
                case 0:
                    1
                case 1:
                    0
                case 2:
                    0
                case 3:
                    0
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    1

def get_s_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            1 if horiz else 0
        case 1:
            2 if horiz else 0
        case 2:
            0 if horiz else 1
        case 3:
            1 if horiz else 1

def get_s_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 0
        case 1:
            0 if horiz else 1
        case 2:
            1 if horiz else 1
        case 3:
            1 if horiz else 2

def get_z_x(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 1
        case 1:
            1 if horiz else 1
        case 2:
            1 if horiz else 0
        case 3:
            2 if horiz else 0

def get_z_y(rot: Int32, idx: Int32) -> Int32:
    horiz: Bool = (rot % 2) == 0
    match idx:
        case 0:
            0 if horiz else 0
        case 1:
            0 if horiz else 1
        case 2:
            1 if horiz else 1
        case 3:
            1 if horiz else 2

def get_j_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    0
                case 3:
                    0
        case 2:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    2
        case 3:
            match idx:
                case 0:
                    1
                case 1:
                    1
                case 2:
                    1
                case 3:
                    0

def get_j_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    1
                case 3:
                    1
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2
        case 2:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    0
                case 3:
                    1
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    2

def get_l_x(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    2
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    0
                case 3:
                    1
        case 2:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    0
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    1
                case 3:
                    1

def get_l_y(rot: Int32, idx: Int32) -> Int32:
    r: Int32 = rot % 4
    match r:
        case 0:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    1
                case 3:
                    1
        case 1:
            match idx:
                case 0:
                    0
                case 1:
                    1
                case 2:
                    2
                case 3:
                    2
        case 2:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    0
                case 3:
                    1
        case 3:
            match idx:
                case 0:
                    0
                case 1:
                    0
                case 2:
                    1
                case 3:
                    2

def get_offset_x(ptype: Int32, rot: Int32, idx: Int32) -> Int32:
    match ptype:
        case 1:
            get_i_x(rot, idx)
        case 2:
            get_o_x(idx)
        case 3:
            get_t_x(rot, idx)
        case 4:
            get_s_x(rot, idx)
        case 5:
            get_z_x(rot, idx)
        case 6:
            get_j_x(rot, idx)
        case 7:
            get_l_x(rot, idx)
        case _:
            0

def get_offset_y(ptype: Int32, rot: Int32, idx: Int32) -> Int32:
    match ptype:
        case 1:
            get_i_y(rot, idx)
        case 2:
            get_o_y(idx)
        case 3:
            get_t_y(rot, idx)
        case 4:
            get_s_y(rot, idx)
        case 5:
            get_z_y(rot, idx)
        case 6:
            get_j_y(rot, idx)
        case 7:
            get_l_y(rot, idx)
        case _:
            0

# Collision check for a single block, returns 1 if collision, 0 if not
def check_block_bounds(view: VoidPtr, px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32) -> Int32:
    bx : Int32 = px + get_offset_x(pt, pr, idx)
    by : Int32 = py + get_offset_y(pt, pr, idx)
    
    # Bounds check
    if (bx < 0) or (bx >= 10) or (by >= 20):
        1
    else:
        if by < 0:
            0
        else:
            idx_val : Int64 = Std.Memory.int32_to_int64(bx + by * 10)
            offset : Int64 = Std.Int.mul64(idx_val, 4L)
            ptr : VoidPtr = Std.Memory.ptr_offset(view, offset)
            cell : Int32 = Std.Memory.unsafe_load_int32(ptr)
            if cell != 0:
                1
            else:
                0

# Check all 4 blocks for boundary collision
def check_bounds(grid: Int64, px: Int32, py: Int32, pt: Int32, pr: Int32) -> Int32:
    view : VoidPtr = Std.Memory.int64_to_ptr(grid)
    c0 : Int32 = check_block_bounds(view, px, py, pt, pr, 0)
    c1 : Int32 = check_block_bounds(view, px, py, pt, pr, 1)
    c2 : Int32 = check_block_bounds(view, px, py, pt, pr, 2)
    c3 : Int32 = check_block_bounds(view, px, py, pt, pr, 3)
    return c0 + c1 + c2 + c3

def get_color_hex(c: Int32) -> Int32:
    match c:
        case 1:
            0 - 16776961
        case 2:
            16711935
        case 3:
            65535
        case 4:
            0 - 256
        case 5:
            0 - 65281
        case 6:
            0 - 5963521
        case 7:
            1431655935
        case _:
            255

def draw_block(x: Int32, y: Int32, c: Int32) -> IO(Unit):
    DrawRectangle(x * 30, y * 30, 28, 28, GetColor(get_color_hex(c)))

def draw_piece_block(px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32) -> IO(Unit):
    bx : Int32 = px + get_offset_x(pt, pr, idx)
    by : Int32 = py + get_offset_y(pt, pr, idx)
    draw_block(bx, by, pt)

def draw_piece(px: Int32, py: Int32, pt: Int32, pr: Int32) -> IO(Unit):
    draw_piece_block(px, py, pt, pr, 0)
    draw_piece_block(px, py, pt, pr, 1)
    draw_piece_block(px, py, pt, pr, 2)
    draw_piece_block(px, py, pt, pr, 3)
    return Std.IO.return(Unit, tt)

def lock_block(view: VoidPtr, px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32) -> Unit:
    bx : Int32 = px + get_offset_x(pt, pr, idx)
    by : Int32 = py + get_offset_y(pt, pr, idx)
    valid : Bool = (bx >= 0) and (bx < 10) and (by >= 0) and (by < 20)
    if valid:
        idx_val : Int64 = Std.Memory.int32_to_int64(bx + by * 10)
        offset : Int64 = Std.Int.mul64(idx_val, 4L)
        ptr : VoidPtr = Std.Memory.ptr_offset(view, offset)
        dummy : Int32 = Std.Memory.unsafe_store_int32(ptr, pt)

# Line clearing logic
def check_row_full(view: VoidPtr, y: Int32, x: Int32) -> Bool:
    if x >= 10:
        True
    else:
        idx : Int64 = Std.Memory.int32_to_int64(x + y * 10)
        offset : Int64 = Std.Int.mul64(idx, 4L)
        ptr : VoidPtr = Std.Memory.ptr_offset(view, offset)
        cell : Int32 = Std.Memory.unsafe_load_int32(ptr)
        if cell == 0:
            False
        else:
            check_row_full(view, y, x + 1)

def shift_row_down(view: VoidPtr, y: Int32, x: Int32) -> Unit:
    if x < 10:
        src_idx : Int64 = Std.Memory.int32_to_int64(x + (y - 1) * 10)
        dst_idx : Int64 = Std.Memory.int32_to_int64(x + y * 10)
        
        src_offset : Int64 = Std.Int.mul64(src_idx, 4L)
        dst_offset : Int64 = Std.Int.mul64(dst_idx, 4L)
        
        src_ptr : VoidPtr = Std.Memory.ptr_offset(view, src_offset)
        dst_ptr : VoidPtr = Std.Memory.ptr_offset(view, dst_offset)
        
        val : Int32 = Std.Memory.unsafe_load_int32(src_ptr)
        _ : Int32 = Std.Memory.unsafe_store_int32(dst_ptr, val)
        shift_row_down(view, y, x + 1)

def clear_top_row(view: VoidPtr, x: Int32) -> Unit:
    if x < 10:
        idx : Int64 = Std.Memory.int32_to_int64(x)
        offset : Int64 = Std.Int.mul64(idx, 4L)
        ptr : VoidPtr = Std.Memory.ptr_offset(view, offset)
        _ : Int32 = Std.Memory.unsafe_store_int32(ptr, 0)
        clear_top_row(view, x + 1)

def shift_rows(view: VoidPtr, y: Int32) -> Unit:
    if y > 0:
        _ : Unit = shift_row_down(view, y, 0)
        shift_rows(view, y - 1)
    else:
        _ : Unit = clear_top_row(view, 0)

def check_lines_rec(view: VoidPtr, y: Int32) -> Unit:
    if y >= 0:
        if check_row_full(view, y, 0):
            _ : Unit = shift_rows(view, y)
            check_lines_rec(view, y)
        else:
            check_lines_rec(view, y - 1)

def lock_piece(grid: Int64, px: Int32, py: Int32, pt: Int32, pr: Int32) -> Unit:
    view : VoidPtr = Std.Memory.int64_to_ptr(grid)
    _ : Unit = lock_block(view, px, py, pt, pr, 0)
    _ : Unit = lock_block(view, px, py, pt, pr, 1)
    _ : Unit = lock_block(view, px, py, pt, pr, 2)
    _ : Unit = lock_block(view, px, py, pt, pr, 3)
    
    _ : Unit = check_lines_rec(view, 19)

def draw_cell(view: VoidPtr, i: Int32) -> IO(Unit):
    idx_val : Int64 = Std.Memory.int32_to_int64(i)
    offset : Int64 = Std.Int.mul64(idx_val, 4L)
    ptr : VoidPtr = Std.Memory.ptr_offset(view, offset)
    cell : Int32 = Std.Memory.unsafe_load_int32(ptr)
    if cell != 0:
        x : Int32 = i % 10
        y : Int32 = i / 10
        draw_block(x, y, cell)
    else:
        return Std.IO.return(Unit, tt)

def draw_grid_rec(view: VoidPtr, i: Int32) -> IO(Unit):
    if i < 200:
        draw_cell(view, i)
        draw_grid_rec(view, i + 1)
    else:
        Std.IO.return(Unit, tt)

def draw_grid(grid: Int64) -> IO(Unit):
    view : VoidPtr = Std.Memory.int64_to_ptr(grid)
    draw_grid_rec(view, 0)

def random_piece(seed: Int32) -> Int32:
    s : Int32 = seed % 7
    pos_s : Int32 = s if (s >= 0) else (0 - s)
    return pos_s + 1

def game_loop(grid: Int64, px: Int32, py: Int32, pt: Int32, pr: Int32, timer: Int32, seed: Int32, game_over: Bool) -> IO(Unit):
    should_close : Bool <- WindowShouldClose(tt)
    if should_close:
        Std.IO.return(Unit, tt)
    else:
        if game_over:
            BeginDrawing(tt)
            ClearBackground(GetColor(255))
            draw_grid(grid)
            DrawText("GAME OVER", 50, 250, 40, GetColor(0 - 16776961))
            EndDrawing(tt)
            game_loop(grid, px, py, pt, pr, timer, seed, game_over)
        else:
            # Input handling
            key_left : Bool <- IsKeyPressed(263)
            key_right : Bool <- IsKeyPressed(262)
            key_down : Bool <- IsKeyDown(264)
            key_up : Bool <- IsKeyPressed(265)
            
            # Horizontal movement
            dx : Int32 = (0 - 1) if key_left else (1 if key_right else 0)
            
            new_px : Int32 = px + dx
            final_px : Int32 = new_px if (check_bounds(grid, new_px, py, pt, pr) == 0) else px
            
            # Rotation
            new_pr : Int32 = (pr + 1) % 4
            final_pr : Int32 = new_pr if (key_up and (check_bounds(grid, final_px, py, pt, new_pr) == 0)) else pr
            
            # Vertical movement (Gravity)
            drop_rate : Int32 = 5 if key_down else 30
            
            should_drop : Bool = (timer % drop_rate) == 0
            
            if should_drop:
                new_py : Int32 = py + 1
                if check_bounds(grid, final_px, new_py, pt, final_pr) == 0:
                    # Drawing
                    BeginDrawing(tt)
                    ClearBackground(GetColor(255))
                    draw_grid(grid)
                    draw_piece(final_px, new_py, pt, final_pr)
                    EndDrawing(tt)
                    game_loop(grid, final_px, new_py, pt, final_pr, timer + 1, seed, game_over)
                else:
                    # Lock piece
                    _ : Unit = lock_piece(grid, final_px, py, pt, final_pr)
                    
                    # Spawn new piece
                    new_seed : Int32 = (seed * 1103515245) + 12345
                    new_pt : Int32 = random_piece(new_seed)
                    new_px_spawn : Int32 = 4
                    new_py_spawn : Int32 = 0
                    new_pr_spawn : Int32 = 0
                    
                    # Check Game Over
                    new_game_over : Bool = check_bounds(grid, new_px_spawn, new_py_spawn, new_pt, new_pr_spawn) > 0
                    
                    # Drawing
                    BeginDrawing(tt)
                    ClearBackground(GetColor(255))
                    draw_grid(grid)
                    draw_piece(final_px, py, pt, final_pr)
                    EndDrawing(tt)
                    
                    game_loop(grid, new_px_spawn, new_py_spawn, new_pt, new_pr_spawn, timer + 1, new_seed, new_game_over)
            else:
                # Drawing
                BeginDrawing(tt)
                ClearBackground(GetColor(255))
                draw_grid(grid)
                draw_piece(final_px, py, pt, final_pr)
                EndDrawing(tt)
                game_loop(grid, final_px, py, pt, final_pr, timer + 1, seed, game_over)

def main() -> IO(Unit):
    InitWindow(300, 600, "ProofPy Tetris")
    SetTargetFPS(60)
    
    grid_ptr : VoidPtr <- Std.Memory.calloc(200L, 4L)
    grid : Int64 = Std.Memory.ptr_to_int64(grid_ptr)
    
    # Game state variables
    px : Int32 = 4
    py : Int32 = 0
    pt : Int32 = random_piece(42)
    pr : Int32 = 0
    timer : Int32 = 0
    seed : Int32 = 42
    game_over : Bool = False
    
    game_loop(grid, px, py, pt, pr, timer, seed, game_over)

    grid_ptr_free : VoidPtr = Std.Memory.int64_to_ptr(grid)
    Std.Memory.free(grid_ptr_free)
    CloseWindow(tt)
    return Std.IO.return(Unit, tt)
