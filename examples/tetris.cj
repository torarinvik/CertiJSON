import Std.IO
import Std.Bool
import Std.Memory
import Std.SafeMemory
import Raylib

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

# Collision check for a single block, returns 1 if collision, 0 if not
def check_block_bounds(view: ArrayView(Int32, 200L), px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32) -> IO(Int32):
    bx: Int32 = px + get_offset_x(pt, pr, idx)
    by: Int32 = py + get_offset_y(pt, pr, idx)
    
    # Bounds check
    out_of_bounds: Bool = (bx < 0) or (bx >= 10) or (by >= 20)
    if out_of_bounds:
        return Std.IO.return(Int32, 1)
    else:
        if by < 0:
            return Std.IO.return(Int32, 0)
        else:
            idx_val: Int64 = to_int64(bx + by * 10)
            return Std.IO.bind(Int32, Int32, view_get_int32(200L, view, idx_val), \cell ->
                res: Int32 = 1 if (cell != 0) else 0
                return Std.IO.return(Int32, res)
            )

# Check all 4 blocks for boundary collision
def check_bounds(grid: ArrayHandle(Int32, 200L), px: Int32, py: Int32, pt: Int32, pr: Int32) -> IO(Pair(ArrayHandle(Int32, 200L), Int32)):
    res_pair: Pair(ArrayHandle(Int32, 200L), Int32) <- as_view(Int32, 200L, Int32, grid, \view ->
        c0: Int32 <- check_block_bounds(view, px, py, pt, pr, 0)
        c1: Int32 <- check_block_bounds(view, px, py, pt, pr, 1)
        c2: Int32 <- check_block_bounds(view, px, py, pt, pr, 2)
        c3: Int32 <- check_block_bounds(view, px, py, pt, pr, 3)
        return Std.IO.return(Int32, c0 + c1 + c2 + c3)
    )
    return Std.IO.return(Pair(ArrayHandle(Int32, 200L), Int32), res_pair)

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
    bx: Int32 = px + get_offset_x(pt, pr, idx)
    by: Int32 = py + get_offset_y(pt, pr, idx)
    draw_block(bx, by, pt)

def draw_piece(px: Int32, py: Int32, pt: Int32, pr: Int32) -> IO(Unit):
    draw_piece_block(px, py, pt, pr, 0)
    draw_piece_block(px, py, pt, pr, 1)
    draw_piece_block(px, py, pt, pr, 2)
    draw_piece_block(px, py, pt, pr, 3)
    return Std.IO.return(Unit, tt)

def lock_block(view: ArrayView(Int32, 200L), px: Int32, py: Int32, pt: Int32, pr: Int32, idx: Int32) -> IO(Unit):
    bx: Int32 = px + get_offset_x(pt, pr, idx)
    by: Int32 = py + get_offset_y(pt, pr, idx)
    valid: Bool = (bx >= 0) and (bx < 10) and (by >= 0) and (by < 20)
    if valid:
        idx_val: Int64 = to_int64(bx + by * 10)
        view_set_int32(200L, view, idx_val, pt)
    else:
        return Std.IO.return(Unit, tt)

# Line clearing logic
def check_row_full(view: ArrayView(Int32, 200L), y: Int32, x: Int32) -> IO(Bool):
    if x >= 10:
        return Std.IO.return(Bool, True)
    else:
        idx: Int64 = to_int64(x + y * 10)
        cell: Int32 <- view_get_int32(200L, view, idx)
        if cell == 0:
            return Std.IO.return(Bool, False)
        else:
            check_row_full(view, y, x + 1)

def shift_row_down(view: ArrayView(Int32, 200L), y: Int32, x: Int32) -> IO(Unit):
    if x >= 10:
        return Std.IO.return(Unit, tt)
    else:
        src_idx: Int64 = to_int64(x + (y - 1) * 10)
        dst_idx: Int64 = to_int64(x + y * 10)
        val: Int32 <- view_get_int32(200L, view, src_idx)
        view_set_int32(200L, view, dst_idx, val)
        shift_row_down(view, y, x + 1)

def clear_top_row(view: ArrayView(Int32, 200L), x: Int32) -> IO(Unit):
    if x >= 10:
        return Std.IO.return(Unit, tt)
    else:
        idx: Int64 = to_int64(x)
        view_set_int32(200L, view, idx, 0)
        clear_top_row(view, x + 1)

def shift_rows(view: ArrayView(Int32, 200L), y: Int32) -> IO(Unit):
    if y <= 0:
        clear_top_row(view, 0)
    else:
        shift_row_down(view, y, 0)
        shift_rows(view, y - 1)

def check_lines_rec(view: ArrayView(Int32, 200L), y: Int32) -> IO(Unit):
    if y < 0:
        return Std.IO.return(Unit, tt)
    else:
        is_full: Bool <- check_row_full(view, y, 0)
        if is_full:
            shift_rows(view, y)
            check_lines_rec(view, y) # Check same row again
        else:
            check_lines_rec(view, y - 1)

def lock_piece(grid: ArrayHandle(Int32, 200L), px: Int32, py: Int32, pt: Int32, pr: Int32) -> IO(ArrayHandle(Int32, 200L)):
    res_pair: Pair(ArrayHandle(Int32, 200L), Unit) <- as_view(Int32, 200L, Unit, grid, \view ->
        lock_block(view, px, py, pt, pr, 0)
        lock_block(view, px, py, pt, pr, 1)
        lock_block(view, px, py, pt, pr, 2)
        lock_block(view, px, py, pt, pr, 3)
        check_lines_rec(view, 19)
        return Std.IO.return(Unit, tt)
    )
    return Std.IO.return(ArrayHandle(Int32, 200L), fst(ArrayHandle(Int32, 200L), Unit, res_pair))

def draw_cell(view: ArrayView(Int32, 200L), i: Int32) -> IO(Unit):
    idx_val: Int64 = to_int64(i)
    cell: Int32 <- view_get_int32(200L, view, idx_val)
    if cell != 0:
        x: Int32 = i % 10
        y: Int32 = i / 10
        draw_block(x, y, cell)
    else:
        return Std.IO.return(Unit, tt)

def draw_grid_rec(view: ArrayView(Int32, 200L), i: Int32) -> IO(Unit):
    if i >= 200:
        return Std.IO.return(Unit, tt)
    else:
        draw_cell(view, i)
        draw_grid_rec(view, i + 1)

def draw_grid(grid: ArrayHandle(Int32, 200L)) -> IO(ArrayHandle(Int32, 200L)):
    res_pair: Pair(ArrayHandle(Int32, 200L), Unit) <- as_view(Int32, 200L, Unit, grid, \view ->
        draw_grid_rec(view, 0)
    )
    return Std.IO.return(ArrayHandle(Int32, 200L), fst(ArrayHandle(Int32, 200L), Unit, res_pair))

def random_piece(seed: Int32) -> Int32:
    s: Int32 = seed % 7
    pos_s: Int32 = s if (s >= 0) else (0 - s)
    result: Int32 = pos_s + 1
    return result

def loop(grid: ArrayHandle(Int32, 200L), px: Int32, py: Int32, pt: Int32, pr: Int32, timer: Int32, seed: Int32) -> IO(Unit):
    should_close: Bool <- WindowShouldClose(tt)
    if should_close:
        # We must consume grid? No, loop returns Unit.
        # But grid is linear.
        # In ProofPy, if we drop a linear value, it's a leak.
        # But we don't have a destructor.
        # stack_alloc will free it anyway.
        # So we can just drop it here.
        return Std.IO.return(Unit, tt)
    else:
        key_left: Bool <- IsKeyPressed(263)
        key_right: Bool <- IsKeyPressed(262)
        key_down: Bool <- IsKeyDown(264)
        key_up: Bool <- IsKeyPressed(265)
        
        # Calculate movement
        dx: Int32 = (0 - 1) if key_left else (1 if key_right else 0)
        new_px: Int32 = px + dx
        new_pr: Int32 = ((pr + 1) % 4) if key_up else pr
        
        # Check horizontal collision
        res_h: Pair(ArrayHandle(Int32, 200L), Int32) <- check_bounds(grid, new_px, py, pt, pr)
        grid_h: ArrayHandle(Int32, 200L) = fst(ArrayHandle(Int32, 200L), Int32, res_h)
        h_coll: Int32 = snd(ArrayHandle(Int32, 200L), Int32, res_h)
        
        final_px: Int32 = px if (h_coll > 0) else new_px
        
        # Check rotation collision
        res_r: Pair(ArrayHandle(Int32, 200L), Int32) <- check_bounds(grid_h, px, py, pt, new_pr)
        grid_r: ArrayHandle(Int32, 200L) = fst(ArrayHandle(Int32, 200L), Int32, res_r)
        r_coll: Int32 = snd(ArrayHandle(Int32, 200L), Int32, res_r)
        
        final_pr: Int32 = pr if (r_coll > 0) else new_pr
        
        # Calculate drop
        drop_rate: Int32 = 5 if key_down else 30
        should_drop: Bool = (timer % drop_rate) == 0
        new_py: Int32 = (py + 1) if should_drop else py
        
        # Check vertical collision
        res_v: Pair(ArrayHandle(Int32, 200L), Int32) <- check_bounds(grid_r, final_px, new_py, pt, final_pr)
        grid_v: ArrayHandle(Int32, 200L) = fst(ArrayHandle(Int32, 200L), Int32, res_v)
        v_coll: Int32 = snd(ArrayHandle(Int32, 200L), Int32, res_v)
        
        need_lock: Bool = (v_coll > 0) and should_drop
        
        if need_lock:
            grid_locked: ArrayHandle(Int32, 200L) <- lock_piece(grid_v, final_px, py, pt, final_pr)
            new_seed: Int32 = seed * 1103515245 + 12345
            new_type: Int32 = random_piece(new_seed)
            BeginDrawing(tt)
            ClearBackground(GetColor(255))
            grid_drawn: ArrayHandle(Int32, 200L) <- draw_grid(grid_locked)
            draw_piece(4, 0, new_type, 0)
            EndDrawing(tt)
            loop(grid_drawn, 4, 0, new_type, 0, 0, new_seed)
        else:
            final_py: Int32 = py if (v_coll > 0) else new_py
            BeginDrawing(tt)
            ClearBackground(GetColor(255))
            grid_drawn: ArrayHandle(Int32, 200L) <- draw_grid(grid_v)
            draw_piece(final_px, final_py, pt, final_pr)
            EndDrawing(tt)
            loop(grid_drawn, final_px, final_py, pt, final_pr, timer + 1, seed)


def main() -> IO(Unit):
    InitWindow(300, 600, "ProofPy Tetris")
    SetTargetFPS(60)
    stack_alloc(Int32, 200L, Unit, \grid ->
        start_type: Int32 = random_piece(42)
        loop(grid, 4, 0, start_type, 0, 0, 42)
    )
    CloseWindow(tt)
