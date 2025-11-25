import json

def var(name): return {"var": name}
def app(f, args): return {"app": [f] + args}
def lam(arg_name, arg_type, body): return {"lambda": {"arg": {"name": arg_name, "type": arg_type}, "body": body}}
def bind(typ_a, typ_b, m, f): return app(var("bind"), [typ_a, typ_b, m, f])
def ret(typ, val): return app(var("return"), [typ, val])
def int32(val): return {"int32": val}
def bool_lit(val): return {"bool": val}
def string(val): return {"string": val}
def unit(): return var("Unit")
def tt(): return var("tt")
def prim(p): return {"prim": p}

declarations = []

# Basic Types
declarations.append({
    "inductive": {
        "name": "Unit",
        "params": [],
        "universe": "Type",
        "constructors": [{ "name": "tt", "args": [] }]
    }
})

declarations.append({
    "inductive": {
        "name": "World",
        "params": [],
        "universe": "Type",
        "constructors": [{ "name": "world_token", "args": [] }]
    }
})

declarations.append({
    "inductive": {
        "name": "Pair",
        "params": [{ "name": "A", "type": { "universe": "Type" } }, { "name": "B", "type": { "universe": "Type" } }],
        "universe": "Type",
        "constructors": [{ "name": "pair", "args": [{ "name": "fst", "type": { "var": "A" } }, { "name": "snd", "type": { "var": "B" } }] }]
    }
})

# IO Monad
declarations.append({
    "def": {
        "name": "IO",
        "type": {
            "pi": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "result": { "universe": "Type" }
            }
        },
        "body": {
            "lambda": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "body": {
                    "pi": {
                        "arg": { "name": "w", "type": { "var": "World" } },
                        "result": { "app": [{ "var": "Pair" }, { "var": "A" }, { "var": "World" }] }
                    }
                }
            }
        }
    }
})

declarations.append({
    "def": {
        "name": "return",
        "type": {
            "forall": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "result": {
                    "pi": {
                        "arg": { "name": "x", "type": { "var": "A" } },
                        "result": { "app": [{ "var": "IO" }, { "var": "A" }] }
                    }
                }
            }
        },
        "body": {
            "lambda": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "body": {
                    "lambda": {
                        "arg": { "name": "x", "type": { "var": "A" } },
                        "body": {
                            "lambda": {
                                "arg": { "name": "w", "type": { "var": "World" } },
                                "body": { "app": [{ "var": "pair" }, { "var": "A" }, { "var": "World" }, { "var": "x" }, { "var": "w" }] }
                            }
                        }
                    }
                }
            }
        }
    }
})

declarations.append({
    "def": {
        "name": "bind",
        "type": {
            "forall": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "result": {
                    "forall": {
                        "arg": { "name": "B", "type": { "universe": "Type" } },
                        "result": {
                            "pi": {
                                "arg": { "name": "m", "type": { "app": [{ "var": "IO" }, { "var": "A" }] } },
                                "result": {
                                    "pi": {
                                        "arg": { "name": "f", "type": { "pi": { "arg": { "name": "x", "type": { "var": "A" } }, "result": { "app": [{ "var": "IO" }, { "var": "B" }] } } } },
                                        "result": { "app": [{ "var": "IO" }, { "var": "B" }] }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        },
        "body": {
            "lambda": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "body": {
                    "lambda": {
                        "arg": { "name": "B", "type": { "universe": "Type" } },
                        "body": {
                            "lambda": {
                                "arg": { "name": "m", "type": { "app": [{ "var": "IO" }, { "var": "A" }] } },
                                "body": {
                                    "lambda": {
                                        "arg": { "name": "f", "type": { "pi": { "arg": { "name": "x", "type": { "var": "A" } }, "result": { "app": [{ "var": "IO" }, { "var": "B" }] } } } },
                                        "body": {
                                            "lambda": {
                                                "arg": { "name": "w", "type": { "var": "World" } },
                                                "body": {
                                                    "match": {
                                                        "scrutinee": { "app": [{ "var": "m" }, { "var": "w" }] },
                                                        "motive": { "app": [{ "var": "Pair" }, { "var": "B" }, { "var": "World" }] },
                                                        "cases": [{
                                                            "pattern": { "ctor": "pair", "args": [{ "name": "a" }, { "name": "w_prime" }] },
                                                            "body": { "app": [{ "var": "f" }, { "var": "a" }, { "var": "w_prime" }] }
                                                        }],
                                                        "coverage_hint": "complete"
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
})

# Primitives
declarations.append({ "repr": { "name": "int", "kind": "primitive", "c_type": "int", "size_bits": 32, "signed": True } })
declarations.append({ "repr": { "name": "bool", "kind": "primitive", "c_type": "bool", "size_bits": 8, "signed": False } })
declarations.append({ "repr": { "name": "char*", "kind": "primitive", "c_type": "char*", "size_bits": 64, "signed": False } })
declarations.append({ "repr": { "name": "Color", "kind": "primitive", "c_type": "Color", "size_bits": 32, "signed": False } })

# Math Helpers
# We now rely on the compiler to translate these to C operators
def add_math_op(name, ret_type="Int32"):
    # Body must match the type signature: Int32 -> Int32 -> ret_type
    dummy_val = { "int32": 0 } if ret_type == "Int32" else { "bool": False }
    body = {
        "lambda": {
            "arg": { "name": "a", "type": { "prim": "Int32" } },
            "body": {
                "lambda": {
                    "arg": { "name": "b", "type": { "prim": "Int32" } },
                    "body": dummy_val
                }
            }
        }
    }
    
    declarations.append({
        "def": {
            "name": name,
            "role": "proof_only", 
            "type": {
                "pi": {
                    "arg": { "name": "a", "type": { "prim": "Int32" } },
                    "result": {
                        "pi": {
                            "arg": { "name": "b", "type": { "prim": "Int32" } },
                            "result": { "prim": ret_type }
                        }
                    }
                }
            },
            "body": body
        }
    })

add_math_op("add")
add_math_op("sub")
add_math_op("mul")
add_math_op("div")
add_math_op("lt", "Bool")
add_math_op("gt", "Bool")
add_math_op("eq", "Bool")

# Raylib FFI
declarations.append({
    "extern_io": {
        "name": "InitWindow",
        "c_name": "InitWindow",
        "header": "<raylib.h>",
        "args": [{ "name": "width", "repr": "int" }, { "name": "height", "repr": "int" }, { "name": "title", "repr": "char*" }],
        "result": None,
        "type": {
            "pi": {
                "arg": { "name": "width", "type": { "prim": "Int32" } },
                "result": {
                    "pi": {
                        "arg": { "name": "height", "type": { "prim": "Int32" } },
                        "result": {
                            "pi": {
                                "arg": { "name": "title", "type": { "prim": "String" } },
                                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
                            }
                        }
                    }
                }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "WindowShouldClose",
        "c_name": "WindowShouldClose",
        "header": "<raylib.h>",
        "args": [],
        "result": { "repr": "bool" },
        "type": {
            "pi": {
                "arg": { "name": "_", "type": { "var": "Unit" } },
                "result": { "app": [{ "var": "IO" }, { "prim": "Bool" }] }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "CloseWindow",
        "c_name": "CloseWindow",
        "header": "<raylib.h>",
        "args": [],
        "result": None,
        "type": {
            "pi": {
                "arg": { "name": "_", "type": { "var": "Unit" } },
                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "BeginDrawing",
        "c_name": "BeginDrawing",
        "header": "<raylib.h>",
        "args": [],
        "result": None,
        "type": {
            "pi": {
                "arg": { "name": "_", "type": { "var": "Unit" } },
                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "EndDrawing",
        "c_name": "EndDrawing",
        "header": "<raylib.h>",
        "args": [],
        "result": None,
        "type": {
            "pi": {
                "arg": { "name": "_", "type": { "var": "Unit" } },
                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "ClearBackground",
        "c_name": "ClearBackground",
        "header": "<raylib.h>",
        "args": [{ "name": "color", "repr": "Color" }],
        "result": None,
        "type": {
            "pi": {
                "arg": { "name": "color", "type": { "var": "Color" } },
                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
            }
        }
    }
})

declarations.append({
    "extern_c": {
        "name": "MakeColor_Wrapper",
        "c_name": "MakeColor_Wrapper",
        "header": "\"raylib_helper.h\"",
        "signature": {
            "args": [
                { "name": "r", "repr": "int" },
                { "name": "g", "repr": "int" },
                { "name": "b", "repr": "int" },
                { "name": "a", "repr": "int" }
            ],
            "return": { "repr": "Color" }
        },
        "type": {
            "pi": {
                "arg": { "name": "r", "type": { "prim": "Int32" } },
                "result": {
                    "pi": {
                        "arg": { "name": "g", "type": { "prim": "Int32" } },
                        "result": {
                            "pi": {
                                "arg": { "name": "b", "type": { "prim": "Int32" } },
                                "result": {
                                    "pi": {
                                        "arg": { "name": "a", "type": { "prim": "Int32" } },
                                        "result": { "var": "Color" }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "DrawRectangle",
        "c_name": "DrawRectangle",
        "header": "<raylib.h>",
        "args": [{ "name": "posX", "repr": "int" }, { "name": "posY", "repr": "int" }, { "name": "width", "repr": "int" }, { "name": "height", "repr": "int" }, { "name": "color", "repr": "Color" }],
        "result": None,
        "type": {
            "pi": {
                "arg": { "name": "posX", "type": { "prim": "Int32" } },
                "result": {
                    "pi": {
                        "arg": { "name": "posY", "type": { "prim": "Int32" } },
                        "result": {
                            "pi": {
                                "arg": { "name": "width", "type": { "prim": "Int32" } },
                                "result": {
                                    "pi": {
                                        "arg": { "name": "height", "type": { "prim": "Int32" } },
                                        "result": {
                                            "pi": {
                                                "arg": { "name": "color", "type": { "var": "Color" } },
                                                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "DrawText",
        "c_name": "DrawText",
        "header": "<raylib.h>",
        "args": [{ "name": "text", "repr": "char*" }, { "name": "posX", "repr": "int" }, { "name": "posY", "repr": "int" }, { "name": "fontSize", "repr": "int" }, { "name": "color", "repr": "Color" }],
        "result": None,
        "type": {
            "pi": {
                "arg": { "name": "text", "type": { "prim": "String" } },
                "result": {
                    "pi": {
                        "arg": { "name": "posX", "type": { "prim": "Int32" } },
                        "result": {
                            "pi": {
                                "arg": { "name": "posY", "type": { "prim": "Int32" } },
                                "result": {
                                    "pi": {
                                        "arg": { "name": "fontSize", "type": { "prim": "Int32" } },
                                        "result": {
                                            "pi": {
                                                "arg": { "name": "color", "type": { "var": "Color" } },
                                                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "IsKeyDown",
        "c_name": "IsKeyDown",
        "header": "<raylib.h>",
        "args": [{ "name": "key", "repr": "int" }],
        "result": { "repr": "bool" },
        "type": {
            "pi": {
                "arg": { "name": "key", "type": { "prim": "Int32" } },
                "result": { "app": [{ "var": "IO" }, { "prim": "Bool" }] }
            }
        }
    }
})

declarations.append({
    "extern_io": {
        "name": "SetTargetFPS",
        "c_name": "SetTargetFPS",
        "header": "<raylib.h>",
        "args": [{ "name": "fps", "repr": "int" }],
        "result": None,
        "type": {
            "pi": {
                "arg": { "name": "fps", "type": { "prim": "Int32" } },
                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
            }
        }
    }
})

declarations.append({
    "extern_c": {
        "name": "IntToString",
        "c_name": "IntToString",
        "header": "\"raylib_helper.h\"",
        "signature": {
            "args": [{ "name": "val", "repr": "int" }],
            "return": { "repr": "char*" }
        },
        "type": {
            "pi": {
                "arg": { "name": "val", "type": { "prim": "Int32" } },
                "result": { "prim": "String" }
            }
        }
    }
})

# Game Logic

# Constants
SCREEN_WIDTH = 800
SCREEN_HEIGHT = 450
PADDLE_WIDTH = 20
PADDLE_HEIGHT = 100
BALL_SIZE = 20
PADDLE_SPEED = 5
KEY_W = 87
KEY_S = 83
KEY_UP = 265
KEY_DOWN = 264

# loop(ball_x, ball_y, ball_dx, ball_dy, p1_y, p2_y, s1, s2)
loop_args = [
    ("ball_x", "Int32"), ("ball_y", "Int32"),
    ("ball_dx", "Int32"), ("ball_dy", "Int32"),
    ("p1_y", "Int32"), ("p2_y", "Int32"),
    ("s1", "Int32"), ("s2", "Int32")
]

def make_loop_type():
    t = {"app": [{"var": "IO"}, {"var": "Unit"}]}
    for name, ty in reversed(loop_args):
        t = {"pi": {"arg": {"name": name, "type": {"prim": ty}}, "result": t}}
    return t

def make_loop_lambda(body):
    l = body
    for name, ty in reversed(loop_args):
        l = {"lambda": {"arg": {"name": name, "type": {"prim": ty}}, "body": l}}
    return l

# Update Logic Construction
# We need to construct the next state values
# This is complex because we need to chain many IO actions (IsKeyDown) and pure calculations

# Helper to build nested binds
def bind_chain(actions, final_body):
    if not actions:
        return final_body
    
    typ_a, typ_b, m, arg_name, next_actions = actions[0]
    return bind(typ_a, typ_b, m, 
        lam(arg_name, typ_a, bind_chain(next_actions, final_body)))

# We will build the loop body
# 1. Check WindowShouldClose
# 2. If true, return
# 3. Else:
#    Read Inputs (W, S, UP, DOWN)
#    Update State
#    Draw
#    Recurse

# Let's rewrite the loop body generation using a helper
def generate_loop_body():
    # Input reading chain
    inputs = [
        ("key_w", KEY_W),
        ("key_s", KEY_S),
        ("key_up", KEY_UP),
        ("key_down", KEY_DOWN)
    ]
    
    def build_input_chain(idx):
        if idx >= len(inputs):
            return generate_update_draw_recurse()
        
        name, key = inputs[idx]
        return bind(prim("Bool"), unit(), 
            app(var("IsKeyDown"), [int32(key)]),
            lam(name, prim("Bool"), build_input_chain(idx + 1)))

    return bind(prim("Bool"), unit(),
        app(var("WindowShouldClose"), [tt()]),
        lam("should_close", prim("Bool"),
            {"if": {
                "cond": var("should_close"),
                "then": ret(unit(), tt()),
                "else": build_input_chain(0)
            }}
        ))

def generate_update_draw_recurse():
    # Logic to update state variables based on inputs and current state
    # We construct the new values as terms
    
    # Paddle 1 Update
    # if key_w then p1_y - speed else if key_s then p1_y + speed else p1_y
    p1_next = {
        "if": {
            "cond": var("key_w"),
            "then": app(var("sub"), [var("p1_y"), int32(PADDLE_SPEED)]),
            "else": {
                "if": {
                    "cond": var("key_s"),
                    "then": app(var("add"), [var("p1_y"), int32(PADDLE_SPEED)]),
                    "else": var("p1_y")
                }
            }
        }
    }
    
    # Paddle 2 Update
    p2_next = {
        "if": {
            "cond": var("key_up"),
            "then": app(var("sub"), [var("p2_y"), int32(PADDLE_SPEED)]),
            "else": {
                "if": {
                    "cond": var("key_down"),
                    "then": app(var("add"), [var("p2_y"), int32(PADDLE_SPEED)]),
                    "else": var("p2_y")
                }
            }
        }
    }
    
    # Ball Position Update
    ball_x_next = app(var("add"), [var("ball_x"), var("ball_dx")])
    ball_y_next = app(var("add"), [var("ball_y"), var("ball_dy")])
    
    # Ball Collision Logic (Simplified)
    # Wall Collision Y
    # if ball_y <= 0 or ball_y >= SCREEN_HEIGHT - BALL_SIZE then -ball_dy else ball_dy
    ball_dy_next = {
        "if": {
            "cond": app(var("lt"), [ball_y_next, int32(0)]),
            "then": app(var("sub"), [int32(0), var("ball_dy")]), # Negate
            "else": {
                "if": {
                    "cond": app(var("gt"), [ball_y_next, int32(SCREEN_HEIGHT - BALL_SIZE)]),
                    "then": app(var("sub"), [int32(0), var("ball_dy")]),
                    "else": var("ball_dy")
                }
            }
        }
    }
    
    # Paddle Collision X (Very simplified)
    # if ball_x <= PADDLE_WIDTH and ball_y >= p1_y and ball_y <= p1_y + PADDLE_HEIGHT then -ball_dx
    # else if ball_x >= SCREEN_WIDTH - PADDLE_WIDTH - BALL_SIZE and ball_y >= p2_y and ball_y <= p2_y + PADDLE_HEIGHT then -ball_dx
    # else ball_dx
    
    # Helper for AND
    def and_op(a, b): return {"if": {"cond": a, "then": b, "else": bool_lit(False)}}
    
    hit_p1 = and_op(
        app(var("lt"), [ball_x_next, int32(PADDLE_WIDTH)]),
        and_op(
            app(var("gt"), [ball_y_next, p1_next]),
            app(var("lt"), [ball_y_next, app(var("add"), [p1_next, int32(PADDLE_HEIGHT)])])
        )
    )
    
    hit_p2 = and_op(
        app(var("gt"), [ball_x_next, int32(SCREEN_WIDTH - PADDLE_WIDTH - BALL_SIZE)]),
        and_op(
            app(var("gt"), [ball_y_next, p2_next]),
            app(var("lt"), [ball_y_next, app(var("add"), [p2_next, int32(PADDLE_HEIGHT)])])
        )
    )
    
    ball_dx_next = {
        "if": {
            "cond": hit_p1,
            "then": app(var("sub"), [int32(0), var("ball_dx")]), # Should be abs(ball_dx) to force right
            "else": {
                "if": {
                    "cond": hit_p2,
                    "then": app(var("sub"), [int32(0), var("ball_dx")]), # Should be -abs(ball_dx) to force left
                    "else": var("ball_dx")
                }
            }
        }
    }
    
    # Score Update and Reset
    # if ball_x < 0 then s2 + 1, reset ball
    # if ball_x > SCREEN_WIDTH then s1 + 1, reset ball
    
    reset_ball = app(var("lt"), [ball_x_next, int32(0)])
    reset_ball_2 = app(var("gt"), [ball_x_next, int32(SCREEN_WIDTH)])
    
    final_ball_x = {
        "if": { "cond": reset_ball, "then": int32(SCREEN_WIDTH // 2), "else": {
            "if": { "cond": reset_ball_2, "then": int32(SCREEN_WIDTH // 2), "else": ball_x_next }
        }}
    }
    
    final_ball_y = {
        "if": { "cond": reset_ball, "then": int32(SCREEN_HEIGHT // 2), "else": {
            "if": { "cond": reset_ball_2, "then": int32(SCREEN_HEIGHT // 2), "else": ball_y_next }
        }}
    }
    
    final_s1 = {
        "if": { "cond": reset_ball_2, "then": app(var("add"), [var("s1"), int32(1)]), "else": var("s1") }
    }
    
    final_s2 = {
        "if": { "cond": reset_ball, "then": app(var("add"), [var("s2"), int32(1)]), "else": var("s2") }
    }
    
    # Drawing Logic
    # BeginDrawing -> ClearBackground -> DrawRect(p1) -> DrawRect(p2) -> DrawRect(ball) -> DrawText(s1) -> DrawText(s2) -> EndDrawing -> Recurse
    
    white = app(var("MakeColor_Wrapper"), [int32(255), int32(255), int32(255), int32(255)])
    black = app(var("MakeColor_Wrapper"), [int32(0), int32(0), int32(0), int32(255)])
    
    draw_seq = [
        app(var("BeginDrawing"), [tt()]),
        app(var("ClearBackground"), [black]),
        app(var("DrawRectangle"), [int32(10), p1_next, int32(PADDLE_WIDTH), int32(PADDLE_HEIGHT), white]),
        app(var("DrawRectangle"), [int32(SCREEN_WIDTH - 10 - PADDLE_WIDTH), p2_next, int32(PADDLE_WIDTH), int32(PADDLE_HEIGHT), white]),
        app(var("DrawRectangle"), [final_ball_x, final_ball_y, int32(BALL_SIZE), int32(BALL_SIZE), white]),
        app(var("DrawText"), [app(var("IntToString"), [final_s1]), int32(200), int32(20), int32(40), white]),
        app(var("DrawText"), [app(var("IntToString"), [final_s2]), int32(600), int32(20), int32(40), white]),
        app(var("EndDrawing"), [tt()]),
        app(var("loop"), [final_ball_x, final_ball_y, ball_dx_next, ball_dy_next, p1_next, p2_next, final_s1, final_s2])
    ]
    
    def build_draw_chain(idx):
        if idx >= len(draw_seq) - 1:
            return draw_seq[idx] # Last one is loop call
        
        return bind(unit(), unit(), draw_seq[idx], lam("_", unit(), build_draw_chain(idx + 1)))

    return build_draw_chain(0)

declarations.append({
    "def": {
        "name": "loop",
        "role": "runtime",
        "type": make_loop_type(),
        "body": make_loop_lambda(generate_loop_body())
    }
})

main_body = {
  "app": [
    { "var": "bind" }, { "var": "Unit" }, { "var": "Unit" },
    { "app": [{ "var": "InitWindow" }, { "int32": SCREEN_WIDTH }, { "int32": SCREEN_HEIGHT }, { "string": "CertiJSON Pong" }] },
    {
      "lambda": {
        "arg": { "name": "_", "type": { "var": "Unit" } },
        "body": {
          "app": [
            { "var": "bind" }, { "var": "Unit" }, { "var": "Unit" },
            { "app": [{ "var": "SetTargetFPS" }, { "int32": 60 }] },
            {
              "lambda": {
                "arg": { "name": "_", "type": { "var": "Unit" } },
                "body": {
                  "app": [
                    { "var": "bind" }, { "var": "Unit" }, { "var": "Unit" },
                    # Initial State: ball_x=400, ball_y=225, dx=5, dy=5, p1=175, p2=175, s1=0, s2=0
                    { "app": [{ "var": "loop" }, 
                        { "int32": 400 }, { "int32": 225 }, 
                        { "int32": 5 }, { "int32": 5 }, 
                        { "int32": 175 }, { "int32": 175 }, 
                        { "int32": 0 }, { "int32": 0 }] },
                    {
                      "lambda": {
                        "arg": { "name": "_", "type": { "var": "Unit" } },
                        "body": { "app": [{ "var": "CloseWindow" }, { "var": "tt" }] }
                      }
                    }
                  ]
                }
              }
            }
          ]
        }
      }
    }
  ]
}

declarations.append({
    "def": {
        "name": "main",
        "type": { "app": [{ "var": "IO" }, { "var": "Unit" }] },
        "body": main_body
    }
})

data = {
  "module": "Pong",
  "declarations": declarations
}

with open("examples/pong.json", "w") as f:
    json.dump(data, f, indent=2)
