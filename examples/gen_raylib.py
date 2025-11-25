import json

loop_body = {
  "lambda": {
    "arg": { "name": "_", "type": { "var": "Unit" } },
    "body": {
      "app": [
        { "var": "bind" }, { "prim": "Bool" }, { "var": "Unit" },
        { "app": [{ "var": "WindowShouldClose" }, { "var": "tt" }] },
        {
          "lambda": {
            "arg": { "name": "should_close", "type": { "prim": "Bool" } },
            "body": {
              "if": {
                "cond": { "var": "should_close" },
                "then": { "app": [{ "var": "return" }, { "var": "Unit" }, { "var": "tt" }] },
                "else": {
                  "app": [
                    { "var": "bind" }, { "var": "Unit" }, { "var": "Unit" },
                    { "app": [{ "var": "BeginDrawing" }, { "var": "tt" }] },
                    {
                      "lambda": {
                        "arg": { "name": "_", "type": { "var": "Unit" } },
                        "body": {
                          "app": [
                            { "var": "bind" }, { "var": "Unit" }, { "var": "Unit" },
                            { "app": [{ "var": "ClearBackground" }, { "app": [{ "var": "MakeColor_Wrapper" }, { "int32": 255 }, { "int32": 255 }, { "int32": 255 }, { "int32": 255 }] }] },
                            {
                              "lambda": {
                                "arg": { "name": "_", "type": { "var": "Unit" } },
                                "body": {
                                  "app": [
                                    { "var": "bind" }, { "var": "Unit" }, { "var": "Unit" },
                                    { "app": [{ "var": "EndDrawing" }, { "var": "tt" }] },
                                    {
                                      "lambda": {
                                        "arg": { "name": "_", "type": { "var": "Unit" } },
                                        "body": { "app": [{ "var": "loop" }, { "var": "tt" }] }
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
              }
            }
          }
        }
      ]
    }
  }
}

main_body = {
  "app": [
    { "var": "bind" }, { "var": "Unit" }, { "var": "Unit" },
    { "app": [{ "var": "InitWindow" }, { "int32": 800 }, { "int32": 450 }, { "string": "CertiJSON Raylib" }] },
    {
      "lambda": {
        "arg": { "name": "_", "type": { "var": "Unit" } },
        "body": {
          "app": [
            { "var": "bind" }, { "var": "Unit" }, { "var": "Unit" },
            { "app": [{ "var": "loop" }, { "var": "tt" }] },
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

declarations = []

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

declarations.append({
    "repr": {
        "name": "int",
        "kind": "primitive",
        "c_type": "int",
        "size_bits": 32,
        "signed": True
    }
})

declarations.append({
    "repr": {
        "name": "bool",
        "kind": "primitive",
        "c_type": "bool",
        "size_bits": 8,
        "signed": False
    }
})

declarations.append({
    "repr": {
        "name": "char*",
        "kind": "primitive",
        "c_type": "char*",
        "size_bits": 64,
        "signed": False
    }
})

declarations.append({
    "repr": {
        "name": "unsigned char",
        "kind": "primitive",
        "c_type": "unsigned char",
        "size_bits": 8,
        "signed": False
    }
})

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
    "repr": {
        "name": "Color",
        "kind": "primitive",
        "c_type": "Color",
        "size_bits": 32,
        "signed": False
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
    "def": {
        "name": "loop",
        "role": "runtime",
        "type": {
            "pi": {
                "arg": { "name": "_", "type": { "var": "Unit" } },
                "result": { "app": [{ "var": "IO" }, { "var": "Unit" }] }
            }
        },
        "body": loop_body
    }
})

declarations.append({
    "def": {
        "name": "main",
        "type": { "app": [{ "var": "IO" }, { "var": "Unit" }] },
        "body": main_body
    }
})

data = {
  "module": "RaylibReal",
  "declarations": declarations
}

with open("examples/raylib_real.json", "w") as f:
    json.dump(data, f, indent=2)
