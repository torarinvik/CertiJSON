def safe_div(x: Int32, y: {v: Int32 | v != 0}) -> Int32:
    return x / y
