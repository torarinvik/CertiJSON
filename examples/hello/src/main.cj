# Hello World - A simple ProofPy program

import Std.Nat
import Std.IO

# A simple greeting
def greet() -> IO(Unit):
    return print_line("Hello from ProofPy!")

# Main entry point
def main() -> IO(Unit):
    return greet()
