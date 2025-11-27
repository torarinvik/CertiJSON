(** Build configuration types and TOML parser for ProofPy.toml 
    Uses the 'toml' opam library for standards-compliant parsing *)

(** Package metadata *)
type package = {
  name : string;
  version : string;
  authors : string list;
  description : string option;
  license : string option;
  entry_point : string;  (* Main .cj file *)
}

(** Build settings *)
type build = {
  compiler : string;           (* C compiler: gcc, clang, tcc *)
  opt_level : int;             (* 0, 1, 2, 3 *)
  debug : bool;                (* Include debug symbols *)
  warnings : string list;      (* Compiler warnings to enable *)
  extra_cflags : string list;  (* Additional C compiler flags *)
  extra_ldflags : string list; (* Additional linker flags *)
  output_dir : string;         (* Output directory for binaries *)
}

(** Dependency specification *)
type dependency = {
  dep_name : string;
  dep_version : string option;
  dep_path : string option;    (* Local path dependency *)
  dep_git : string option;     (* Git repository *)
}

(** Library to link *)
type library = {
  lib_name : string;
  lib_path : string option;    (* Custom path to library *)
  lib_system : bool;           (* Is it a system library? *)
}

(** Full project configuration *)
type config = {
  package : package;
  build : build;
  dependencies : dependency list;
  libraries : library list;
  stdlib_imports : string list;  (* Standard library modules to include *)
}

(** Default build configuration *)
let default_build = {
  compiler = "clang";
  opt_level = 2;
  debug = false;
  warnings = ["-Wall"; "-Wextra"];
  extra_cflags = [];
  extra_ldflags = [];
  output_dir = "target";
}

(** Default package configuration *)
let default_package name = {
  name;
  version = "0.1.0";
  authors = [];
  description = None;
  license = None;
  entry_point = "src/main.cj";
}

(** TOML value helpers using the toml library *)
module TomlHelpers = struct
  open Toml.Types

  let get_string table key default =
    match Table.find_opt (Toml.Min.key key) table with
    | Some (TString s) -> s
    | _ -> default

  let get_string_opt table key =
    match Table.find_opt (Toml.Min.key key) table with
    | Some (TString s) -> Some s
    | _ -> None

  let get_int table key default =
    match Table.find_opt (Toml.Min.key key) table with
    | Some (TInt i) -> i
    | _ -> default

  let get_bool table key default =
    match Table.find_opt (Toml.Min.key key) table with
    | Some (TBool b) -> b
    | _ -> default

  let get_string_list table key default =
    match Table.find_opt (Toml.Min.key key) table with
    | Some (TArray (NodeString arr)) -> arr
    | _ -> default

  let get_table toml key =
    match Toml.Types.Table.find_opt (Toml.Min.key key) toml with
    | Some (TTable t) -> Some t
    | _ -> None
end

(** Load configuration from ProofPy.toml *)
let load_config filename : config =
  let open TomlHelpers in
  
  let toml = match Toml.Parser.from_filename filename with
    | `Ok table -> table
    | `Error (msg, _loc) -> failwith (Printf.sprintf "TOML parse error: %s" msg)
  in
  
  let pkg_table = match get_table toml "package" with
    | Some t -> t
    | None -> Toml.Types.Table.empty
  in
  
  let build_table = match get_table toml "build" with
    | Some t -> t
    | None -> Toml.Types.Table.empty
  in
  
  let package = {
    name = get_string pkg_table "name" "unnamed";
    version = get_string pkg_table "version" "0.1.0";
    authors = get_string_list pkg_table "authors" [];
    description = get_string_opt pkg_table "description";
    license = get_string_opt pkg_table "license";
    entry_point = get_string pkg_table "entry_point" "src/main.cj";
  } in
  
  let build = {
    compiler = get_string build_table "compiler" default_build.compiler;
    opt_level = get_int build_table "opt_level" default_build.opt_level;
    debug = get_bool build_table "debug" default_build.debug;
    warnings = get_string_list build_table "warnings" default_build.warnings;
    extra_cflags = get_string_list build_table "cflags" [];
    extra_ldflags = get_string_list build_table "ldflags" [];
    output_dir = get_string build_table "output_dir" default_build.output_dir;
  } in
  
  (* Parse dependencies section *)
  let dependencies = match get_table toml "dependencies" with
    | None -> []
    | Some deps_table ->
        Toml.Types.Table.fold (fun key value acc ->
          let name = Toml.Types.Table.Key.to_string key in
          match value with
          | Toml.Types.TString version -> 
              { dep_name = name; dep_version = Some version; dep_path = None; dep_git = None } :: acc
          | Toml.Types.TTable inner ->
              let path = get_string_opt inner "path" in
              let git = get_string_opt inner "git" in
              let version = get_string_opt inner "version" in
              { dep_name = name; dep_version = version; dep_path = path; dep_git = git } :: acc
          | _ -> acc
        ) deps_table []
  in
  
  (* Parse libraries section *)
  let libraries = match get_table toml "libraries" with
    | None -> []
    | Some libs_table ->
        Toml.Types.Table.fold (fun key value acc ->
          let name = Toml.Types.Table.Key.to_string key in
          match value with
          | Toml.Types.TBool true -> 
              { lib_name = name; lib_path = None; lib_system = true } :: acc
          | Toml.Types.TString path -> 
              { lib_name = name; lib_path = Some path; lib_system = false } :: acc
          | Toml.Types.TTable inner ->
              let path = get_string_opt inner "path" in
              let system = get_bool inner "system" false in
              { lib_name = name; lib_path = path; lib_system = system } :: acc
          | _ -> acc
        ) libs_table []
  in
  
  let stdlib_imports = get_string_list pkg_table "stdlib" ["Std.Nat"; "Std.Bool"] in
  
  { package; build; dependencies; libraries; stdlib_imports }

(** Create default ProofPy.toml content *)
let default_toml_content name =
  Printf.sprintf {|# ProofPy Project Configuration
# Similar to Cargo.toml for Rust projects

[package]
name = "%s"
version = "0.1.0"
authors = []
description = "A ProofPy project"
entry_point = "src/main.cj"
stdlib = ["Std.Nat", "Std.Bool", "Std.Int"]

[build]
# C compiler to use: gcc, clang, tcc
compiler = "clang"

# Optimization level: 0 (none), 1 (basic), 2 (default), 3 (aggressive)
opt_level = 2

# Include debug symbols
debug = false

# Compiler warnings
warnings = ["-Wall", "-Wextra"]

# Additional C compiler flags
cflags = []

# Additional linker flags
ldflags = []

# Output directory for compiled binaries
output_dir = "target"

[dependencies]
# Dependencies from the ProofPy package registry
# example_lib = "1.0.0"
# local_lib = { path = "../my_lib" }

[libraries]
# System libraries to link
# raylib = true
# sdl2 = true
# Custom library paths
# mylib = "/path/to/libmylib.a"
|} name

(** Print configuration for debugging *)
let print_config cfg =
  Printf.printf "Package: %s v%s\n" cfg.package.name cfg.package.version;
  Printf.printf "Entry point: %s\n" cfg.package.entry_point;
  Printf.printf "Compiler: %s -O%d%s\n" 
    cfg.build.compiler 
    cfg.build.opt_level
    (if cfg.build.debug then " (debug)" else "");
  Printf.printf "Output: %s/\n" cfg.build.output_dir;
  if cfg.libraries <> [] then begin
    Printf.printf "Libraries:\n";
    List.iter (fun lib -> Printf.printf "  - %s\n" lib.lib_name) cfg.libraries
  end
