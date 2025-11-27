(** Build runner - compiles ProofPy projects to executables *)

open Config

(** Runtime library paths *)
let runtime_dir = ref ""
let stdlib_dir = ref ""
let certijson_path = ref "certijson"

(** Find project root by walking up directory tree looking for dune-project *)
let find_project_root start_dir =
  let rec find_root dir depth =
    if depth > 10 then None
    else if Sys.file_exists (Filename.concat dir "dune-project") then Some dir
    else 
      let parent = Filename.dirname dir in
      if parent = dir then None else find_root parent (depth + 1)
  in
  (* First check if we're in a _build directory and go to its parent *)
  let dir = 
    if String.length start_dir > 6 then
      try
        let idx = Str.search_forward (Str.regexp_string "_build") start_dir 0 in
        String.sub start_dir 0 idx
      with Not_found -> start_dir
    else start_dir
  in
  find_root dir 0

(** Find the certijson executable *)
let find_certijson () =
  let exe_dir = Filename.dirname Sys.executable_name in
  let project_root = find_project_root exe_dir in
  
  let candidates = 
    (match project_root with 
     | Some root -> [Filename.concat root "_build/default/bin/main.exe"]
     | None -> []) @
    [
      Filename.concat exe_dir "certijson";
      Filename.concat exe_dir "../bin/certijson";
      Sys.getcwd () ^ "/_build/default/bin/main.exe";
      "certijson";  (* Fall back to PATH *)
    ]
  in
  List.find_opt (fun p -> 
    Sys.file_exists p || Sys.command (Printf.sprintf "which %s > /dev/null 2>&1" p) = 0
  ) candidates
  |> Option.value ~default:"certijson"

(** Find the runtime directory relative to the executable *)
let find_runtime_dir () =
  let exe_dir = Filename.dirname Sys.executable_name in
  let project_root = find_project_root exe_dir in
  
  let candidates = 
    (match project_root with 
     | Some root -> [Filename.concat root "runtime"]
     | None -> []) @
    [
      Sys.getcwd () ^ "/runtime";
      exe_dir ^ "/../runtime";
      exe_dir ^ "/runtime";
      "/usr/local/share/proofpy/runtime";
    ]
  in
  List.find_opt Sys.file_exists candidates
  |> Option.value ~default:(Sys.getcwd () ^ "/runtime")

(** Find the stdlib directory *)
let find_stdlib_dir () =
  let exe_dir = Filename.dirname Sys.executable_name in
  let project_root = find_project_root exe_dir in
  
  let candidates = 
    (match project_root with 
     | Some root -> [Filename.concat root "stdlib"]
     | None -> []) @
    [
      exe_dir ^ "/../stdlib";                (* installed location *)
      exe_dir ^ "/stdlib";                   (* alongside executable *)
      Sys.getcwd () ^ "/stdlib";             (* current directory *)
      "/usr/local/share/proofpy/stdlib";     (* system location *)
    ] 
  in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> 
      Printf.eprintf "warning: Could not find stdlib directory\n";
      Sys.getcwd () ^ "/stdlib"

(** Ensure directory exists *)
let ensure_dir dir =
  if not (Sys.file_exists dir) then
    Unix.mkdir dir 0o755

(** Verbose output flag *)
let verbose = ref false

(** Run a shell command and return exit code *)
let run_command cmd =
  if !verbose then Printf.printf "  %s\n" cmd;
  Sys.command cmd

(** Run a command, fail on error *)
let run_command_or_fail cmd =
  let code = run_command cmd in
  if code <> 0 then
    failwith (Printf.sprintf "Command failed with exit code %d: %s" code cmd)

(** Build steps *)
type build_step =
  | TypeCheck
  | Extract
  | Compile
  | Link

let step_name = function
  | TypeCheck -> "Checking"
  | Extract -> "Extracting"
  | Compile -> "Compiling"
  | Link -> "Linking"

(** Build context *)
type build_ctx = {
  config : config;
  project_dir : string;
  target_dir : string;
  c_file : string;
  obj_file : string;
  exe_file : string;
}

(** Create build context from config *)
let make_build_ctx config project_dir =
  let target_dir = Filename.concat project_dir config.build.output_dir in
  let base_name = Filename.remove_extension (Filename.basename config.package.entry_point) in
  {
    config;
    project_dir;
    target_dir;
    c_file = Filename.concat target_dir (base_name ^ ".c");
    obj_file = Filename.concat target_dir (base_name ^ ".o");
    exe_file = Filename.concat target_dir config.package.name;
  }

(** Collect all runtime C files *)
let runtime_c_files () =
  let dir = !runtime_dir in
  if Sys.file_exists dir then
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".c")
    |> List.map (Filename.concat dir)
  else []

(** Collect runtime object files (or compile them) *)
let get_runtime_objects ctx =
  let runtime_obj_dir = Filename.concat ctx.target_dir "runtime" in
  ensure_dir runtime_obj_dir;
  
  let c_files = runtime_c_files () in
  let obj_files = List.map (fun c_file ->
    let base = Filename.remove_extension (Filename.basename c_file) in
    let obj = Filename.concat runtime_obj_dir (base ^ ".o") in
    
    (* Check if we need to recompile *)
    let needs_compile = 
      not (Sys.file_exists obj) ||
      (Unix.stat c_file).Unix.st_mtime > (Unix.stat obj).Unix.st_mtime
    in
    
    if needs_compile then begin
      let cmd = Printf.sprintf "%s -c %s -o %s -I%s"
        ctx.config.build.compiler
        c_file
        obj
        !runtime_dir
      in
      run_command_or_fail cmd
    end;
    obj
  ) c_files in
  obj_files

(** Build the compiler flags *)
let build_cflags ctx =
  let opt = Printf.sprintf "-O%d" ctx.config.build.opt_level in
  let debug = if ctx.config.build.debug then ["-g"] else [] in
  let warnings = ctx.config.build.warnings in
  let includes = [
    Printf.sprintf "-I%s" !runtime_dir;
    Printf.sprintf "-I%s" ctx.target_dir;
  ] in
  let extra = ctx.config.build.extra_cflags in
  String.concat " " (opt :: debug @ warnings @ includes @ extra)

(** Build the linker flags *)
let build_ldflags ctx =
  let libs = List.map (fun lib ->
    if lib.lib_system then
      Printf.sprintf "-l%s" lib.lib_name
    else match lib.lib_path with
      | Some path -> path
      | None -> Printf.sprintf "-l%s" lib.lib_name
  ) ctx.config.libraries in
  let extra = ctx.config.build.extra_ldflags in
  String.concat " " (libs @ extra)

(** Type check the source file *)
let type_check ctx =
  Printf.printf "   %s %s\n" (step_name TypeCheck) ctx.config.package.entry_point;
  let entry = Filename.concat ctx.project_dir ctx.config.package.entry_point in
  let quiet = if !verbose then "" else "-q " in
  let cmd = Printf.sprintf "%s check %s-I %s %s" !certijson_path quiet !stdlib_dir entry in
  run_command cmd

(** Extract to C *)
let extract ctx =
  Printf.printf "   %s %s -> %s\n" (step_name Extract) 
    ctx.config.package.entry_point 
    (Filename.basename ctx.c_file);
  let entry = Filename.concat ctx.project_dir ctx.config.package.entry_point in
  let cmd = Printf.sprintf "%s extract -I %s %s > %s" !certijson_path !stdlib_dir entry ctx.c_file in
  run_command cmd

(** Compile C to object file *)
let compile ctx =
  Printf.printf "   %s %s\n" (step_name Compile) (Filename.basename ctx.c_file);
  let cflags = build_cflags ctx in
  let cmd = Printf.sprintf "%s %s -c %s -o %s"
    ctx.config.build.compiler
    cflags
    ctx.c_file
    ctx.obj_file
  in
  run_command cmd

(** Link to executable *)
let link ctx =
  Printf.printf "   %s %s\n" (step_name Link) ctx.config.package.name;
  let runtime_objs = get_runtime_objects ctx in
  let ldflags = build_ldflags ctx in
  let all_objs = ctx.obj_file :: runtime_objs in
  let cmd = Printf.sprintf "%s %s -o %s %s"
    ctx.config.build.compiler
    (String.concat " " all_objs)
    ctx.exe_file
    ldflags
  in
  run_command cmd

(** Full build pipeline *)
let build config project_dir =
  certijson_path := find_certijson ();
  runtime_dir := find_runtime_dir ();
  stdlib_dir := find_stdlib_dir ();
  
  let ctx = make_build_ctx config project_dir in
  
  Printf.printf "   Building %s v%s\n" config.package.name config.package.version;
  
  (* Ensure target directory exists *)
  ensure_dir ctx.target_dir;
  
  (* Run build steps *)
  let check_result = type_check ctx in
  if check_result <> 0 then begin
    Printf.printf "error: Type checking failed\n";
    exit 1
  end;
  
  let extract_result = extract ctx in
  if extract_result <> 0 then begin
    Printf.printf "error: Extraction failed\n";
    exit 1
  end;
  
  let compile_result = compile ctx in
  if compile_result <> 0 then begin
    Printf.printf "error: Compilation failed\n";
    exit 1
  end;
  
  let link_result = link ctx in
  if link_result <> 0 then begin
    Printf.printf "error: Linking failed\n";
    exit 1
  end;
  
  Printf.printf "    Finished release target in %s\n" ctx.target_dir;
  ctx.exe_file

(** Build and run *)
let run config project_dir args =
  let exe = build config project_dir in
  Printf.printf "     Running `%s`\n" exe;
  let cmd = 
    if args = [] then exe
    else Printf.sprintf "%s %s" exe (String.concat " " args)
  in
  let code = Sys.command cmd in
  exit code

(** Clean build artifacts *)
let clean config project_dir =
  let target_dir = Filename.concat project_dir config.build.output_dir in
  if Sys.file_exists target_dir then begin
    Printf.printf "   Cleaning %s\n" target_dir;
    let cmd = Printf.sprintf "rm -rf %s" target_dir in
    ignore (Sys.command cmd)
  end

(** Initialize a new project *)
let init_project name =
  Printf.printf "     Creating project `%s`\n" name;
  
  (* Create directory structure *)
  Unix.mkdir name 0o755;
  Unix.mkdir (Filename.concat name "src") 0o755;
  
  (* Create ProofPy.toml *)
  let toml_path = Filename.concat name "ProofPy.toml" in
  let oc = open_out toml_path in
  output_string oc (default_toml_content name);
  close_out oc;
  Printf.printf "      Created %s\n" toml_path;
  
  (* Create main.cj *)
  let main_path = Filename.concat (Filename.concat name "src") "main.cj" in
  let oc = open_out main_path in
  output_string oc (Printf.sprintf {|# %s - A ProofPy project

import Std.Nat
import Std.IO

# Main entry point
def main() -> IO(Unit):
    return print_line("Hello from %s!")
|} name name);
  close_out oc;
  Printf.printf "      Created %s\n" main_path;
  
  Printf.printf "     Created project `%s`\n" name;
  Printf.printf "\n  To build: cd %s && proofpy build\n" name;
  Printf.printf "  To run:   cd %s && proofpy run\n" name
