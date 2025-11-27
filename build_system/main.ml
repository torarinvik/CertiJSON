(** ProofPy Build System - Main CLI *)

open Build_system.Config
open Build_system.Builder

let version = "0.1.0"

let usage = {|ProofPy Build System

Usage: proofpy <command> [options]

Commands:
  new <name>     Create a new ProofPy project
  build          Build the current project
  run [args]     Build and run the current project
  check          Type-check the current project
  clean          Remove build artifacts
  extract        Extract to C without compiling
  help           Show this help message

Options:
  --release      Build with optimizations (default)
  --debug        Build with debug symbols
  -v, --verbose  Show verbose output
  --version      Show version

Examples:
  proofpy new my_game       Create a new project called my_game
  proofpy build             Build the current project
  proofpy run               Build and run
  proofpy run -- arg1 arg2  Run with arguments
|}

(** Find ProofPy.toml in current or parent directories *)
let find_project_root () =
  let rec search dir depth =
    if depth > 10 then None
    else
      let toml = Filename.concat dir "ProofPy.toml" in
      if Sys.file_exists toml then Some dir
      else
        let parent = Filename.dirname dir in
        if parent = dir then None
        else search parent (depth + 1)
  in
  search (Sys.getcwd ()) 0

(** Load project configuration *)
let load_project () =
  match find_project_root () with
  | None ->
      Printf.eprintf "error: Could not find ProofPy.toml in current or parent directories\n";
      Printf.eprintf "hint: Run `proofpy new <name>` to create a new project\n";
      exit 1
  | Some dir ->
      let toml = Filename.concat dir "ProofPy.toml" in
      let config = load_config toml in
      (config, dir)

(** Command: new *)
let cmd_new args =
  match args with
  | [] ->
      Printf.eprintf "error: Missing project name\n";
      Printf.eprintf "usage: proofpy new <name>\n";
      exit 1
  | name :: _ ->
      if Sys.file_exists name then begin
        Printf.eprintf "error: Directory `%s` already exists\n" name;
        exit 1
      end;
      init_project name

(** Command: build *)
let cmd_build _args =
  let config, dir = load_project () in
  ignore (build config dir)

(** Command: run *)
let cmd_run args =
  let config, dir = load_project () in
  (* Split args at -- if present *)
  let prog_args = 
    match List.find_index (fun a -> a = "--") args with
    | None -> []
    | Some idx -> 
        let after = List.filteri (fun i _ -> i > idx) args in
        after
  in
  run config dir prog_args

(** Command: check *)
let cmd_check _args =
  let config, dir = load_project () in
  let entry = Filename.concat dir config.package.entry_point in
  let certijson = find_certijson () in
  let stdlib = find_stdlib_dir () in
  Printf.printf "   Checking %s\n" config.package.name;
  let cmd = Printf.sprintf "%s check -I %s %s" certijson stdlib entry in
  let code = Sys.command cmd in
  if code = 0 then
    Printf.printf "    Finished type checking\n"
  else
    exit code

(** Command: clean *)
let cmd_clean _args =
  let config, dir = load_project () in
  clean config dir

(** Command: extract *)
let cmd_extract _args =
  let config, dir = load_project () in
  let entry = Filename.concat dir config.package.entry_point in
  let target_dir = Filename.concat dir config.build.output_dir in
  let certijson = find_certijson () in
  let stdlib = find_stdlib_dir () in
  
  if not (Sys.file_exists target_dir) then
    Unix.mkdir target_dir 0o755;
  
  let base_name = Filename.remove_extension (Filename.basename config.package.entry_point) in
  let c_file = Filename.concat target_dir (base_name ^ ".c") in
  
  Printf.printf "   Extracting %s -> %s\n" config.package.entry_point c_file;
  let cmd = Printf.sprintf "%s extract -I %s %s > %s" certijson stdlib entry c_file in
  let code = Sys.command cmd in
  if code = 0 then
    Printf.printf "    Finished extraction\n"
  else
    exit code

(** Main entry point *)
let main () =
  let args = Array.to_list Sys.argv |> List.tl in
  match args with
  | [] | ["help"] | ["-h"] | ["--help"] ->
      print_string usage
  | ["--version"] | ["-V"] ->
      Printf.printf "proofpy %s\n" version
  | "new" :: rest ->
      cmd_new rest
  | "build" :: rest ->
      cmd_build rest
  | "run" :: rest ->
      cmd_run rest
  | "check" :: rest ->
      cmd_check rest
  | "clean" :: rest ->
      cmd_clean rest
  | "extract" :: rest ->
      cmd_extract rest
  | cmd :: _ ->
      Printf.eprintf "error: Unknown command `%s`\n" cmd;
      Printf.eprintf "Run `proofpy help` for usage\n";
      exit 1

let () = main ()
