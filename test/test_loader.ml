(** Loader tests for CertiJSON. *)

open Alcotest
open Certijson

let test_custom_module_loading () =
  (* Create a temporary directory for custom modules *)
  let tmp_dir = Filename.temp_file "certijson_test" "" in
  Sys.remove tmp_dir;
  Sys.mkdir tmp_dir 0o755;
  
  let module_name = "CustomMod" in
  let filename = "CustomMod.json" in
  let path = Filename.concat tmp_dir filename in
  
  let json = {|
    {
      "module": "CustomMod",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "x",
            "role": "runtime",
            "type": { "universe": "Type" },
            "body": { "universe": "Type" }
          }
        }
      ]
    }
  |} in
  
  let oc = open_out path in
  output_string oc json;
  close_out oc;
  
  let config = { Loader.include_paths = [tmp_dir] } in
  let cache = Loader.create_cache () in
  
  let result = Loader.load_module config cache [] module_name in
  
  (* Cleanup *)
  Sys.remove path;
  Sys.rmdir tmp_dir;
  
  match result with
  | Ok _ -> ()
  | Error e -> fail (Format.asprintf "%a" Loader.pp_error e)

let test_stdlib_loading () =
  (* We try to locate stdlib relative to the build directory *)
  (* Tests run in _build/default/test, so stdlib is at ../../stdlib *)
  let stdlib_path = "../../../stdlib" in
  
  (* Check if directory exists to be safe, though we expect it to *)
  if not (Sys.file_exists stdlib_path && Sys.is_directory stdlib_path) then
    fail "stdlib directory not found at ../../stdlib";

  let config = { Loader.include_paths = [stdlib_path] } in
  let cache = Loader.create_cache () in
  
  (* Try to load a simple module like Std.Bool *)
  match Loader.load_module config cache [] "Std.Bool" with
  | Ok _ -> ()
  | Error e -> fail (Format.asprintf "%a" Loader.pp_error e)

let () =
  run "Loader" [
    "custom", [
      test_case "load custom module" `Quick test_custom_module_loading;
      test_case "load stdlib" `Quick test_stdlib_loading;
    ]
  ]
