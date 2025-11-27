(** CertiJSON compiler command-line interface. *)

open Cmdliner

module CJ = Certijson

(** Common arguments *)
let include_paths =
  let doc = "Add directory to include search path." in
  Arg.(value & opt_all dir [] & info ["I"; "include"] ~docv:"DIR" ~doc)

let quiet_flag =
  let doc = "Suppress informational output." in
  Arg.(value & flag & info ["q"; "quiet"] ~doc)

let make_config includes =
  let base_paths = CJ.Loader.default_config.include_paths in
  { CJ.Loader.include_paths = includes @ base_paths }

(** {1 Commands} *)

let check_cmd =
  let file =
    let doc = "The CertiJSON source file to check." in
    Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let check quiet includes file =
    let config = make_config includes in
    match CJ.Loader.parse_file file with
    | Error (CJ.Loader.ParseError e) ->
        let err = CJ.Error.error_of_parse ~file e in
        Fmt.epr "%a@." CJ.Error.pp_error err;
        `Error (false, "parsing failed")
    | Error e ->
        Fmt.epr "%a@." CJ.Loader.pp_error e;
        `Error (false, "parsing failed")
    | Ok mod_ ->
        if not quiet then begin
          Fmt.pr "Parsed module: %s@." mod_.module_name;
          Fmt.pr "Imports: %a@."
            Fmt.(list ~sep:comma string) mod_.imports;
          Fmt.pr "Declarations: %d@." (List.length mod_.declarations)
        end;
        let cache = CJ.Loader.create_cache () in
        match CJ.Loader.load_imports config cache [mod_.module_name] mod_ with
        | Error e ->
            Fmt.epr "%a@." CJ.Loader.pp_error e;
            `Error (false, "type checking failed")
        | Ok _sig ->
            if not quiet then
              Fmt.pr "✓ Module type-checked successfully@.";
            `Ok ()
  in
  let doc = "Type-check a CertiJSON source file." in
  let info = Cmd.info "check" ~doc in
  Cmd.v info Term.(ret (const check $ quiet_flag $ include_paths $ file))

let parse_cmd =
  let file =
    let doc = "The CertiJSON source file to parse." in
    Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let parse file =
    match CJ.Loader.parse_file file with
    | Error (CJ.Loader.ParseError e) ->
        let err = CJ.Error.error_of_parse ~file e in
        Fmt.epr "%a@." CJ.Error.pp_error err;
        `Error (false, "parsing failed")
    | Error e ->
        Fmt.epr "%a@." CJ.Loader.pp_error e;
        `Error (false, "parsing failed")
    | Ok mod_ ->
        Fmt.pr "%s@." (CJ.Pretty.module_to_string mod_);
        `Ok ()
  in
  let doc = "Parse and pretty-print a CertiJSON source file." in
  let info = Cmd.info "parse" ~doc in
  Cmd.v info Term.(ret (const parse $ file))

let eval_cmd =
  let file =
    let doc = "The CertiJSON source file containing the term to evaluate." in
    Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let def_name =
    let doc = "The name of the definition to evaluate." in
    Arg.(required & pos 1 (some string) None & info [] ~docv:"NAME" ~doc)
  in
  let do_eval includes file def_name =
    let config = make_config includes in
    match CJ.Loader.parse_file file with
    | Error (CJ.Loader.ParseError e) ->
        let err = CJ.Error.error_of_parse ~file e in
        Fmt.epr "%a@." CJ.Error.pp_error err;
        `Error (false, "parsing failed")
    | Error e ->
        Fmt.epr "%a@." CJ.Loader.pp_error e;
        `Error (false, "parsing failed")
    | Ok mod_ ->
        let cache = CJ.Loader.create_cache () in
        match CJ.Loader.load_imports config cache [mod_.module_name] mod_ with
        | Error e ->
            Fmt.epr "%a@." CJ.Loader.pp_error e;
            `Error (false, "type checking failed")
        | Ok sig_ ->
            let ctx = CJ.Context.make_ctx sig_ in
            let term = CJ.Syntax.mk (CJ.Syntax.Global def_name) in
            let result = CJ.Eval.normalize ctx term in
            Fmt.pr "%s@." (CJ.Pretty.term_to_string result);
            `Ok ()
  in
  let doc = "Evaluate a definition from a CertiJSON source file." in
  let cmd_info = Cmd.info "eval" ~doc in
  Cmd.v cmd_info Term.(ret (const do_eval $ include_paths $ file $ def_name))

let run_cmd =
  let file =
    let doc = "The CertiJSON source file to run." in
    Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let def_name =
    let doc = "The name of the IO definition to run (default: main)." in
    Arg.(value & opt string "main" & info ["entry"] ~docv:"NAME" ~doc)
  in
  let do_run includes file def_name =
    let config = make_config includes in
    match CJ.Loader.parse_file file with
    | Error (CJ.Loader.ParseError e) ->
        let err = CJ.Error.error_of_parse ~file e in
        Fmt.epr "%a@." CJ.Error.pp_error err;
        `Error (false, "parsing failed")
    | Error e ->
        Fmt.epr "%a@." CJ.Loader.pp_error e;
        `Error (false, "parsing failed")
    | Ok mod_ ->
        let cache = CJ.Loader.create_cache () in
        match CJ.Loader.load_imports config cache [mod_.module_name] mod_ with
        | Error e ->
            Fmt.epr "%a@." CJ.Loader.pp_error e;
            `Error (false, "type checking failed")
        | Ok sig_ ->
            let ctx = CJ.Context.make_ctx sig_ in
            let term = CJ.Syntax.mk (CJ.Syntax.Global def_name) in
            try
              CJ.Eval.run_io ctx term;
              `Ok ()
            with e ->
              Fmt.epr "Runtime error: %s@." (Printexc.to_string e);
              `Error (false, "runtime error")
  in
  let doc = "Run a CertiJSON IO program." in
  let info = Cmd.info "run" ~doc in
  Cmd.v info Term.(ret (const do_run $ include_paths $ file $ def_name))

let extract_cmd =
  let file =
    let doc = "The CertiJSON source file to extract." in
    Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)
  in
  let do_extract includes file =
    let config = make_config includes in
    match CJ.Loader.parse_file file with
    | Error (CJ.Loader.ParseError e) ->
        let err = CJ.Error.error_of_parse ~file e in
        Fmt.epr "%a@." CJ.Error.pp_error err;
        `Error (false, "parsing failed")
    | Error e ->
        Fmt.epr "%a@." CJ.Loader.pp_error e;
        `Error (false, "parsing failed")
    | Ok mod_ ->
        let cache = CJ.Loader.create_cache () in
        match CJ.Loader.load_imports config cache [mod_.module_name] mod_ with
        | Error e ->
            Fmt.epr "%a@." CJ.Loader.pp_error e;
            `Error (false, "type checking failed")
        | Ok sig_ ->
            let prog = CJ.Extraction.extract_module mod_ sig_ in
            CJ.Extraction.pp_c_program Format.std_formatter prog;
            `Ok ()
  in
  let doc = "Extract a CertiJSON file to C." in
  let info = Cmd.info "extract" ~doc in
  Cmd.v info Term.(ret (const do_extract $ include_paths $ file))

(** {1 Main} *)

let () =
  let doc = "A proof-based programming language for agentic LLMs" in
  let info = Cmd.info "certijson" ~version:"0.1.0" ~doc in
  let cmds = [check_cmd; parse_cmd; eval_cmd; run_cmd; extract_cmd] in
  exit (Cmd.eval (Cmd.group info cmds))
