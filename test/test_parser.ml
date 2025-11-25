(** Parser tests for CertiJSON. *)

open Alcotest
open Certijson

module Loc = Certijson.Loc

let test_minimal_module () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": []
    }
  |} in
  match Json_parser.parse_string json with
  | Ok m ->
      check string "module name" "Test" m.Syntax.module_name;
      check (list string) "imports" [] m.imports;
      check int "declarations" 0 (List.length m.declarations)
  | Error e ->
      fail (Json_parser.show_parse_error e)

let test_variable () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "id",
            "type": {
              "pi": {
                "arg": { "name": "A", "type": { "universe": "Type" } },
                "result": {
                  "pi": {
                    "arg": { "name": "x", "type": { "var": "A" } },
                    "result": { "var": "A" }
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
                    "body": { "var": "x" }
                  }
                }
              }
            }
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Ok m ->
      check string "module name" "Test" m.Syntax.module_name;
      check int "declarations" 1 (List.length m.declarations)
  | Error e ->
      fail (Json_parser.show_parse_error e)

let test_inductive () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "inductive": {
            "name": "Nat",
            "params": [],
            "universe": "Type",
            "constructors": [
              { "name": "zero", "args": [] },
              { "name": "succ", "args": [{ "name": "n", "type": { "var": "Nat" } }] }
            ]
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Ok m ->
      check int "declarations" 1 (List.length m.declarations);
      (match List.hd m.declarations with
      | Syntax.Inductive ind ->
          check string "inductive name" "Nat" ind.ind_name;
          check int "constructors" 2 (List.length ind.constructors)
      | _ -> fail "expected inductive declaration")
  | Error e ->
      fail (Json_parser.show_parse_error e)

let test_literals () =
  let json = {|
    {
      "module": "Test",
      "imports": [],
      "declarations": [
        {
          "def": {
            "name": "forty_two",
            "type": { "var": "Int32" },
            "body": { "int32": 42 }
          }
        }
      ]
    }
  |} in
  match Json_parser.parse_string json with
  | Ok m ->
      check int "declarations" 1 (List.length m.declarations)
  | Error e ->
      fail (Json_parser.show_parse_error e)

(** {1 Location Tests} *)

let check_loc = check (option (testable Loc.pp Loc.equal)) "loc"

(** [expect_loc got expected] checks that [got] matches [expected]. *)
let expect_loc expected got = check_loc expected got

let test_term_locations () =
  let json = {|{
  "module": "Test",
  "imports": [],
  "declarations": [
    {
      "def": {
        "name": "id",
        "type": { "var": "A" },
        "body": { "var": "x" }
      }
    }
  ]
}|} in
  match Json_parser.parse_string json with
  | Ok m ->
      (match List.hd m.declarations with
      | Syntax.Definition def ->
          (* "type": { "var": "A" } starts at line 8, column 17 *)
          expect_loc (Some { file = None; line = Some 8; column = Some 17 }) def.def_type.loc;
          (* "body": { "var": "x" } starts at line 9, column 17 *)
          expect_loc (Some { file = None; line = Some 9; column = Some 17 }) def.def_body.loc
      | _ -> fail "expected definition")
  | Error e -> fail (Json_parser.show_parse_error e)

let test_lambda_locations () =
  let json = {|{
  "module": "Test",
  "imports": [],
  "declarations": [
    {
      "def": {
        "name": "id",
        "type": { "var": "A" },
        "body": {
          "lambda": {
            "arg": { "name": "x", "type": { "var": "A" } },
            "body": { "var": "x" }
          }
        }
      }
    }
  ]
}|} in
  match Json_parser.parse_string json with
  | Ok m ->
      (match List.hd m.declarations with
      | Syntax.Definition def ->
          (* lambda starts at line 9, column 17 *)
          expect_loc (Some { file = None; line = Some 9; column = Some 17 }) def.def_body.loc;
          (* inner { "var": "x" } starts at line 12, column 21 *)
          (match def.def_body.desc with
          | Syntax.Lambda { body; _ } ->
              expect_loc (Some { file = None; line = Some 12; column = Some 21 }) body.loc
          | _ -> fail "expected lambda")
      | _ -> fail "expected definition")
  | Error e -> fail (Json_parser.show_parse_error e)

let test_pi_locations () =
  let json = {|{
  "module": "Test",
  "imports": [],
  "declarations": [
    {
      "def": {
        "name": "id",
        "type": {
          "pi": {
            "arg": { "name": "A", "type": { "universe": "Type" } },
            "result": { "var": "A" }
          }
        },
        "body": { "var": "A" }
      }
    }
  ]
}|} in
  match Json_parser.parse_string json with
  | Ok m ->
      (match List.hd m.declarations with
      | Syntax.Definition def ->
          (* pi type starts at line 8, column 17 *)
          expect_loc (Some { file = None; line = Some 8; column = Some 17 }) def.def_type.loc;
          (* result { "var": "A" } starts at line 11, column 23 *)
          (match def.def_type.desc with
          | Syntax.Pi { result; _ } ->
              expect_loc (Some { file = None; line = Some 11; column = Some 23 }) result.loc
          | _ -> fail "expected pi")
      | _ -> fail "expected definition")
  | Error e -> fail (Json_parser.show_parse_error e)

let test_app_locations () =
  let json = {|{
  "module": "Test",
  "imports": [],
  "declarations": [
    {
      "def": {
        "name": "test",
        "type": { "var": "R" },
        "body": { "app": [{ "var": "f" }, { "var": "x" }] }
      }
    }
  ]
}|} in
  match Json_parser.parse_string json with
  | Ok m ->
      (match List.hd m.declarations with
      | Syntax.Definition def ->
          (* app starts at line 9, column 17 *)
          expect_loc (Some { file = None; line = Some 9; column = Some 17 }) def.def_body.loc
      | _ -> fail "expected definition")
  | Error e -> fail (Json_parser.show_parse_error e)

let test_inductive_locations () =
  let json = {|{
  "module": "Test",
  "imports": [],
  "declarations": [
    {
      "inductive": {
        "name": "Nat",
        "params": [],
        "universe": "Type",
        "constructors": [
          { "name": "zero", "args": [] },
          { "name": "succ", "args": [{ "name": "n", "type": { "var": "Nat" } }] }
        ]
      }
    }
  ]
}|} in
  match Json_parser.parse_string json with
  | Ok m ->
      (match List.hd m.declarations with
      | Syntax.Inductive ind ->
          (* ind_loc is from loc_of_name which finds "Nat" at line 7, column 18 *)
          expect_loc (Some { file = None; line = Some 7; column = Some 18 }) ind.ind_loc;
          (* First constructor (zero) at line 11, column 22 *)
          let zero_ctor = List.hd ind.constructors in
          expect_loc (Some { file = None; line = Some 11; column = Some 22 }) zero_ctor.ctor_loc
      | _ -> fail "expected inductive")
  | Error e -> fail (Json_parser.show_parse_error e)

let test_declaration_locations () =
  let json = {|{
  "module": "Test",
  "imports": [],
  "declarations": [
    {
      "def": {
        "name": "mydef",
        "type": { "var": "A" },
        "body": { "var": "x" }
      }
    }
  ]
}|} in
  match Json_parser.parse_string json with
  | Ok m ->
      (match List.hd m.declarations with
      | Syntax.Definition def ->
          (* def_loc is from loc_of_name which finds "mydef" at line 7, column 18 *)
          expect_loc (Some { file = None; line = Some 7; column = Some 18 }) def.def_loc
      | _ -> fail "expected definition")
  | Error e -> fail (Json_parser.show_parse_error e)

let () =
  run "Parser" [
    "basic", [
      test_case "minimal module" `Quick test_minimal_module;
      test_case "variable and lambda" `Quick test_variable;
      test_case "inductive type" `Quick test_inductive;
      test_case "literals" `Quick test_literals;
    ];
    "locations", [
      test_case "term locations" `Quick test_term_locations;
      test_case "lambda locations" `Quick test_lambda_locations;
      test_case "pi locations" `Quick test_pi_locations;
      test_case "app locations" `Quick test_app_locations;
      test_case "inductive locations" `Quick test_inductive_locations;
      test_case "declaration locations" `Quick test_declaration_locations;
    ]
  ]
