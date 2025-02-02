(*
 * Copyright (c) 2009-2013, Monoidics ltd.
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open PolyVariantEqual

(** Configuration values: either constant, determined at compile time, or set at startup
    time by system calls, environment variables, or command line options *)

module F = Format
module CLOpt = CommandLineOption
module L = Die

type analyzer = Checkers | Linters [@@deriving compare]

let equal_analyzer = [%compare.equal: analyzer]

let string_to_analyzer = [("checkers", Checkers); ("linters", Linters)]

let clang_frontend_action_symbols =
  [("lint", `Lint); ("capture", `Capture); ("lint_and_capture", `Lint_and_capture)]


let ml_bucket_symbols =
  [ ("all", `MLeak_all)
  ; ("cf", `MLeak_cf)
  ; ("arc", `MLeak_arc)
  ; ("narc", `MLeak_no_arc)
  ; ("cpp", `MLeak_cpp)
  ; ("unknown_origin", `MLeak_unknown) ]


let issues_fields_symbols =
  [ ("bug_type", `Issue_field_bug_type)
  ; ("bucket", `Issue_field_bucket)
  ; ("qualifier", `Issue_field_qualifier)
  ; ("severity", `Issue_field_severity)
  ; ("line", `Issue_field_line)
  ; ("column", `Issue_field_column)
  ; ("procedure", `Issue_field_procedure)
  ; ("procedure_start_line", `Issue_field_procedure_start_line)
  ; ("file", `Issue_field_file)
  ; ("bug_trace", `Issue_field_bug_trace)
  ; ("key", `Issue_field_key)
  ; ("hash", `Issue_field_hash)
  ; ("line_offset", `Issue_field_line_offset)
  ; ( "qualifier_contains_potential_exception_note"
    , `Issue_field_qualifier_contains_potential_exception_note ) ]


type os_type = Unix | Win32 | Cygwin

type compilation_database_dependencies =
  | Deps of int option
  (* get the compilation database of the dependencies up to depth n
     by [Deps (Some n)], or all by [Deps None]  *)
  | NoDeps
[@@deriving compare]

type build_system =
  | BAnt
  | BBuck
  | BClang
  | BGradle
  | BJava
  | BJavac
  | BMake
  | BMvn
  | BNdk
  | BXcode
[@@deriving compare]

let equal_build_system = [%compare.equal: build_system]

(* List of ([build system], [executable name]). Several executables may map to the same build
   system. In that case, the first one in the list will be used for printing, eg, in which mode
   infer is running. *)
let build_system_exe_assoc =
  [ (BAnt, "ant")
  ; (BBuck, "buck")
  ; (BGradle, "gradle")
  ; (BGradle, "gradlew")
  ; (BJava, "java")
  ; (BJavac, "javac")
  ; (BClang, "cc")
  ; (BClang, "clang")
  ; (BClang, "gcc")
  ; (BClang, "clang++")
  ; (BClang, "c++")
  ; (BClang, "g++")
  ; (BMake, "make")
  ; (BMake, "configure")
  ; (BMake, "cmake")
  ; (BMake, "waf")
  ; (BMvn, "mvn")
  ; (BMvn, "mvnw")
  ; (BNdk, "ndk-build")
  ; (BXcode, "xcodebuild") ]


let string_of_build_system build_system =
  List.Assoc.find_exn ~equal:equal_build_system build_system_exe_assoc build_system


let build_system_of_exe_name name =
  try List.Assoc.find_exn ~equal:String.equal (List.Assoc.inverse build_system_exe_assoc) name
  with Not_found_s _ | Caml.Not_found ->
    L.(die UserError)
      "Unsupported build command '%s'.@\n\
       If this is an alias for another build system that infer supports, you can use@\n\
       `--force-integration <command>` where <command> is one of the following supported build \
       systems:@\n\
       @[<v2>  %a@]"
      name
      (Pp.seq ~print_env:Pp.text_break ~sep:"" F.pp_print_string)
      ( List.map ~f:fst build_system_exe_assoc
      |> List.map ~f:string_of_build_system
      |> List.dedup_and_sort ~compare:String.compare )


(** Constant configuration values *)

let anonymous_block_num_sep = "_"

let anonymous_block_prefix = "objc_block"

let assign = "<\"Assign\">"

let backend_stats_dir_name = "backend_stats"

(** If true, a procedure call succeeds even when there is a bound error this mimics what
    happens with a direct array access where an error is produced and the analysis
    continues *)
let bound_error_allowed_in_procedure_call = true

let buck_infer_deps_file_name = "infer-deps.txt"

let buck_results_dir_name = "infer"

let captured_dir_name = "captured"

let clang_initializer_prefix = "__infer_globals_initializer_"

let clang_inner_destructor_prefix = "__infer_inner_destructor_"

let classnames_dir_name = "classnames"

let costs_report_json = "costs-report.json"

(** Experimental: if true do some specialized analysis of concurrent constructs. *)
let csl_analysis = true

let default_failure_name = "ASSERTION_FAILURE"

let default_in_zip_results_dir = "infer"

(** Dotty output filename **)
let dotty_output = "icfg.dot"

let driver_stats_dir_name = "driver_stats"

let duplicates_filename = "duplicates.txt"

let events_dir_name = "events"

let trace_events_file = "perf_events.json"

(** exit code to use for the --fail-on-issue option *)
let fail_on_issue_exit_code = 2

let frontend_stats_dir_name = "frontend_stats"

let global_tenv_filename = ".global.tenv"

(** If true, treat calls to no-arg getters as idempotent w.r.t non-nullness *)
let idempotent_getters = true

(** Our Python script does its own argument parsing and will fail with this error on failure *)
let infer_py_argparse_error_exit_code = 22

let ivar_attributes = "ivar_attributes"

let lint_dotty_dir_name = "lint_dotty"

let lint_issues_dir_name = "lint_issues"

let manual_buck_compilation_db = "BUCK COMPILATION DATABASE OPTIONS"

let manual_buck_flavors = "BUCK FLAVORS OPTIONS"

let manual_buck_java = "BUCK FOR JAVA OPTIONS"

let manual_buffer_overrun = "BUFFER OVERRUN OPTIONS"

let manual_clang = "CLANG OPTIONS"

let manual_clang_linters = "CLANG LINTERS OPTIONS"

let manual_generic = Cmdliner.Manpage.s_options

let manual_hoisting = "HOISTING OPTIONS"

let manual_internal = "INTERNAL OPTIONS"

let manual_java = "JAVA OPTIONS"

let manual_quandary = "QUANDARY CHECKER OPTIONS"

let manual_racerd = "RACERD CHECKER OPTIONS"

let manual_siof = "SIOF CHECKER OPTIONS"

let max_narrows = 5

(** Maximum number of widens that can be performed before the analysis will intentionally crash.
    Used to guard against divergence in the case that someone has implemented a bad widening
    operator *)
let max_widens = 10000

(** Flag to tune the level of applying the meet operator for
    preconditions during the footprint analysis:
    0 = do not use the meet
    1 = use the meet to generate new preconditions *)
let meet_level = 1

let nsnotification_center_checker_backend = false

let perf_stats_prefix = "perf_stats"

let proc_stats_filename = "proc_stats.json"

let property_attributes = "property_attributes"

let racerd_issues_dir_name = "racerd"

let report_condition_always_true_in_clang = false

let report_json = "report.json"

(** If true, sanity-check inferred preconditions against Nullable annotations and report
    inconsistencies *)
let report_nullable_inconsistency = true

let reporting_stats_dir_name = "reporting_stats"

let retain_cycle_dotty_dir = "retain_cycle_dotty"

(** If true, compact summaries before saving *)
let save_compact_summaries = true

(** If true enables printing proposition compatible for the SMT project *)
let smt_output = false

let source_file_extentions = [".java"; ".m"; ".mm"; ".c"; ".cc"; ".cpp"; ".h"]

let specs_dir_name = "specs"

let specs_files_suffix = ".specs"

let starvation_issues_dir_name = "starvation_issues"

(** Enable detailed tracing information during array abstraction *)
let trace_absarray = false

(** If true, optimize based on locality using reachability *)
let undo_join = true

let unsafe_unret = "<\"Unsafe_unretained\">"

let weak = "<\"Weak\">"

(* Whitelists for C++ library functions *)

let std_whitelisted_cpp_methods =
  [ "std::back_inserter"
  ; "std::forward"
  ; "std::front_inserter"
  ; "std::get"
  ; "std::inserter"
  ; "std::make_move_iterator"
  ; "std::make_pair"
  ; "std::max"
  ; "std::min"
  ; "std::move"
  ; "std::operator!="
  ; "std::operator<"
  ; "std::operator<="
  ; "std::operator=="
  ; "std::operator>"
  ; "std::operator>="
  ; "std::swap" ]


let libstdcxx_whitelisted_cpp_methods =
  [ "__gnu_cxx::operator!="
  ; "__gnu_cxx::operator<"
  ; "__gnu_cxx::operator<="
  ; "__gnu_cxx::operator=="
  ; "__gnu_cxx::operator>"
  ; "__gnu_cxx::operator>="
  ; "__gnu_cxx::operator+"
  ; "__gnu_cxx::operator-" ]


let libcxx_whitelisted_cpp_methods = []

let other_whitelisted_cpp_methods = ["google::CheckNotNull"]

let whitelisted_cpp_methods =
  List.concat
    [ std_whitelisted_cpp_methods
    ; libstdcxx_whitelisted_cpp_methods
    ; libcxx_whitelisted_cpp_methods
    ; other_whitelisted_cpp_methods ]


(* Whitelists for C++ library classes *)

let std_whitelisted_cpp_classes =
  [ "std::back_insert_iterator"
  ; "std::equal_to"
  ; "std::front_insert_iterator"
  ; "std::greater"
  ; "std::greater_equal"
  ; "std::insert_iterator"
  ; "std::less"
  ; "std::less_equal"
  ; "std::move_iterator"
  ; "std::not_equal_to"
  ; "std::pair"
  ; "std::reverse_iterator" ]


let libstdcxx_whitelisted_cpp_classes =
  (* libstdc++ internal support class for std::get<std::pair> *)
  [ "__gnu_cxx::__normal_iterator" (* libstdc++ internal name of vector iterator *)
  ; "std::__pair_get" ]


let libcxx_whitelisted_cpp_classes =
  (* libc++ internal support class for std::get<std::pair> *)
  [ "std::__less"
  ; "std::__wrap_iter" (* libc++ internal name of vector iterator *)
  ; "std::__get_pair" ]


let other_whitelisted_cpp_classes = []

let whitelisted_cpp_classes =
  List.concat
    [ std_whitelisted_cpp_classes
    ; libstdcxx_whitelisted_cpp_classes
    ; libcxx_whitelisted_cpp_classes
    ; other_whitelisted_cpp_classes ]


let pp_version fmt () =
  F.fprintf fmt "Infer version %s@\nCopyright 2009 - present Facebook. All Rights Reserved."
    Version.versionString


let version_string = F.asprintf "%a" pp_version ()

(** System call configuration values *)

(** Initial time of the analysis, i.e. when this module is loaded, gotten from
    Unix.time *)
let initial_analysis_time = Unix.time ()

let clang_exe_aliases =
  [ (* this must be kept in sync with the clang-like symlinks in [wrappers_dir] (see below) *)
    "c++"
  ; "cc"
  ; "clang"
  ; "clang++"
  ; "g++"
  ; "gcc" ]


let exe_basename =
  (* Sys.executable_name tries to do clever things which we must avoid, use argv[0] instead *)
  Filename.basename Sys.argv.(0)


let infer_is_clang = List.mem ~equal:String.equal clang_exe_aliases exe_basename

let initial_command =
  match InferCommand.of_exe_name exe_basename with Some _ as command -> command | None -> None


let bin_dir =
  (* Resolve symlinks to get to the real executable, which is located in [bin_dir]. *)
  Filename.dirname (Utils.realpath Sys.executable_name)


let lib_dir = bin_dir ^/ Filename.parent_dir_name ^/ "lib"

let etc_dir = bin_dir ^/ Filename.parent_dir_name ^/ "etc"

(** Path to lib/specs to retrieve the default models *)
let models_dir = lib_dir ^/ specs_dir_name

let models_jar = lib_dir ^/ "java" ^/ "models.jar"

let models_src_dir =
  let root = Unix.getcwd () in
  let dir = bin_dir ^/ Filename.parent_dir_name ^/ "models" in
  Utils.filename_to_absolute ~root dir


(* Normalize the path *)

let relative_cpp_extra_include_dir = "cpp" ^/ "include"

let cpp_extra_include_dir = models_src_dir ^/ relative_cpp_extra_include_dir

let relative_cpp_models_dir = relative_cpp_extra_include_dir ^/ "infer_model"

let linters_def_dir = lib_dir ^/ "linter_rules"

let linters_def_default_file = linters_def_dir ^/ "linters.al"

let wrappers_dir = lib_dir ^/ "wrappers"

let ncpu = Setcore.numcores ()

let os_type = match Sys.os_type with "Win32" -> Win32 | "Cygwin" -> Cygwin | _ -> Unix

(** Resolve relative paths passed as command line options, i.e., with respect to the working
    directory of the initial invocation of infer. *)
let resolve = Utils.filename_to_absolute ~root:CLOpt.init_work_dir

let infer_top_results_dir_env_var = "INFER_TOP_RESULTS_DIR"

let infer_inside_maven_env_var = "INFER_INSIDE_MAVEN"

let maven = CLOpt.is_env_var_set infer_inside_maven_env_var

let env_inside_maven = `Extend [(infer_inside_maven_env_var, "1")]

let infer_is_javac = maven

let startup_action =
  let open CLOpt in
  if infer_is_javac then Javac
  else if !Sys.interactive then NoParse
  else if infer_is_clang then NoParse
  else InferCommand


let exe_usage =
  let exe_command_name =
    match initial_command with
    | Some command ->
        Some (InferCommand.to_string command)
    | None ->
        None
  in
  Printf.sprintf "%s\nUsage: infer %s [options]\nSee `infer%s --help` for more information."
    version_string
    (Option.value ~default:"command" exe_command_name)
    (Option.value_map ~default:"" ~f:(( ^ ) " ") exe_command_name)


let get_symbol_string json_obj =
  match json_obj with
  | `String sym_regexp_str ->
      sym_regexp_str
  | _ ->
      L.(die UserError) "each --custom-symbols element should be list of symbol *strings*"


let get_symbols_regexp json_obj =
  let sym_regexp_strs =
    match json_obj with
    | `List json_objs ->
        List.map ~f:get_symbol_string json_objs
    | _ ->
        L.(die UserError) "each --custom-symbols element should be a *list* of strings"
  in
  Str.regexp ("\\(" ^ String.concat ~sep:"\\|" sym_regexp_strs ^ "\\)")


(** Command Line options *)

(* HOWTO define a new command line and config file option.

   1. Add an entry in the following let...and...and... binding.  See the documentation in
      [CommandLineOption.mli], and use the existing options as a guide.  Preferably the identifer
      and long option name are the same modulo underscores versus hyphens.

      E.g. [and new_option = CLOpt.mk_bool ~long:"new-option"]

   2. Add a line to the [Freeze initialized configuration values] section below.

      E.g. [and new_option = !new_option]

   3. Add a line to [config.mli].

      E.g. [val new_option : bool]

   These are all in alphabetical order as much as possible.

   The references representing the command line options are defined in a single
   simultaneous let...and...and... binding in order to allow the type-checker to catch
   uses of one reference in code for another. This avoids being sensitive to
   initialization-order and unintended dependence on the order in which options appear on
   the command line. For cases where order-dependence is desired, the interacting options
   can be defined together sharing a reference. See debug and specs_library below for two
   different examples. *)

let anon_args = CLOpt.mk_anon ()

let all_checkers = ref []

let disable_all_checkers () = List.iter !all_checkers ~f:(fun (var, _, _, _) -> var := false)

let () =
  let on_unknown_arg_from_command (cmd : InferCommand.t) =
    match cmd with
    | Report ->
        `Add
    | Analyze | Capture | Compile | Diff | Events | Explore | ReportDiff | Run ->
        `Reject
  in
  (* make sure we generate doc for all the commands we know about *)
  List.iter InferCommand.all_commands ~f:(fun cmd ->
      let {CommandDoc.name; command_doc} = CommandDoc.data_of_command cmd in
      let on_unknown_arg = on_unknown_arg_from_command cmd in
      let deprecated_long = if InferCommand.(equal ReportDiff) cmd then Some "diff" else None in
      CLOpt.mk_subcommand cmd ~name ?deprecated_long ~on_unknown_arg (Some command_doc) )


let abs_struct =
  CLOpt.mk_int ~deprecated:["absstruct"] ~long:"abs-struct" ~default:1 ~meta:"int"
    {|Specify abstraction level for fields of structs:
- 0 = no
- 1 = forget some fields during matching (and so lseg abstraction)
|}


and abs_val =
  CLOpt.mk_int ~deprecated:["absval"] ~long:"abs-val" ~default:2 ~meta:"int"
    {|Specify abstraction level for expressions:
- 0 = no abstraction
- 1 = evaluate all expressions abstractly
- 2 = 1 + abstract constant integer values during join
|}


and allow_leak =
  CLOpt.mk_bool ~deprecated:["leak"] ~long:"allow-leak" "Forget leaked memory during abstraction"


and ( analysis_blacklist_files_containing
    , analysis_path_regex_blacklist
    , analysis_path_regex_whitelist
    , analysis_suppress_errors ) =
  let mk_filtering_option ~suffix ~help ~meta =
    let deprecated =
      List.map ["checkers"; "infer"] ~f:(fun name -> Printf.sprintf "%s-%s" name suffix)
    in
    let long = Printf.sprintf "report-%s" suffix in
    CLOpt.mk_string_list ~deprecated ~long ~meta
      ~in_help:InferCommand.[(Report, manual_generic); (Run, manual_generic)]
      help
  in
  ( mk_filtering_option ~suffix:"blacklist-files-containing"
      ~help:
        "blacklist files containing the specified string for the given analyzer (see \
         $(b,--analyzer) for valid values)"
      ~meta:"string"
  , mk_filtering_option ~suffix:"blacklist-path-regex"
      ~help:
        "blacklist the analysis of files whose relative path matches the specified OCaml-style \
         regex (to whitelist: $(b,--<analyzer>-whitelist-path-regex))"
      ~meta:"path_regex"
  , mk_filtering_option ~suffix:"whitelist-path-regex" ~help:"" ~meta:"path_regex"
  , mk_filtering_option ~suffix:"suppress-errors" ~help:"do not report a type of errors"
      ~meta:"error_name" )


and analysis_stops =
  CLOpt.mk_bool ~deprecated:["analysis_stops"] ~long:"analysis-stops"
    "Issue a warning when the analysis stops"


and analyzer =
  CLOpt.mk_symbol ~deprecated:["analyzer"; "-analyzer"; "a"] ~long:"" ~default:Checkers
    ~eq:equal_analyzer ~symbols:string_to_analyzer
    "DEPRECATED: To enable and disable individual analyses, use the various checkers options. For \
     instance, to enable only the biabduction analysis, run with $(b,--biabduction-only)."


and ( annotation_reachability
    , biabduction
    , bufferoverrun
    , class_loads
    , cost
    , eradicate
    , fragment_retains_view
    , gradual
    , gradual_dereferences
    , gradual_unannotated
    , immutable_cast
    , linters
    , litho
    , liveness
    , loop_hoisting
    , nullsafe
    , ownership
    , printf_args
    , pulse
    , purity
    , quandary
    , quandaryBO
    , racerd
    , resource_leak
    , siof
    , starvation
    , uninit ) =
  let mk_checker ?(default = false) ?(deprecated = []) ~long doc =
    let var =
      CLOpt.mk_bool ~long
        ~in_help:InferCommand.[(Analyze, manual_generic)]
        ~default ~deprecated doc
    in
    all_checkers := (var, long, doc, default) :: !all_checkers ;
    var
  in
  let annotation_reachability =
    mk_checker ~default:false ~long:"annotation-reachability"
      "the annotation reachability checker. Given a pair of source and sink annotation, e.g. \
       @PerformanceCritical and @Expensive, this checker will warn whenever some method annotated \
       with @PerformanceCritical calls, directly or indirectly, another method annotated with \
       @Expensive"
  and biabduction =
    mk_checker ~long:"biabduction" ~default:true
      "the separation logic based bi-abduction analysis using the checkers framework"
  and bufferoverrun = mk_checker ~long:"bufferoverrun" "the buffer overrun analysis"
  and class_loads = mk_checker ~long:"class-loads" ~default:false "Java class loading analysis"
  and cost = mk_checker ~long:"cost" ~default:false "checker for performance cost analysis"
  and eradicate =
    mk_checker ~long:"eradicate" "the eradicate @Nullable checker for Java annotations"
  and fragment_retains_view =
    mk_checker ~long:"fragment-retains-view" ~default:true
      "detects when Android fragments are not explicitly nullified before becoming unreabable"
  and gradual =
    mk_checker ~long:"gradual" "the gradual @Nullable checker for Java annotations"
  and gradual_dereferences =
    mk_checker ~long:"gradual-dereferences" "warns about all deferences; does not analyze"
  and gradual_unannotated =
    mk_checker ~long:"gradual-unannotated" "doesn't take annotations into account"
  and immutable_cast =
    mk_checker ~long:"immutable-cast" ~default:false
      "the detection of object cast from immutable type to mutable type. For instance, it will \
       detect cast from ImmutableList to List, ImmutableMap to Map, and ImmutableSet to Set."
  and linters = mk_checker ~long:"linters" ~default:true "syntactic linters"
  and litho = mk_checker ~long:"litho" "Experimental checkers supporting the Litho framework"
  and liveness =
    mk_checker ~long:"liveness" ~default:true "the detection of dead stores and unused variables"
  and loop_hoisting = mk_checker ~long:"loop-hoisting" ~default:false "checker for loop-hoisting"
  and nullsafe =
    mk_checker ~long:"nullsafe"
      ~deprecated:["-check-nullable"; "-suggest-nullable"]
      "[EXPERIMENTAL] Nullable type checker (incomplete: use --eradicate for now)"
  and ownership = mk_checker ~long:"ownership" ~default:true "the detection of C++ lifetime bugs"
  and printf_args =
    mk_checker ~long:"printf-args" ~default:false
      "the detection of mismatch between the Java printf format strings and the argument types \
       For, example, this checker will warn about the type error in `printf(\"Hello %d\", \
       \"world\")`"
  and pulse = mk_checker ~long:"pulse" "[EXPERIMENTAL] C++ lifetime analysis"
  and purity = mk_checker ~long:"purity" ~default:false "[EXPERIMENTAL] Purity analysis"
  and quandary = mk_checker ~long:"quandary" ~default:false "the quandary taint analysis"
  and quandaryBO =
    mk_checker ~long:"quandaryBO" ~default:false
      "[EXPERIMENTAL] The quandaryBO tainted buffer access analysis"
  and racerd =
    mk_checker ~long:"racerd" ~deprecated:["-threadsafety"] ~default:true
      "the RacerD thread safety analysis"
  and resource_leak = mk_checker ~long:"resource-leak" ""
  and siof =
    mk_checker ~long:"siof" ~default:true
      "the Static Initialization Order Fiasco analysis (C++ only)"
  and starvation = mk_checker ~long:"starvation" ~default:false "starvation analysis"
  and uninit = mk_checker ~long:"uninit" "checker for use of uninitialized values" ~default:true in
  let mk_only (var, long, doc, _) =
    let (_ : bool ref) =
      CLOpt.mk_bool_group ~long:(long ^ "-only")
        ~in_help:InferCommand.[(Analyze, manual_generic)]
        ~f:(fun b ->
          disable_all_checkers () ;
          var := b ;
          b )
        ( if String.equal doc "" then ""
        else Printf.sprintf "Enable $(b,--%s) and disable all other checkers" long )
        [] (* do all the work in ~f *) []
      (* do all the work in ~f *)
    in
    ()
  in
  List.iter ~f:mk_only !all_checkers ;
  let _default_checkers : bool ref =
    CLOpt.mk_bool_group ~long:"default-checkers"
      ~in_help:InferCommand.[(Analyze, manual_generic)]
      ~default:true
      ( "Default checkers: "
      ^ ( List.rev_filter_map
            ~f:(fun (_, long, _, default) ->
              if default then Some (Printf.sprintf "$(b,--%s)" long) else None )
            !all_checkers
        |> String.concat ~sep:", " ) )
      ~f:(fun b ->
        List.iter
          ~f:(fun (var, _, _, default) ->
            var := if b then default || !var else (not default) && !var )
          !all_checkers ;
        b )
      [] (* do all the work in ~f *) []
    (* do all the work in ~f *)
  in
  ( annotation_reachability
  , biabduction
  , bufferoverrun
  , class_loads
  , cost
  , eradicate
  , fragment_retains_view
  , gradual
  , gradual_dereferences
  , gradual_unannotated
  , immutable_cast
  , linters
  , litho
  , liveness
  , loop_hoisting
  , nullsafe
  , ownership
  , printf_args
  , pulse
  , purity
  , quandary
  , quandaryBO
  , racerd
  , resource_leak
  , siof
  , starvation
  , uninit )


and annotation_reachability_cxx =
  CLOpt.mk_json ~long:"annotation-reachability-cxx"
    ~in_help:InferCommand.[(Analyze, manual_clang)]
    {|Specify annotation reachability analyses to be performed on C/C++/ObjC code. Each entry is a JSON object whose key is the issue name. "sources" and "sinks" can be specified either by symbol or path prefix.  "sinks" optionally can specify "overrides" (by symbol or path prefix) that block the reachability analysis when hit.  Example:
  {
    "ISOLATED_REACHING_CONNECT": {
      "doc_url": "http:://optional/issue/doc/link.html",
      "sources": {
        "desc": "Code that should not call connect [optional]",
        "paths": [ "isolated/" ]
      },
      "sinks": {
        "symbols": [ "connect" ],
        "overrides": { "symbols": [ "Trusted::" ] }
      }
    }
  }
This will cause us to create a new ISOLATED_REACHING_CONNECT issue for every function whose source path starts with "isolated/" that may reach the function named "connect", ignoring paths that go through a symbol starting with "Trusted::".
|}


and annotation_reachability_custom_pairs =
  CLOpt.mk_json ~long:"annotation-reachability-custom-pairs"
    ~in_help:InferCommand.[(Analyze, manual_java)]
    {|Specify custom sources/sink for the annotation reachability checker
Example format: for custom annotations com.my.annotation.{Source1,Source2,Sink1}
{ "sources" : ["Source1", "Source2"], "sink" : "Sink1" }|}


and append_buck_flavors =
  CLOpt.mk_string_list ~long:"append-buck-flavors"
    ~in_help:InferCommand.[(Capture, manual_buck_flavors)]
    "Additional Buck flavors to append to targets discovered by the \
     $(b,--buck-compilation-database) option."


and array_level =
  CLOpt.mk_int ~deprecated:["arraylevel"] ~long:"array-level" ~default:0 ~meta:"int"
    {|Level of treating the array indexing and pointer arithmetic:
- 0 = treats both features soundly
- 1 = assumes that the size of every array is infinite
- 2 = assumes that all heap dereferences via array indexing and pointer arithmetic are correct
|}


and bo_relational_domain =
  CLOpt.mk_symbol_opt ~long:"bo-relational-domain"
    ~in_help:InferCommand.[(Analyze, manual_buffer_overrun)]
    ~symbols:[("oct", `Bo_relational_domain_oct); ("poly", `Bo_relational_domain_poly)]
    "Select a relational domain being used in the bufferoverrun checker (experimental)"


and bootclasspath =
  CLOpt.mk_string_opt ~long:"bootclasspath"
    ~in_help:InferCommand.[(Capture, manual_java)]
    "Specify the Java bootclasspath"


(** Automatically set when running from within Buck *)
and buck = CLOpt.mk_bool ~long:"buck" ""

and buck_blacklist =
  CLOpt.mk_string_list
    ~deprecated:["-blacklist-regex"; "-blacklist"]
    ~long:"buck-blacklist"
    ~in_help:InferCommand.[(Run, manual_buck_flavors); (Capture, manual_buck_flavors)]
    ~meta:"regex"
    "Skip capture of files matched by the specified regular expression (only the \"flavors \
     (C++)\" Buck integration is supported, not Java)."


and buck_build_args =
  CLOpt.mk_string_list ~long:"Xbuck"
    ~in_help:InferCommand.[(Capture, manual_buck_flavors)]
    "Pass values as command-line arguments to invocations of $(i,`buck build`)"


and buck_build_args_no_inline =
  CLOpt.mk_string_list ~long:"Xbuck-no-inline"
    ~in_help:InferCommand.[(Capture, manual_buck_flavors)]
    "Pass values as command-line arguments to invocations of $(i,`buck build`), don't inline any \
     args starting with '@'"


and buck_compilation_database_depth =
  CLOpt.mk_int_opt ~long:"buck-compilation-database-depth"
    ~in_help:InferCommand.[(Capture, manual_buck_compilation_db)]
    "Depth of dependencies used by the $(b,--buck-compilation-database deps) option. By default, \
     all recursive dependencies are captured."
    ~meta:"int"


and buck_compilation_database =
  CLOpt.mk_symbol_opt ~long:"buck-compilation-database" ~deprecated:["-use-compilation-database"]
    ~in_help:InferCommand.[(Capture, manual_buck_compilation_db)]
    "Buck integration using the compilation database, with or without dependencies."
    ~symbols:[("no-deps", `NoDeps); ("deps", `DepsTmp)]


and buck_out =
  CLOpt.mk_path_opt ~long:"buck-out"
    ~in_help:InferCommand.[(Capture, manual_buck_java)]
    ~meta:"dir" "Specify the root directory of buck-out"


and buck_targets_blacklist =
  CLOpt.mk_string_list ~long:"buck-targets-blacklist"
    ~in_help:
      InferCommand.[(Run, manual_buck_compilation_db); (Capture, manual_buck_compilation_db)]
    ~meta:"regex" "Skip capture of buck targets matched by the specified regular expression."


and capture =
  CLOpt.mk_bool ~long:"capture" ~default:true
    "capture and translate source files into infer's intermediate language for analysis"


and capture_blacklist =
  CLOpt.mk_string_opt ~long:"capture-blacklist"
    ~in_help:InferCommand.[(Run, manual_buck_flavors); (Capture, manual_buck_flavors)]
    ~meta:"regex"
    "Skip capture of files matched by the specified OCaml regular expression (only supported by \
     the javac integration for now)."


and changed_files_index =
  CLOpt.mk_path_opt ~long:"changed-files-index"
    ~in_help:InferCommand.[(Analyze, manual_generic); (Diff, manual_generic)]
    ~meta:"file"
    "Specify the file containing the list of source files from which reactive analysis should \
     start. Source files should be specified relative to project root or be absolute"


and check_version =
  CLOpt.mk_string_opt ~long:"check-version" ~meta:"version"
    "Verify that the Infer version is equal to the provided argument"


and clang_biniou_file =
  CLOpt.mk_path_opt ~long:"clang-biniou-file"
    ~in_help:InferCommand.[(Capture, manual_clang)]
    ~meta:"file" "Specify a file containing the AST of the program, in biniou format"


and clang_extra_flags =
  CLOpt.mk_string_list ~long:"Xclang"
    ~in_help:InferCommand.[(Capture, manual_clang)]
    "Pass values as command-line arguments to invocations of clang"


and clang_compilation_dbs = ref []

and clang_frontend_action =
  CLOpt.mk_symbol_opt ~long:"" ~deprecated:["-clang-frontend-action"]
    ~in_help:InferCommand.[(Capture, manual_clang); (Run, manual_clang)]
    (* doc only shows up in deprecation warnings *)
    "use --capture and --linters instead" ~symbols:clang_frontend_action_symbols


and clang_include_to_override_regex =
  CLOpt.mk_string_opt ~long:"clang-include-to-override-regex"
    ~deprecated:["-clang-include-to-override"] ~meta:"dir_OCaml_regex"
    "Use this option in the uncommon case where the normal compilation process overrides the \
     location of internal compiler headers. This option should specify regular expression with \
     the path to those headers so that infer can use its own clang internal headers instead."


and clang_ignore_regex =
  CLOpt.mk_string_opt ~long:"clang-ignore-regex" ~meta:"dir_OCaml_regex"
    "The files in this regex will be ignored in the compilation process and an empty file will be \
     passed to clang instead. This is to be used with the buck flavour infer-capture-all to work \
     around missing generated files."


and class_loads_roots =
  CLOpt.mk_string_list ~long:"class-loads-roots" "Report class loads of this list of Java methods"


and classpath = CLOpt.mk_string_opt ~long:"classpath" "Specify the Java classpath"

and compilation_database =
  CLOpt.mk_path_list ~long:"compilation-database" ~deprecated:["-clang-compilation-db-files"]
    ~in_help:InferCommand.[(Capture, manual_clang)]
    "File that contain compilation commands (can be specified multiple times)"


and compilation_database_escaped =
  CLOpt.mk_path_list ~long:"compilation-database-escaped"
    ~deprecated:["-clang-compilation-db-files-escaped"]
    ~in_help:InferCommand.[(Capture, manual_clang)]
    "File that contain compilation commands where all entries are escaped for the shell, eg \
     coming from Xcode (can be specified multiple times)"


and compute_analytics =
  CLOpt.mk_bool ~long:"compute-analytics" ~default:false
    ~in_help:InferCommand.[(Capture, manual_clang); (Run, manual_clang)]
    "Emit analytics as info-level issues, like component kit line count and component kit file \
     cyclomatic complexity"


(** Continue the capture for reactive mode:
    If a procedure was changed beforehand, keep the changed marking. *)
and continue =
  CLOpt.mk_bool ~deprecated:["continue"] ~long:"continue"
    ~in_help:InferCommand.[(Analyze, manual_generic)]
    "Continue the capture for the reactive analysis, increasing the changed files/procedures. (If \
     a procedure was changed beforehand, keep the changed marking.)"


and cost_invariant_by_default =
  CLOpt.mk_bool ~long:"invariant-by-default" ~default:false
    "[Cost]Consider functions to be invariant by default"


and costs_current =
  CLOpt.mk_path_opt ~long:"costs-current"
    ~in_help:InferCommand.[(ReportDiff, manual_generic)]
    "Costs report of the latest revision"


and costs_previous =
  CLOpt.mk_path_opt ~long:"costs-previous"
    ~in_help:InferCommand.[(ReportDiff, manual_generic)]
    "Costs report of the base revision to use for comparison"


and current_to_previous_script =
  CLOpt.mk_string_opt ~long:"current-to-previous-script"
    ~in_help:InferCommand.[(Diff, manual_generic)]
    ~meta:"shell"
    "Specify a script to checkout a previous version of the project to compare against, assuming \
     we are on the current version already."


and cxx_infer_headers, siof_check_iostreams =
  let siof_check_iostreams =
    CLOpt.mk_bool ~long:"siof-check-iostreams"
      ~in_help:InferCommand.[(Analyze, manual_siof)]
      "Do not assume that iostreams (cout, cerr, ...) are always initialized. The default is to \
       assume they are always initialized when $(b,--cxx-infer-headers) is false to avoid false \
       positives due to lack of models of the proper initialization of io streams. However, if \
       your program compiles against a recent libstdc++ then the infer models are not needed for \
       precision and it is safe to turn this option on."
  in
  let cxx_infer_headers =
    CLOpt.mk_bool_group ~long:"cxx-infer-headers" ~default:false
      ~in_help:InferCommand.[(Capture, manual_clang)]
      "Include C++ header models during compilation. Infer swaps some C++ headers for its own in \
       order to get a better model of, eg, the standard library. This can sometimes cause \
       compilation failures."
      [siof_check_iostreams] []
  in
  (cxx_infer_headers, siof_check_iostreams)


and cxx_scope_guards =
  CLOpt.mk_json ~long:"cxx-scope-guards"
    ~in_help:InferCommand.[(Analyze, manual_clang)]
    "Specify scope guard classes that can be read only by destructors without being reported as \
     dead stores."


and cxx =
  CLOpt.mk_bool ~long:"cxx" ~default:true
    ~in_help:InferCommand.[(Capture, manual_clang)]
    "Analyze C++ methods"


and custom_symbols =
  CLOpt.mk_json ~long:"custom-symbols"
    ~in_help:InferCommand.[(Analyze, manual_generic)]
    "Specify named lists of symbols available to rules"


and ( bo_debug
    , developer_mode
    , debug
    , debug_exceptions
    , debug_level_analysis
    , debug_level_capture
    , debug_level_linters
    , debug_level_test_determinator
    , default_linters
    , filtering
    , frontend_tests
    , keep_going
    , linters_developer_mode
    , models_mode
    , only_cheap_debug
    , print_buckets
    , print_logs
    , print_types
    , reports_include_ml_loc
    , trace_error
    , write_html
    , write_html_whitelist_regex
    , write_dotty ) =
  let all_generic_manuals =
    List.filter_map InferCommand.all_commands ~f:(fun cmd ->
        if InferCommand.equal Explore cmd then None else Some (cmd, manual_generic) )
  in
  let bo_debug =
    CLOpt.mk_int ~default:0 ~long:"bo-debug"
      ~in_help:InferCommand.[(Analyze, manual_buffer_overrun)]
      "Debug level for buffer-overrun checker (0-4)"
  and debug_level_analysis =
    CLOpt.mk_int ~long:"debug-level-analysis" ~default:0 ~in_help:all_generic_manuals
      "Debug level for the analysis. See $(b,--debug-level) for accepted values."
  and debug_level_capture =
    CLOpt.mk_int ~long:"debug-level-capture" ~default:0 ~in_help:all_generic_manuals
      "Debug level for the capture. See $(b,--debug-level) for accepted values."
  and debug_level_linters =
    CLOpt.mk_int ~long:"debug-level-linters" ~default:0
      ~in_help:(InferCommand.(Capture, manual_clang_linters) :: all_generic_manuals)
      "Debug level for the linters. See $(b,--debug-level) for accepted values."
  and debug_level_test_determinator =
    CLOpt.mk_int ~long:"debug-level-test-determinator" ~default:0
      "Debug level for the test determinator. See $(b,--debug-level) for accepted values."
  and developer_mode =
    CLOpt.mk_bool ~long:"developer-mode"
      ~default:(Option.value_map ~default:false ~f:InferCommand.(equal Report) initial_command)
      "Show internal exceptions"
  and filtering =
    CLOpt.mk_bool ~deprecated_no:["nf"] ~long:"filtering" ~short:'f' ~default:true
      ~in_help:InferCommand.[(Report, manual_generic)]
      "Do not show the experimental and blacklisted issue types"
  and only_cheap_debug =
    CLOpt.mk_bool ~long:"only-cheap-debug" ~default:true "Disable expensive debugging output"
  and print_buckets =
    CLOpt.mk_bool ~long:"print-buckets"
      "Show the internal bucket of Infer reports in their textual description"
  and print_types =
    CLOpt.mk_bool ~long:"print-types" ~default:false "Print types in symbolic heaps"
  and keep_going =
    CLOpt.mk_bool ~deprecated_no:["-no-failures-allowed"] ~long:"keep-going"
      ~in_help:InferCommand.[(Analyze, manual_generic)]
      "Keep going when the analysis encounters a failure"
  and reports_include_ml_loc =
    CLOpt.mk_bool ~deprecated:["with_infer_src_loc"] ~long:"reports-include-ml-loc"
      "Include the location in the Infer source code from where reports are generated"
  and trace_error =
    CLOpt.mk_bool ~long:"trace-error" "Detailed tracing information during error explanation"
  and write_html =
    CLOpt.mk_bool ~long:"write-html" "Produce hmtl debug output in the results directory"
  and write_html_whitelist_regex =
    CLOpt.mk_string_list ~long:"write-html-whitelist-regex"
      "whitelist files that will have its html debug output printed"
  and write_dotty =
    CLOpt.mk_bool ~long:"write-dotty" "Produce dotty files for specs in the results directory"
  in
  let set_debug_level level =
    bo_debug := level ;
    debug_level_analysis := level ;
    debug_level_capture := level ;
    debug_level_linters := level ;
    debug_level_test_determinator := level
  in
  let debug =
    CLOpt.mk_bool_group ~deprecated:["debug"; "-stats"] ~long:"debug" ~short:'g'
      ~in_help:all_generic_manuals
      "Debug mode (also sets $(b,--debug-level 2), $(b,--developer-mode), $(b,--no-filtering), \
       $(b,--print-buckets), $(b,--print-types), $(b,--reports-include-ml-loc), \
       $(b,--no-only-cheap-debug), $(b,--trace-error), $(b,--write-dotty), $(b,--write-html))"
      ~f:(fun debug ->
        if debug then set_debug_level 2 else set_debug_level 0 ;
        CommandLineOption.keep_args_file := debug ;
        debug )
      [ developer_mode
      ; print_buckets
      ; print_types
      ; reports_include_ml_loc
      ; trace_error
      ; write_html
      ; write_dotty ]
      [filtering; only_cheap_debug]
  and (_ : int option ref) =
    CLOpt.mk_int_opt ~long:"debug-level" ~in_help:all_generic_manuals ~meta:"level"
      ~f:(fun level -> set_debug_level level ; level)
      {|Debug level (sets $(b,--bo-debug) $(i,level), $(b,--debug-level-analysis) $(i,level), $(b,--debug-level-capture) $(i,level), $(b,--debug-level-linters) $(i,level)):
  - 0: only basic debugging enabled
  - 1: verbose debugging enabled
  - 2: very verbose debugging enabled|}
  and debug_exceptions =
    CLOpt.mk_bool_group ~long:"debug-exceptions"
      "Generate lightweight debugging information: just print the internal exceptions during \
       analysis (also sets $(b,--developer-mode), $(b,--no-filtering), $(b,--print-buckets), \
       $(b,--reports-include-ml-loc))"
      [developer_mode; print_buckets; reports_include_ml_loc]
      [filtering; keep_going]
  and default_linters =
    CLOpt.mk_bool ~long:"default-linters"
      ~in_help:InferCommand.[(Capture, manual_clang_linters)]
      ~default:true "Use the default linters for the analysis."
  and frontend_tests =
    CLOpt.mk_bool_group ~long:"frontend-tests"
      ~in_help:InferCommand.[(Capture, manual_clang)]
      "Save filename.ext.test.dot with the cfg in dotty format for frontend tests (also sets \
       $(b,--print-types))"
      [print_types] []
  and models_mode =
    CLOpt.mk_bool_group ~long:"models-mode" "Mode for analyzing the models" [] [keep_going]
  and print_logs =
    CLOpt.mk_bool ~long:"print-logs"
      ~in_help:
        InferCommand.
          [ (Analyze, manual_generic)
          ; (Capture, manual_generic)
          ; (Run, manual_generic)
          ; (Report, manual_generic) ]
      "Also log messages to stdout and stderr"
  in
  let linters_developer_mode =
    CLOpt.mk_bool_group ~long:"linters-developer-mode"
      ~in_help:InferCommand.[(Capture, manual_clang_linters)]
      "Debug mode for developing new linters. (Sets the analyzer to $(b,linters); also sets \
       $(b,--debug), $(b,--debug-level-linters 2), $(b,--developer-mode), and unsets \
       $(b,--allowed-failures) and $(b,--default-linters)."
      ~f:(fun debug ->
        debug_level_linters := if debug then 2 else 0 ;
        debug )
      [debug; developer_mode] [default_linters; keep_going]
  in
  ( bo_debug
  , developer_mode
  , debug
  , debug_exceptions
  , debug_level_analysis
  , debug_level_capture
  , debug_level_linters
  , debug_level_test_determinator
  , default_linters
  , filtering
  , frontend_tests
  , keep_going
  , linters_developer_mode
  , models_mode
  , only_cheap_debug
  , print_buckets
  , print_logs
  , print_types
  , reports_include_ml_loc
  , trace_error
  , write_html
  , write_html_whitelist_regex
  , write_dotty )


and dependencies =
  CLOpt.mk_bool ~deprecated:["dependencies"] ~long:"dependencies"
    ~in_help:InferCommand.[(Capture, manual_java)]
    "Translate all the dependencies during the capture. The classes in the given jar file will be \
     translated. No sources needed."


and differential_filter_files =
  CLOpt.mk_string_opt ~long:"differential-filter-files"
    ~in_help:InferCommand.[(Report, manual_generic)]
    "Specify the file containing the list of source files for which a differential report is \
     desired. Source files should be specified relative to project root or be absolute"


and differential_filter_set =
  CLOpt.mk_symbol_seq ~long:"differential-filter-set" ~eq:PolyVariantEqual.( = )
    "Specify which set of the differential results is filtered with the modified files provided \
     through the $(b,--differential-modified-files) argument. By default it is applied to all \
     sets ($(b,introduced), $(b,fixed), and $(b,preexisting))"
    ~symbols:[("introduced", `Introduced); ("fixed", `Fixed); ("preexisting", `Preexisting)]
    ~default:[`Introduced; `Fixed; `Preexisting]


and () =
  let mk b ?deprecated ~long ?default doc =
    let (_ : string list ref) =
      CLOpt.mk_string_list ?deprecated ~long
        ~f:(fun issue_id ->
          let issue = IssueType.from_string issue_id in
          IssueType.set_enabled issue b ; issue_id )
        ?default ~meta:"issue_type"
        ~in_help:InferCommand.[(Report, manual_generic)]
        doc
    in
    ()
  in
  let disabled_issues_ids =
    IssueType.all_issues ()
    |> List.filter_map ~f:(fun issue ->
           if not issue.IssueType.enabled then Some issue.IssueType.unique_id else None )
  in
  mk false ~default:disabled_issues_ids ~long:"disable-issue-type"
    ~deprecated:["disable_checks"; "-disable-checks"]
    (Printf.sprintf
       "Do not show reports coming from this type of issue. Each checker can report a range of \
        issue types. This option provides fine-grained filtering over which types of issue should \
        be reported once the checkers have run. In particular, note that disabling issue types \
        does not make the corresponding checker not run.\n\
       \ By default, the following issue types are disabled: %s.\n\n\
       \ See also $(b,--report-issue-type).\n"
       (String.concat ~sep:", " disabled_issues_ids)) ;
  mk true ~long:"enable-issue-type"
    ~deprecated:["enable_checks"; "-enable-checks"]
    "Show reports coming from this type of issue. By default, all issue types are enabled except \
     the ones listed in $(b,--disable-issue-type). Note that enabling issue types does not make \
     the corresponding checker run; see individual checker options to turn them on or off."


and dotty_cfg_libs =
  CLOpt.mk_bool ~deprecated:["dotty_no_cfg_libs"] ~long:"dotty-cfg-libs" ~default:true
    "Print the cfg of the code coming from the libraries"


and dump_duplicate_symbols =
  CLOpt.mk_bool ~long:"dump-duplicate-symbols"
    ~in_help:InferCommand.[(Capture, manual_clang)]
    "Dump all symbols with the same name that are defined in more than one file."


and eradicate_condition_redundant =
  CLOpt.mk_bool ~long:"eradicate-condition-redundant" "Condition redundant warnings"


and eradicate_field_not_mutable =
  CLOpt.mk_bool ~long:"eradicate-field-not-mutable" "Field not mutable warnings"


and eradicate_field_over_annotated =
  CLOpt.mk_bool ~long:"eradicate-field-over-annotated" "Field over-annotated warnings"


and eradicate_optional_present =
  CLOpt.mk_bool ~long:"eradicate-optional-present" "Check for @Present annotations"


and eradicate_return_over_annotated =
  CLOpt.mk_bool ~long:"eradicate-return-over-annotated" "Return over-annotated warning"


and eradicate_debug =
  CLOpt.mk_bool ~long:"eradicate-debug" "Print debug info when errors are found"


and eradicate_verbose =
  CLOpt.mk_bool ~long:"eradicate-verbose" "Print initial and final typestates"


and external_java_packages =
  CLOpt.mk_string_list ~long:"external-java-packages"
    ~in_help:InferCommand.[(Analyze, manual_java)]
    ~meta:"prefix"
    "Specify a list of Java package prefixes for external Java packages. If set, the analysis \
     will not report non-actionable warnings on those packages."


and fail_on_bug =
  CLOpt.mk_bool ~deprecated:["-fail-on-bug"] ~long:"fail-on-issue" ~default:false
    ~in_help:InferCommand.[(Run, manual_generic)]
    (Printf.sprintf "Exit with error code %d if Infer found something to report"
       fail_on_issue_exit_code)


and fcp_apple_clang =
  CLOpt.mk_path_opt ~long:"fcp-apple-clang" ~meta:"path" "Specify the path to Apple Clang"


and fcp_syntax_only = CLOpt.mk_bool ~long:"fcp-syntax-only" "Skip creation of object files"

and file_renamings =
  CLOpt.mk_path_opt ~long:"file-renamings"
    ~in_help:InferCommand.[(ReportDiff, manual_generic)]
    "JSON with a list of file renamings to use while computing differential reports"


and filter_paths =
  CLOpt.mk_bool ~long:"filter-paths" ~default:true "Filters specified in .inferconfig"


and filter_report =
  CLOpt.mk_string_list ~long:"filter-report"
    ~in_help:InferCommand.[(Report, manual_generic); (Run, manual_generic)]
    "Specify a filter for issues to report. If multiple filters are specified, they are applied \
     in the order in which they are specified. Each filter is applied to each issue detected, and \
     only issues which are accepted by all filters are reported. Each filter is of the form: \
     `<issue_type_regex>:<filename_regex>:<reason_string>`. The first two components are OCaml \
     Str regular expressions, with an optional `!` character prefix. If a regex has a `!` prefix, \
     the polarity is inverted, and the filter becomes a \"blacklist\" instead of a \"whitelist\". \
     Each filter is interpreted as an implication: an issue matches if it does not match the \
     `issue_type_regex` or if it does match the `filename_regex`. The filenames that are tested \
     by the regex are relative to the `--project-root` directory. The `<reason_string>` is a \
     non-empty string used to explain why the issue was filtered."


and flavors =
  CLOpt.mk_bool ~deprecated:["-use-flavors"] ~long:"flavors"
    ~in_help:InferCommand.[(Capture, manual_buck_flavors)]
    "Buck integration using Buck flavors (clang only), eg $(i,`infer --flavors -- buck build \
     //foo:bar#infer`)"


and force_delete_results_dir =
  CLOpt.mk_bool ~long:"force-delete-results-dir" ~default:false
    ~in_help:
      InferCommand.
        [ (Capture, manual_generic)
        ; (Compile, manual_generic)
        ; (Diff, manual_generic)
        ; (Run, manual_generic) ]
    "Do not refuse to delete the results directory if it doesn't look like an infer results \
     directory."


and force_integration =
  CLOpt.mk_symbol_opt ~long:"force-integration" ~meta:"command"
    ~symbols:(List.Assoc.inverse build_system_exe_assoc)
    ~in_help:InferCommand.[(Capture, manual_generic); (Run, manual_generic)]
    (Printf.sprintf
       "Proceed as if the first argument after $(b,--) was $(i,command). Possible values: %s."
       ( List.map build_system_exe_assoc ~f:(fun (_, s) -> Printf.sprintf "$(i,%s)" s)
       |> String.concat ~sep:", " ))


and from_json_report =
  CLOpt.mk_path_opt ~long:"from-json-report"
    ~in_help:InferCommand.[(Report, manual_generic)]
    ~meta:"report.json"
    "Load analysis results from a report file (default is to load the results from the specs \
     files generated by the analysis)."


and frontend_stats =
  CLOpt.mk_bool ~deprecated:["fs"] ~deprecated_no:["nfs"] ~long:"frontend-stats"
    "Output statistics about the capture phase to *.o.astlog (clang only)"


and function_pointer_specialization =
  CLOpt.mk_bool ~long:"function-pointer-specialization" ~default:false
    "Do function pointer preprocessing (clang only)."


and gen_previous_build_command_script =
  CLOpt.mk_string_opt ~long:"gen-previous-build-command-script"
    ~in_help:InferCommand.[(Diff, manual_generic)]
    ~meta:"shell"
    "Specify a script that outputs the build command to capture in the previous version of the \
     project. The script should output the command on stdout. For example \"echo make\"."


and generated_classes =
  CLOpt.mk_path_opt ~long:"generated-classes"
    ~in_help:InferCommand.[(Capture, manual_java)]
    "Specify where to load the generated class files"


and genrule_mode =
  CLOpt.mk_bool ~default:false ~long:"genrule-mode"
    "Enable the genrule compatibility mode used for the Buck integration"


and headers =
  CLOpt.mk_bool ~deprecated:["headers"; "hd"] ~deprecated_no:["no_headers"; "nhd"] ~long:"headers"
    ~in_help:InferCommand.[(Capture, manual_clang)]
    "Analyze code in header files"


and help =
  let var = ref `None in
  CLOpt.mk_set var `Help ~long:"help"
    ~in_help:(List.map InferCommand.all_commands ~f:(fun command -> (command, manual_generic)))
    "Show this manual" ;
  CLOpt.mk_set var `HelpFull ~long:"help-full"
    ~in_help:(List.map InferCommand.all_commands ~f:(fun command -> (command, manual_generic)))
    (Printf.sprintf "Show this manual with all internal options in the %s section" manual_internal) ;
  var


and help_format =
  CLOpt.mk_symbol ~long:"help-format"
    ~symbols:[("auto", `Auto); ("groff", `Groff); ("pager", `Pager); ("plain", `Plain)]
    ~eq:PolyVariantEqual.( = ) ~default:`Auto
    ~in_help:(List.map InferCommand.all_commands ~f:(fun command -> (command, manual_generic)))
    "Show this help in the specified format. $(b,auto) sets the format to $(b,plain) if the \
     environment variable $(b,TERM) is \"dumb\" or undefined, and to $(b,pager) otherwise."


and html =
  CLOpt.mk_bool ~long:"html"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Generate html report."


and hoisting_report_only_expensive =
  CLOpt.mk_bool ~long:"hoisting-report-only-expensive" ~default:true
    ~in_help:InferCommand.[(Report, manual_hoisting)]
    "[Hoisting] Report loop-invariant calls only when the function is expensive, i.e. at least \
     linear"


and icfg_dotty_outfile =
  CLOpt.mk_path_opt ~long:"icfg-dotty-outfile" ~meta:"path"
    "If set, specifies path where .dot file should be written, it overrides the path for all \
     other options that would generate icfg file otherwise"


and iphoneos_target_sdk_version =
  CLOpt.mk_string_opt ~long:"iphoneos-target-sdk-version"
    ~in_help:InferCommand.[(Capture, manual_clang_linters)]
    "Specify the target SDK version to use for iphoneos"


and iphoneos_target_sdk_version_path_regex =
  CLOpt.mk_string_list ~long:"iphoneos-target-sdk-version-path-regex"
    ~in_help:InferCommand.[(Capture, manual_clang_linters)]
    "To pass a specific target SDK version to use for iphoneos in a particular path, with the \
     format path:version (can be specified multiple times)"


and issues_fields =
  CLOpt.mk_symbol_seq ~long:"issues-fields"
    ~in_help:InferCommand.[(Report, manual_generic)]
    ~default:
      [ `Issue_field_file
      ; `Issue_field_procedure
      ; `Issue_field_line_offset
      ; `Issue_field_bug_type
      ; `Issue_field_bucket
      ; `Issue_field_severity
      ; `Issue_field_bug_trace ]
    ~symbols:issues_fields_symbols ~eq:PolyVariantEqual.( = )
    "Fields to emit with $(b,--issues-tests)"


and issues_tests =
  CLOpt.mk_path_opt ~long:"issues-tests"
    ~in_help:InferCommand.[(Report, manual_generic)]
    ~meta:"file" "Write a list of issues in a format suitable for tests to $(i,file)"


and issues_txt =
  CLOpt.mk_path_opt ~deprecated:["bugs_txt"] ~long:"issues-txt"
    ~in_help:InferCommand.[(Report, manual_generic)]
    ~meta:"file" "Write a list of issues in text format to $(i,file) (default: infer-out/bugs.txt)"


and iterations =
  CLOpt.mk_int ~deprecated:["iterations"] ~long:"iterations" ~default:1 ~meta:"int"
    "Specify the maximum number of operations for each function, expressed as a multiple of \
     symbolic operations and a multiple of seconds of elapsed time"


and java_jar_compiler =
  CLOpt.mk_path_opt ~long:"java-jar-compiler"
    ~in_help:InferCommand.[(Capture, manual_java)]
    ~meta:"path" "Specify the Java compiler jar used to generate the bytecode"


and job_id = CLOpt.mk_string_opt ~long:"job-id" "Specify the job ID of this Infer run."

and jobs =
  CLOpt.mk_int ~deprecated:["-multicore"] ~long:"jobs" ~short:'j' ~default:ncpu
    ~default_to_string:(fun _ -> "<number of cores>")
    ~in_help:InferCommand.[(Analyze, manual_generic)]
    ~meta:"int" "Run the specified number of analysis jobs simultaneously"


and join_cond =
  CLOpt.mk_int ~deprecated:["join_cond"] ~long:"join-cond" ~default:1 ~meta:"int"
    {|Set the strength of the final information-loss check used by the join:
- 0 = use the most aggressive join for preconditions
- 1 = use the least aggressive join for preconditions
|}


and liveness_dangerous_classes =
  CLOpt.mk_json ~long:"liveness-dangerous-classes"
    ~in_help:InferCommand.[(Analyze, manual_clang)]
    "Specify classes where the destructor should be ignored when computing liveness. In other \
     words, assignement to variables of these types (or common wrappers around these types such \
     as $(i,unique_ptr<type>)) will count as dead stores when the variables are not read \
     explicitly by the program."


and log_events =
  CLOpt.mk_bool ~long:"log-events"
    ~in_help:InferCommand.[(Run, manual_generic)]
    "Turn on the feature that logs events in a machine-readable format"


and log_file =
  CLOpt.mk_string ~deprecated:["out_file"; "-out-file"] ~long:"log-file" ~meta:"file"
    ~default:"logs" "Specify the file to use for logging"


and log_skipped =
  CLOpt.mk_bool ~long:"log-skipped"
    ~in_help:InferCommand.[(Run, manual_generic)]
    "Turn on the feature that logs skipped functions (one per file) in a machine-readable format"


and perf_profiler_data_file =
  CLOpt.mk_path_opt ~long:"perf-profiler-data-file"
    ~in_help:InferCommand.[(Analyze, manual_generic)]
    ~meta:"file" "Specify the file containing perf profiler data to read"


and linter =
  CLOpt.mk_string_opt ~long:"linter"
    ~in_help:InferCommand.[(Capture, manual_clang_linters)]
    "From the linters available, only run this one linter. (Useful together with \
     $(b,--linters-developer-mode))"


and linters_def_file =
  CLOpt.mk_path_list ~default:[] ~long:"linters-def-file"
    ~in_help:InferCommand.[(Capture, manual_clang_linters)]
    ~meta:"file" "Specify the file containing linters definition (e.g. 'linters.al')"


and linters_def_folder =
  let linters_def_folder =
    CLOpt.mk_path_list ~default:[] ~long:"linters-def-folder"
      ~in_help:InferCommand.[(Capture, manual_clang_linters)]
      ~meta:"dir" "Specify the folder containing linters files with extension .al"
  in
  let () =
    CLOpt.mk_set linters_def_folder [] ~long:"reset-linters-def-folder"
      "Reset the list of folders containing linters definitions to be empty (see \
       $(b,linters-def-folder))."
  in
  linters_def_folder


and linters_doc_url =
  CLOpt.mk_string_list ~long:"linters-doc-url"
    ~in_help:InferCommand.[(Capture, manual_clang_linters)]
    "Specify custom documentation URL for some linter that overrides the default one. Useful if \
     your project has specific ways of fixing a lint error that is not true in general or public \
     info. Format: linter_name:doc_url."


and linters_ignore_clang_failures =
  CLOpt.mk_bool ~long:"linters-ignore-clang-failures"
    ~in_help:InferCommand.[(Capture, manual_clang_linters)]
    ~default:false "Continue linting files even if some compilation fails."


and linters_validate_syntax_only =
  CLOpt.mk_bool ~long:"linters-validate-syntax-only"
    ~in_help:InferCommand.[(Capture, manual_clang_linters)]
    ~default:false
    "Validate syntax of AL files, then emit possible errors in JSON format to stdout"


and load_average =
  CLOpt.mk_float_opt ~long:"load-average" ~short:'l'
    ~in_help:InferCommand.[(Capture, manual_generic)]
    ~meta:"float"
    "Do not start new parallel jobs if the load average is greater than that specified (Buck and \
     make only)"


and margin =
  CLOpt.mk_int ~deprecated:["set_pp_margin"] ~long:"margin" ~default:100 ~meta:"int"
    "Set right margin for the pretty printing functions"


and max_nesting =
  CLOpt.mk_int_opt ~long:"max-nesting"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Level of nested procedure calls to show. Trace elements beyond the maximum nesting level are \
     skipped. If omitted, all levels are shown."


and method_decls_info =
  CLOpt.mk_path_opt ~long:"method-decls-info" ~meta:"method_decls_info.json"
    "Specifies the file containing the method declarations info (eg. start line, end line, class, \
     method name, etc.) when Infer is run Test Determinator mode with $(b,--test-determinator)."


and memcached =
  CLOpt.mk_bool ~long:"memcached" ~default:false
    "EXPERIMENTAL: Use memcached caching summaries during analysis."


and memcached_size_mb =
  CLOpt.mk_int ~long:"memcached-size-mb" ~default:2048
    "EXPERIMENTAL: Default memcached size in megabytes."


and merge =
  CLOpt.mk_bool ~deprecated:["merge"] ~long:"merge"
    ~in_help:InferCommand.[(Analyze, manual_buck_flavors)]
    "Merge the captured results directories specified in the dependency file"


and ml_buckets =
  CLOpt.mk_symbol_seq ~deprecated:["ml_buckets"; "-ml_buckets"] ~long:"ml-buckets"
    ~default:[`MLeak_cf]
    ~in_help:InferCommand.[(Analyze, manual_clang)]
    {|Specify the memory leak buckets to be checked in C++:
- $(b,cpp) from C++ code
|}
    ~symbols:ml_bucket_symbols ~eq:PolyVariantEqual.( = )


and modified_lines =
  CLOpt.mk_path_opt ~long:"modified-lines"
    "Specifies the file containing the modified lines when Infer is run Test Determinator mode \
     with $(b,--test-determinator)."


and modified_targets =
  CLOpt.mk_path_opt ~deprecated:["modified_targets"] ~long:"modified-targets" ~meta:"file"
    "Read the file of Buck targets modified since the last analysis"


and monitor_prop_size =
  CLOpt.mk_bool ~deprecated:["monitor_prop_size"] ~long:"monitor-prop-size"
    "Monitor size of props, and print every time the current max is exceeded"


and nelseg = CLOpt.mk_bool ~deprecated:["nelseg"] ~long:"nelseg" "Use only nonempty lsegs"

and nullable_annotation =
  CLOpt.mk_string_opt ~long:"nullable-annotation-name" "Specify custom nullable annotation name"


and nullsafe_strict_containers =
  CLOpt.mk_bool ~long:"nullsafe-strict-containers" ~default:false
    "Warn when containers are used with nullable keys or values"


and only_footprint =
  CLOpt.mk_bool ~deprecated:["only_footprint"] ~long:"only-footprint" "Skip the re-execution phase"


and only_show =
  CLOpt.mk_bool ~long:"only-show"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Show the list of reports and exit"


and passthroughs =
  CLOpt.mk_bool ~long:"passthroughs" ~default:false
    "In error traces, show intermediate steps that propagate data. When false, error traces are \
     shorter and show only direct flow via souces/sinks"


and patterns_modeled_expensive =
  let long = "modeled-expensive" in
  ( long
  , CLOpt.mk_json ~deprecated:["modeled_expensive"] ~long
      "Matcher or list of matchers for methods that should be considered expensive by the \
       performance critical checker." )


and patterns_never_returning_null =
  let long = "never-returning-null" in
  ( long
  , CLOpt.mk_json ~deprecated:["never_returning_null"] ~long
      "Matcher or list of matchers for functions that never return $(i,null)." )


and patterns_skip_implementation =
  let long = "skip-implementation" in
  ( long
  , CLOpt.mk_json ~long
      "Matcher or list of matchers for names of files where we only want to translate the method \
       declaration, skipping the body of the methods (Java only)." )


and patterns_skip_translation =
  let long = "skip-translation" in
  ( long
  , CLOpt.mk_json ~deprecated:["skip_translation"] ~long
      "Matcher or list of matchers for names of files that should not be analyzed at all." )


and pmd_xml =
  CLOpt.mk_bool ~long:"pmd-xml"
    ~in_help:InferCommand.[(Run, manual_generic)]
    "Output issues in (PMD) XML format"


and precondition_stats =
  CLOpt.mk_bool ~deprecated:["precondition_stats"] ~long:"precondition-stats"
    "Print stats about preconditions to standard output"


and previous_to_current_script =
  CLOpt.mk_string_opt ~long:"previous-to-current-script"
    ~in_help:InferCommand.[(Diff, manual_generic)]
    ~meta:"shell"
    "Specify a script to checkout the current version of the project. The project is supposed to \
     already be at that current version when running $(b,infer diff); the script is used after \
     having analyzed the current and previous versions of the project, to restore the project to \
     the current version."


and print_active_checkers =
  CLOpt.mk_bool ~long:"print-active-checkers"
    ~in_help:InferCommand.[(Analyze, manual_generic)]
    "Print the active checkers before starting the analysis"


and print_builtins =
  CLOpt.mk_bool ~deprecated:["print_builtins"] ~long:"print-builtins"
    "Print the builtin functions and exit"


and print_log_identifier =
  CLOpt.mk_bool ~long:"print-log-identifier"
    ~in_help:InferCommand.[(Run, manual_generic)]
    "Print the unique identifier that is common to all logged events"


and print_using_diff =
  CLOpt.mk_bool ~deprecated_no:["noprintdiff"] ~long:"print-using-diff" ~default:true
    "Highlight the difference w.r.t. the previous prop when printing symbolic execution debug info"


and procedures =
  CLOpt.mk_bool ~long:"procedures"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Print functions and methods discovered by infer"


and procedures_attributes =
  CLOpt.mk_bool ~long:"procedures-attributes"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Print the attributes of each procedure in the output of $(b,--procedures)"


and procedures_definedness =
  CLOpt.mk_bool ~long:"procedures-definedness" ~default:true
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Include procedures definedness in the output of $(b,--procedures), i.e. whether the \
     procedure definition was found, or only the procedure declaration, or the procedure is an \
     auto-generated Objective-C accessor"


and procedures_filter =
  CLOpt.mk_string_opt ~long:"procedures-filter" ~meta:"filter"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "With $(b,--procedures), only print functions and methods (procedures) matching the specified \
     $(i,filter). A procedure filter is of the form $(i,path_pattern:procedure_name). Patterns \
     are interpreted as OCaml Str regular expressions. For instance, to keep only methods named \
     \"foo\", one can use the filter \".*:foo\", or \"foo\" for short."


and procedures_name =
  CLOpt.mk_bool ~long:"procedures-name"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Include procedures names in the output of $(b,--procedures)"


and procedures_per_process =
  CLOpt.mk_int ~long:"procedures-per-process" ~default:1000 ~meta:"int"
    "Specify the number of procedures to analyze per process when using \
     $(b,--per-procedure-parallelism).  If 0 is specified, each file is divided into $(b,--jobs) \
     groups of procedures."


and procedures_source_file =
  CLOpt.mk_bool ~long:"procedures-source-file" ~default:true
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Include the source file in which the procedure definition or declaration was found in the \
     output of $(b,--procedures)"


and procs_csv =
  CLOpt.mk_path_opt ~deprecated:["procs"] ~long:"procs-csv" ~meta:"file"
    "Write statistics for each procedure in CSV format to a file"


and progress_bar =
  CLOpt.mk_bool ~deprecated:["pb"] ~deprecated_no:["no_progress_bar"; "npb"] ~short:'p'
    ~long:"progress-bar" ~default:true
    ~in_help:InferCommand.[(Run, manual_generic)]
    "Show a progress bar"


and progress_bar_style =
  CLOpt.mk_symbol ~long:"progress-bar-style"
    ~symbols:[("auto", `Auto); ("plain", `Plain); ("multiline", `MultiLine)]
    ~eq:Pervasives.( = ) ~default:`Auto
    ~in_help:[(Analyze, manual_generic); (Capture, manual_generic)]
    "Style of the progress bar. $(b,auto) selects $(b,multiline) if connected to a tty, otherwise \
     $(b,plain)."


and project_root =
  CLOpt.mk_path
    ~deprecated:["project_root"; "-project_root"; "pr"]
    ~long:"project-root" ~short:'C' ~default:CLOpt.init_work_dir
    ~default_to_string:(fun _ -> ".")
    ~in_help:
      InferCommand.
        [ (Analyze, manual_generic)
        ; (Capture, manual_generic)
        ; (Run, manual_generic)
        ; (Report, manual_generic) ]
    ~meta:"dir" "Specify the root directory of the project"


and pulse_max_disjuncts =
  CLOpt.mk_int ~long:"pulse-max-disjuncts" ~default:20
    "Under-approximate after $(i,int) disjunctions in the domain"


and pulse_widen_threshold =
  CLOpt.mk_int ~long:"pulse-widen-threshold" ~default:3
    "Under-approximate after $(i,int) loop iterations"


and quandary_endpoints =
  CLOpt.mk_json ~long:"quandary-endpoints"
    ~in_help:InferCommand.[(Analyze, manual_quandary)]
    "Specify endpoint classes for Quandary"


and quandary_sanitizers =
  CLOpt.mk_json ~long:"quandary-sanitizers"
    ~in_help:InferCommand.[(Analyze, manual_quandary)]
    "Specify custom sanitizers for Quandary"


and quandary_sources =
  CLOpt.mk_json ~long:"quandary-sources"
    ~in_help:InferCommand.[(Analyze, manual_quandary)]
    "Specify custom sources for Quandary"


and quandary_sinks =
  CLOpt.mk_json ~long:"quandary-sinks"
    ~in_help:InferCommand.[(Analyze, manual_quandary)]
    "Specify custom sinks for Quandary"


and quiet =
  CLOpt.mk_bool ~long:"quiet" ~short:'q' ~default:false
    ~in_help:InferCommand.[(Analyze, manual_generic); (Report, manual_generic)]
    "Do not print specs on standard output (default: only print for the $(b,report) command)"


and racerd_guardedby =
  CLOpt.mk_bool ~long:"racerd-guardedby" ~default:false
    ~in_help:InferCommand.[(Analyze, manual_racerd)]
    "Check @GuardedBy annotations with RacerD"


and reactive =
  CLOpt.mk_bool ~deprecated:["reactive"] ~long:"reactive" ~short:'r'
    ~in_help:InferCommand.[(Analyze, manual_generic)]
    "Reactive mode: the analysis starts from the files captured since the $(i,infer) command \
     started"


and reactive_capture =
  CLOpt.mk_bool ~long:"reactive-capture"
    "Compile source files only when required by analyzer (clang only)"


and reanalyze = CLOpt.mk_bool ~long:"reanalyze" "Rerun the analysis"

and relative_path_backtrack =
  CLOpt.mk_int ~long:"backtrack-level" ~default:0 ~meta:"int"
    "Maximum level of backtracking to convert an absolute path to path relative to the common \
     prefix between the project root and the path. For instance, with bactraking level 1, it will \
     convert /my/source/File.java with project root /my/root into ../source/File.java"


and report =
  CLOpt.mk_bool ~long:"report" ~default:true
    ~in_help:InferCommand.[(Analyze, manual_generic); (Run, manual_generic)]
    "Run the reporting phase once the analysis has completed"


and report_current =
  CLOpt.mk_path_opt ~long:"report-current"
    ~in_help:InferCommand.[(ReportDiff, manual_generic)]
    "report of the latest revision"


and report_custom_error = CLOpt.mk_bool ~long:"report-custom-error" ""

and report_force_relative_path =
  CLOpt.mk_bool ~long:"report-force-relative-path" ~default:false
    ~in_help:InferCommand.[(Analyze, manual_generic); (Run, manual_generic)]
    "Force converting an absolute path to a relative path to the root directory"


and report_formatter =
  CLOpt.mk_symbol ~long:"report-formatter"
    ~in_help:InferCommand.[(Report, manual_generic)]
    ~default:`Phabricator_formatter
    ~symbols:[("none", `No_formatter); ("phabricator", `Phabricator_formatter)]
    ~eq:PolyVariantEqual.( = ) "Which formatter to use when emitting the report"


and report_hook =
  CLOpt.mk_string_opt ~long:"report-hook"
    ~in_help:InferCommand.[(Analyze, manual_generic); (Run, manual_generic)]
    ~default:(lib_dir ^/ "python" ^/ "report.py")
    ~default_to_string:(fun _ -> "<infer installation directory>/lib/python/report.py")
    ~meta:"script"
    "Specify a script to be executed after the analysis results are written.  This script will be \
     passed, $(b,--issues-json), $(b,--issues-txt), $(b,--issues-xml), $(b,--project-root), and \
     $(b,--results-dir)."


and report_previous =
  CLOpt.mk_path_opt ~long:"report-previous"
    ~in_help:InferCommand.[(ReportDiff, manual_generic)]
    "Report of the base revision to use for comparison"


and rest =
  CLOpt.mk_rest_actions
    ~in_help:InferCommand.[(Capture, manual_generic); (Run, manual_generic)]
    "Stop argument processing, use remaining arguments as a build command" ~usage:exe_usage
    (fun build_exe ->
      match Filename.basename build_exe with "java" | "javac" -> CLOpt.Javac | _ -> CLOpt.NoParse
      )


and results_dir =
  CLOpt.mk_path ~deprecated:["results_dir"; "-out"] ~long:"results-dir" ~short:'o'
    ~default:(CLOpt.init_work_dir ^/ "infer-out")
    ~default_to_string:(fun _ -> "./infer-out")
    ~in_help:
      InferCommand.
        [ (Analyze, manual_generic)
        ; (Capture, manual_generic)
        ; (Explore, manual_generic)
        ; (Run, manual_generic)
        ; (Report, manual_generic) ]
    ~meta:"dir" "Write results and internal files in the specified directory"


and seconds_per_iteration =
  CLOpt.mk_float_opt ~deprecated:["seconds_per_iteration"] ~long:"seconds-per-iteration"
    ~meta:"float" "Set the number of seconds per iteration (see $(b,--iterations))"


and select =
  CLOpt.mk_int_opt ~long:"select" ~meta:"N"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Select bug number $(i,N). If omitted, prompt for input."


and siof_safe_methods =
  CLOpt.mk_string_list ~long:"siof-safe-methods"
    ~in_help:InferCommand.[(Analyze, manual_siof)]
    "Methods that are SIOF-safe; \"foo::bar\" will match \"foo::bar()\", \"foo<int>::bar()\", \
     etc. (can be specified multiple times)"


and skip_analysis_in_path =
  CLOpt.mk_string_list ~deprecated:["-skip-clang-analysis-in-path"] ~long:"skip-analysis-in-path"
    ~in_help:InferCommand.[(Capture, manual_generic); (Run, manual_generic)]
    ~meta:"path_prefix_OCaml_regex"
    "Ignore files whose path matches the given prefix (can be specified multiple times)"


and skip_analysis_in_path_skips_compilation =
  CLOpt.mk_bool ~long:"skip-analysis-in-path-skips-compilation"
    ~in_help:InferCommand.[(Report, manual_generic)]
    ~default:false "Whether paths in --skip-analysis-in-path should be compiled or not"


and skip_duplicated_types =
  CLOpt.mk_bool ~long:"skip-duplicated-types" ~default:true
    ~in_help:InferCommand.[(ReportDiff, manual_generic)]
    "Skip fixed-then-introduced duplicated types while computing differential reports"


and skip_translation_headers =
  CLOpt.mk_string_list ~deprecated:["skip_translation_headers"] ~long:"skip-translation-headers"
    ~in_help:InferCommand.[(Capture, manual_clang)]
    ~meta:"path_prefix" "Ignore headers whose path matches the given prefix"


and source_preview =
  CLOpt.mk_bool ~long:"source-preview" ~default:true
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "print code excerpts around trace elements"


and source_files =
  CLOpt.mk_bool ~long:"source-files"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Print source files discovered by infer"


and source_files_cfg =
  CLOpt.mk_bool ~long:"source-files-cfg"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    (Printf.sprintf
       "Output a dotty file in infer-out/%s for each source file in the output of \
        $(b,--source-files)"
       captured_dir_name)


and source_files_filter =
  CLOpt.mk_string_opt ~long:"source-files-filter" ~meta:"filter"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "With $(b,--source-files), only print source files matching the specified $(i,filter). The \
     filter is a pattern that should match the file path. Patterns are interpreted as OCaml Str \
     regular expressions."


and source_files_type_environment =
  CLOpt.mk_bool ~long:"source-files-type-environment"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Print the type environment of each source file in the output of $(b,--source-files)"


and source_files_procedure_names =
  CLOpt.mk_bool ~long:"source-files-procedure-names"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Print the names of procedure of each source file in the output of $(b,--source-files)"


and source_files_freshly_captured =
  CLOpt.mk_bool ~long:"source-files-freshly-captured"
    ~in_help:InferCommand.[(Explore, manual_generic)]
    "Print whether the source file has been captured in the most recent capture phase in the \
     output of $(b,--source-files)."


and sources = CLOpt.mk_string_list ~long:"sources" "Specify the list of source files"

and sourcepath = CLOpt.mk_string_opt ~long:"sourcepath" "Specify the sourcepath"

and starvation_skip_analysis =
  CLOpt.mk_json ~long:"starvation-skip-analysis"
    "Specify combinations of class/method list that should be skipped during starvation analysis"


and spec_abs_level =
  CLOpt.mk_int ~deprecated:["spec_abs_level"] ~long:"spec-abs-level" ~default:1 ~meta:"int"
    {|Set the level of abstracting the postconditions of discovered specs:
- 0 = nothing special
- 1 = filter out redundant posts implied by other posts
|}


and specs_library =
  let specs_library =
    CLOpt.mk_path_list ~deprecated:["lib"] ~long:"specs-library" ~short:'L' ~meta:"dir|jar"
      "Search for .spec files in given directory or jar file"
  in
  let (_ : string ref) =
    (* Given a filename with a list of paths, convert it into a list of string iff they are
       absolute *)
    let read_specs_dir_list_file fname =
      match Utils.read_file (resolve fname) with
      | Ok pathlist ->
          pathlist
      | Error error ->
          L.(die UserError) "cannot read file '%s' from cwd '%s': %s" fname (Sys.getcwd ()) error
    in
    (* Add the newline-separated directories listed in <file> to the list of directories to be
       searched for .spec files *)
    CLOpt.mk_path
      ~deprecated:["specs-dir-list-file"; "-specs-dir-list-file"]
      ~long:"specs-library-index" ~default:""
      ~f:(fun file ->
        specs_library := read_specs_dir_list_file file @ !specs_library ;
        "" )
      ~in_help:InferCommand.[(Analyze, manual_generic)]
      ~meta:"file" ""
  in
  specs_library


and sqlite_lock_timeout =
  (* some lame estimate: when the frontend writes CFGs to disk, it may take a few seconds to write
     one CFG and all the cores may be trying to write to the database at the same time. This means
     one process might wait (a few seconds) * (number of cores) to write its CFG. *)
  let five_seconds_per_core = ncpu * 5_000 in
  CLOpt.mk_int ~long:"sqlite-lock-timeout" ~default:five_seconds_per_core
    ~default_to_string:(fun _ -> "five seconds times number of cores")
    ~in_help:
      InferCommand.[(Analyze, manual_generic); (Capture, manual_generic); (Run, manual_generic)]
    "Timeout for SQLite results database operations, in milliseconds."


and sqlite_vfs =
  let default =
    match Utils.read_file "/proc/version" with
    | Result.Ok [line] ->
        let re = Str.regexp "Linux.+-Microsoft" in
        (* on WSL (bash on Windows) standard SQLite VFS can't be used, see WSL/issues/1927 WSL/issues/2395 *)
        if Str.string_match re line 0 then Some "unix-excl" else None
    | _ ->
        None
  in
  CLOpt.mk_string_opt ?default ~long:"sqlite-vfs" "VFS for SQLite"


and stats_report =
  CLOpt.mk_path_opt ~long:"stats-report" ~meta:"file"
    "Write a report of the analysis results to a file"


and subtype_multirange =
  CLOpt.mk_bool ~deprecated:["subtype_multirange"] ~long:"subtype-multirange" ~default:true
    "Use the multirange subtyping domain"


and symops_per_iteration =
  CLOpt.mk_int_opt ~deprecated:["symops_per_iteration"] ~long:"symops-per-iteration" ~meta:"int"
    "Set the number of symbolic operations per iteration (see $(b,--iterations))"


and test_determinator =
  CLOpt.mk_bool ~long:"test-determinator" ~default:false
    "Run infer in Test Determinator mode. It is used together with the $(b,--modified-lines) and \
     $(b,--test-profiler) flags, which speficy the relevant arguments."


and test_determinator_clang =
  CLOpt.mk_bool ~long:"test-determinator-clang" ~default:false
    "Run infer in Test Determinator mode for clang. It is used together with the \
     $(b,--modified-lines)."


and test_filtering =
  CLOpt.mk_bool ~deprecated:["test_filtering"] ~long:"test-filtering"
    "List all the files Infer can report on (should be called from the root of the project)"


and topl_properties =
  CLOpt.mk_path_list ~default:[] ~long:"topl-properties"
    "[EXPERIMENTAL] Specify a file containing a temporal property definition (e.g., jdk.topl)."


and profiler_samples =
  CLOpt.mk_path_opt ~long:"profiler-samples"
    "File containing the profiler samples when Infer is run Test Determinator mode with \
     $(b,--test-determinator)."


and starvation_strict_mode =
  CLOpt.mk_bool ~long:"starvation-strict-mode" ~default:true
    "During starvation analysis, report strict mode violations (Android only)"


and testing_mode =
  CLOpt.mk_bool
    ~deprecated:["testing_mode"; "-testing_mode"; "tm"]
    ~deprecated_no:["ntm"] ~long:"testing-mode"
    "Mode for testing, where no headers are translated, and dot files are created (clang only)"


and threadsafe_aliases =
  CLOpt.mk_json ~long:"threadsafe-aliases"
    ~in_help:InferCommand.[(Analyze, manual_racerd)]
    "Specify custom annotations that should be considered aliases of @ThreadSafe"


and trace_events =
  CLOpt.mk_bool ~long:"trace-events"
    (Printf.sprintf "Emit Chrome performance trace events in infer-out/%s" trace_events_file)


and trace_join =
  CLOpt.mk_bool ~deprecated:["trace_join"] ~long:"trace-join"
    "Detailed tracing information during prop join operations"


and trace_ondemand = CLOpt.mk_bool ~long:"trace-ondemand" ""

and trace_rearrange =
  CLOpt.mk_bool ~deprecated:["trace_rearrange"] ~long:"trace-rearrange"
    "Detailed tracing information during prop re-arrangement operations"


and tracing =
  CLOpt.mk_bool ~deprecated:["tracing"] ~long:"tracing"
    "Report error traces for runtime exceptions (Java only): generate preconditions for \
     runtimeexceptions in Java and report errors for public methods which throw runtime exceptions"


and tv_commit =
  CLOpt.mk_string_opt ~long:"tv-commit" ~meta:"commit" "Commit hash to submit to Traceview"


and tv_limit =
  CLOpt.mk_int ~long:"tv-limit" ~default:100 ~meta:"int"
    "The maximum number of traces to submit to Traceview"


and tv_limit_filtered =
  CLOpt.mk_int ~long:"tv-limit-filtered" ~default:100 ~meta:"int"
    "The maximum number of traces for issues filtered out by --report-filter to submit to Traceview"


and type_size =
  CLOpt.mk_bool ~deprecated:["type_size"] ~long:"type-size"
    "Consider the size of types during analysis, e.g. cannot use an int pointer to write to a char"


and uninit_interproc =
  CLOpt.mk_bool ~long:"uninit-interproc"
    "Run uninit check in the experimental interprocedural mode"


and unsafe_malloc =
  CLOpt.mk_bool ~long:"unsafe-malloc"
    ~in_help:InferCommand.[(Analyze, manual_clang)]
    "Assume that malloc(3) never returns null."


and use_cost_threshold =
  CLOpt.mk_bool ~long:"use-cost-threshold" ~default:false
    "Emit costs issues by comparing costs with a set threshold"


and version =
  let var = ref `None in
  CLOpt.mk_set var `Full ~deprecated:["version"] ~long:"version"
    ~in_help:InferCommand.[(Run, manual_generic)]
    "Print version information and exit" ;
  CLOpt.mk_set var `Json ~deprecated:["version_json"] ~long:"version-json"
    ~in_help:InferCommand.[(Run, manual_generic)]
    "Print version information in json format and exit" ;
  CLOpt.mk_set var `Vcs ~long:"version-vcs" "Print version control system commit and exit" ;
  var


(** visit mode for the worklist:
    0 depth - fist visit
    1 bias towards exit node
    2 least visited first *)
and worklist_mode =
  let var = ref 0 in
  CLOpt.mk_set var 2 ~long:"coverage" "analysis mode to maximize coverage (can take longer)" ;
  CLOpt.mk_set var 1 ~long:"exit-node-bias" ~deprecated:["exit_node_bias"]
    "nodes nearest the exit node are analyzed first" ;
  CLOpt.mk_set var 2 ~long:"visits-bias" ~deprecated:["visits_bias"]
    "nodes visited fewer times are analyzed first" ;
  var


and xcode_developer_dir =
  CLOpt.mk_path_opt ~long:"xcode-developer-dir"
    ~in_help:InferCommand.[(Capture, manual_buck_flavors)]
    ~meta:"XCODE_DEVELOPER_DIR" "Specify the path to Xcode developer directory"


and xcpretty =
  CLOpt.mk_bool ~long:"xcpretty" ~default:false
    ~in_help:InferCommand.[(Capture, manual_clang)]
    "Infer will use xcpretty together with xcodebuild to analyze an iOS app. xcpretty just needs \
     to be in the path, infer command is still just $(i,`infer -- <xcodebuild command>`)."


(* The "rest" args must appear after "--" on the command line, and hence after other args, so they
   are allowed to refer to the other arg variables. *)

let javac_classes_out =
  CLOpt.mk_string ~parse_mode:CLOpt.Javac ~deprecated:["classes_out"] ~long:""
    ~short:
      'd'
      (* Ensure that some form of "-d ..." is passed to javac. It's unclear whether this is strictly
       needed but the tests break without this for now. See discussion in D4397716. *)
    ~default:CLOpt.init_work_dir
    ~default_to_string:(fun _ -> ".")
    ~f:(fun classes_out ->
      if !buck then (
        let classes_out_infer = resolve classes_out ^/ buck_results_dir_name in
        (* extend env var args to pass args to children that do not receive the rest args *)
        CLOpt.extend_env_args ["--results-dir"; classes_out_infer] ;
        results_dir := classes_out_infer ) ;
      classes_out )
    ""


and _ =
  CLOpt.mk_string_opt ~parse_mode:CLOpt.Javac ~deprecated:["classpath"; "cp"] ~long:""
    ~f:(fun classpath ->
      if !buck then (
        let paths = String.split classpath ~on:':' in
        let files = List.filter paths ~f:(fun path -> Sys.is_file path = `Yes) in
        CLOpt.extend_env_args (List.concat_map files ~f:(fun file -> ["--specs-library"; file])) ;
        specs_library := List.rev_append files !specs_library ) ;
      classpath )
    ""


and () = CLOpt.mk_set ~parse_mode:CLOpt.Javac version ~deprecated:["version"] ~long:"" `Javac ""

(** Parse Command Line Args *)

let inferconfig_file =
  let rec find dir =
    match Sys.file_exists ~follow_symlinks:false (dir ^/ CommandDoc.inferconfig_file) with
    | `Yes ->
        Some dir
    | `No | `Unknown ->
        let parent = Filename.dirname dir in
        let is_root = String.equal dir parent in
        if is_root then None else find parent
  in
  match Sys.getenv CommandDoc.inferconfig_env_var with
  | Some _ as env_path ->
      env_path
  | None ->
      find (Sys.getcwd ()) |> Option.map ~f:(fun dir -> dir ^/ CommandDoc.inferconfig_file)


let post_parsing_initialization command_opt =
  if CommandLineOption.is_originator then (
    (* let subprocesses know where the toplevel process' results dir is *)
    Unix.putenv ~key:infer_top_results_dir_env_var ~data:!results_dir ;
    (* make sure subprocesses read from the same .inferconfig as the toplevel process *)
    Option.iter inferconfig_file ~f:(fun filename ->
        let abs_filename =
          if Filename.is_relative filename then
            (* make sure the path makes sense in children infer processes *)
            CLOpt.init_work_dir ^/ filename
          else filename
        in
        Unix.putenv ~key:CommandDoc.inferconfig_env_var ~data:abs_filename ) ) ;
  ( match !version with
  | `Full when !buck ->
      (* Buck reads stderr in some versions, stdout in others *)
      print_endline version_string ; prerr_endline version_string
  | `Javac when !buck ->
      (* print buck key *)
      let infer_version =
        match inferconfig_file with
        | Some inferconfig ->
            Printf.sprintf "version %s/inferconfig %s" Version.commit
              (Caml.Digest.to_hex (Caml.Digest.file inferconfig))
        | None ->
            Version.commit
      in
      F.printf "infer/%s@." infer_version ;
      F.eprintf "infer/%s@." infer_version
  | `Full ->
      print_endline version_string
  | `Javac ->
      (* javac prints version on stderr *) prerr_endline version_string
  | `Json ->
      print_endline Version.versionJson
  | `Vcs ->
      print_endline Version.commit
  | `None ->
      () ) ;
  ( match !help with
  | `Help ->
      CLOpt.show_manual !help_format CommandDoc.infer command_opt
  | `HelpFull ->
      CLOpt.show_manual ~internal_section:manual_internal !help_format CommandDoc.infer command_opt
  | `None ->
      () ) ;
  if !version <> `None || !help <> `None then Pervasives.exit 0 ;
  let uncaught_exception_handler exn raw_backtrace =
    let is_infer_exit_zero = match exn with L.InferExit 0 -> true | _ -> false in
    let should_print_backtrace_default =
      match exn with L.InferUserError _ | L.InferExit _ -> false | _ -> true
    in
    let suggest_keep_going = should_print_backtrace_default && not !keep_going in
    let backtrace =
      if is_infer_exit_zero then "" else Caml.Printexc.raw_backtrace_to_string raw_backtrace
    in
    let print_exception () =
      let error prefix msg =
        ANSITerminal.prerr_string L.(term_styles_of_style Fatal) prefix ;
        ANSITerminal.prerr_string L.(term_styles_of_style Fatal) msg ;
        ANSITerminal.prerr_string L.(term_styles_of_style Normal) "\n"
      in
      match exn with
      | Failure msg ->
          error "ERROR: " msg
      | L.InferExternalError msg ->
          error "External Error: " msg
      | L.InferInternalError msg ->
          error "Internal Error: " msg
      | L.InferUserError msg ->
          error "Usage Error: " msg
      | L.InferExit _ ->
          ()
      | _ ->
          error "Uncaught Internal Error: " (Exn.to_string exn)
    in
    print_exception () ;
    if (not is_infer_exit_zero) && (should_print_backtrace_default || !developer_mode) then (
      ANSITerminal.prerr_string L.(term_styles_of_style Error) "Error backtrace:\n" ;
      ANSITerminal.prerr_string L.(term_styles_of_style Error) backtrace ) ;
    if not is_infer_exit_zero then Out_channel.newline stderr ;
    if suggest_keep_going then
      ANSITerminal.prerr_string
        L.(term_styles_of_style Normal)
        "Run the command again with `--keep-going` to try and ignore this error.\n" ;
    let exitcode = L.exit_code_of_exception exn in
    L.log_uncaught_exception exn ~exitcode ;
    Epilogues.run () ;
    Pervasives.exit exitcode
  in
  Caml.Printexc.set_uncaught_exception_handler uncaught_exception_handler ;
  F.set_margin !margin ;
  let set_minor_heap_size nMb =
    (* increase the minor heap size to speed up gc *)
    let ctrl = Gc.get () in
    let words_of_Mb nMb = nMb * 1024 * 1024 * 8 / Sys.word_size in
    let new_size = max ctrl.minor_heap_size (words_of_Mb nMb) in
    Gc.set {ctrl with minor_heap_size= new_size}
  in
  set_minor_heap_size 8 ;
  let symops_timeout, seconds_timeout =
    let default_symops_timeout = 1100 in
    let default_seconds_timeout = 10.0 in
    if !models_mode then (* disable timeouts when analyzing models *)
      (None, None)
    else (Some default_symops_timeout, Some default_seconds_timeout)
  in
  if is_none !symops_per_iteration then symops_per_iteration := symops_timeout ;
  if is_none !seconds_per_iteration then seconds_per_iteration := seconds_timeout ;
  clang_compilation_dbs :=
    List.rev_map ~f:(fun x -> `Raw x) !compilation_database
    |> List.rev_map_append ~f:(fun x -> `Escaped x) !compilation_database_escaped ;
  (* set analyzer mode to linters in linters developer mode *)
  if !linters_developer_mode then linters := true ;
  if !default_linters then linters_def_file := linters_def_default_file :: !linters_def_file ;
  ( match !analyzer with
  | Linters ->
      disable_all_checkers () ;
      capture := false ;
      linters := true
  | Checkers ->
      () ) ;
  Option.value ~default:InferCommand.Run command_opt


let command, parse_args_and_return_usage_exit =
  let command_opt, usage_exit =
    CLOpt.parse ?config_file:inferconfig_file ~usage:exe_usage startup_action initial_command
  in
  let command = post_parsing_initialization command_opt in
  (command, usage_exit)


let print_usage_exit () = parse_args_and_return_usage_exit 1

type iphoneos_target_sdk_version_path_regex = {path: Str.regexp; version: string}

let process_iphoneos_target_sdk_version_path_regex args =
  let process_iphoneos_target_sdk_version_path_regex arg : iphoneos_target_sdk_version_path_regex =
    match String.rsplit2 ~on:':' arg with
    | Some (path, version) ->
        {path= Str.regexp path; version}
    | None ->
        L.(die UserError)
          "Incorrect format for the option iphoneos-target-sdk_version-path-regex. The correct \
           format is path:version but got %s"
          arg
  in
  List.map ~f:process_iphoneos_target_sdk_version_path_regex args


let process_linters_doc_url args =
  let linters_doc_url arg =
    match String.lsplit2 ~on:':' arg with
    | Some linter_doc_url_assoc ->
        linter_doc_url_assoc
    | None ->
        L.(die UserError)
          "Incorrect format for the option linters-doc-url. The correct format is linter:doc_url \
           but got %s"
          arg
  in
  let linter_doc_url_assocs = List.rev_map ~f:linters_doc_url args in
  fun ~linter_id -> List.Assoc.find ~equal:String.equal linter_doc_url_assocs linter_id


(** Freeze initialized configuration values *)

let anon_args = !anon_args

and rest = !rest

and abs_struct = !abs_struct

and abs_val = !abs_val

and allow_leak = !allow_leak

and analysis_path_regex_whitelist = !analysis_path_regex_whitelist

and analysis_path_regex_blacklist = !analysis_path_regex_blacklist

and analysis_blacklist_files_containing = !analysis_blacklist_files_containing

and analysis_suppress_errors = !analysis_suppress_errors

and analysis_stops = !analysis_stops

and annotation_reachability = !annotation_reachability

and annotation_reachability_cxx = !annotation_reachability_cxx

and annotation_reachability_custom_pairs = !annotation_reachability_custom_pairs

and append_buck_flavors = !append_buck_flavors

and array_level = !array_level

and biabduction = !biabduction

and bootclasspath = !bootclasspath

and bo_debug = !bo_debug

and bo_relational_domain = !bo_relational_domain

and buck = !buck

and buck_blacklist = !buck_blacklist

and buck_build_args = !buck_build_args

and buck_build_args_no_inline = !buck_build_args_no_inline

and buck_cache_mode = (!buck || !genrule_mode) && not !debug

and buck_compilation_database =
  match !buck_compilation_database with
  | Some `DepsTmp ->
      Some (Deps !buck_compilation_database_depth)
  | Some `NoDeps ->
      Some NoDeps
  | None ->
      None


and buck_out = !buck_out

and buck_targets_blacklist = !buck_targets_blacklist

and bufferoverrun = !bufferoverrun

and capture =
  (* take `--clang-frontend-action` as the source of truth as long as that option exists *)
  match !clang_frontend_action with
  | Some (`Capture | `Lint_and_capture) ->
      true
  | Some `Lint ->
      false
  | None ->
      !capture


and capture_blacklist = !capture_blacklist

and changed_files_index = !changed_files_index

and nullsafe = !nullsafe

and check_version = !check_version

and clang_biniou_file = !clang_biniou_file

and clang_extra_flags = !clang_extra_flags

and clang_ignore_regex = !clang_ignore_regex

and clang_include_to_override_regex = !clang_include_to_override_regex

and classpath = !classpath

and class_loads = !class_loads

and class_loads_roots = String.Set.of_list !class_loads_roots

and compute_analytics = !compute_analytics

and continue_capture = !continue

and cost = !cost

and cost_invariant_by_default = !cost_invariant_by_default

and costs_current = !costs_current

and costs_previous = !costs_previous

and current_to_previous_script = !current_to_previous_script

and cxx = !cxx

and cxx_infer_headers = !cxx_infer_headers

and cxx_scope_guards = !cxx_scope_guards

and debug_level_analysis = !debug_level_analysis

and debug_level_capture = !debug_level_capture

and debug_level_linters = !debug_level_linters

and debug_level_test_determinator = !debug_level_test_determinator

and debug_exceptions = !debug_exceptions

and debug_mode = !debug

and default_linters = !default_linters

and dependency_mode = !dependencies

and developer_mode = !developer_mode

and differential_filter_files = !differential_filter_files

and differential_filter_set = !differential_filter_set

and dotty_cfg_libs = !dotty_cfg_libs

and dump_duplicate_symbols = !dump_duplicate_symbols

and eradicate = !eradicate

and eradicate_condition_redundant = !eradicate_condition_redundant

and eradicate_field_not_mutable = !eradicate_field_not_mutable

and eradicate_field_over_annotated = !eradicate_field_over_annotated

and eradicate_optional_present = !eradicate_optional_present

and eradicate_return_over_annotated = !eradicate_return_over_annotated

and eradicate_debug = !eradicate_debug

and eradicate_verbose = !eradicate_verbose

and external_java_packages = !external_java_packages

and fail_on_bug = !fail_on_bug

and fcp_apple_clang = !fcp_apple_clang

and fcp_syntax_only = !fcp_syntax_only

and file_renamings = !file_renamings

and filter_paths = !filter_paths

and filter_report =
  List.map !filter_report ~f:(fun str ->
      match String.split str ~on:':' with
      | [issue_type_re; filename_re; reason_str]
        when not String.(is_empty issue_type_re || is_empty filename_re || is_empty reason_str) ->
          let polarity_regex re =
            let polarity = not (Char.equal '!' re.[0]) in
            let regex = Str.regexp (if polarity then re else String.slice re 1 0) in
            (polarity, regex)
          in
          (polarity_regex issue_type_re, polarity_regex filename_re, reason_str)
      | _ ->
          L.(die UserError) "Ill-formed report filter: %s" str )


and filtering = !filtering

and flavors = !flavors

and force_delete_results_dir = !force_delete_results_dir

and fragment_retains_view = !fragment_retains_view

and force_integration = !force_integration

and from_json_report = !from_json_report

and frontend_stats = !frontend_stats

and function_pointer_specialization = !function_pointer_specialization

and frontend_tests = !frontend_tests

and gen_previous_build_command_script = !gen_previous_build_command_script

and generated_classes = !generated_classes

and get_linter_doc_url = process_linters_doc_url !linters_doc_url

and gradual = !gradual

and gradual_dereferences = !gradual_dereferences

and gradual_unannotated = !gradual_unannotated

and html = !html

and hoisting_report_only_expensive = !hoisting_report_only_expensive

and icfg_dotty_outfile = !icfg_dotty_outfile

and immutable_cast = !immutable_cast

and iphoneos_target_sdk_version = !iphoneos_target_sdk_version

and iphoneos_target_sdk_version_path_regex =
  process_iphoneos_target_sdk_version_path_regex !iphoneos_target_sdk_version_path_regex


and issues_fields = !issues_fields

and issues_tests = !issues_tests

and issues_txt = !issues_txt

and iterations = !iterations

and java_jar_compiler = !java_jar_compiler

and javac_classes_out = !javac_classes_out

and job_id = !job_id

and jobs = !jobs

and join_cond = !join_cond

and linter = !linter

and linters =
  (* take `--clang-frontend-action` as the source of truth as long as that option exists *)
  match !clang_frontend_action with
  | Some (`Lint | `Lint_and_capture) ->
      true
  | Some `Capture ->
      false
  | None ->
      !linters


and linters_def_file = !linters_def_file

and linters_def_folder = !linters_def_folder

and linters_developer_mode = !linters_developer_mode

and linters_ignore_clang_failures = !linters_ignore_clang_failures

and linters_validate_syntax_only = !linters_validate_syntax_only

and litho = !litho

and liveness = !liveness

and liveness_dangerous_classes = !liveness_dangerous_classes

and load_average =
  match !load_average with None when !buck -> Some (float_of_int ncpu) | _ -> !load_average


and log_events = !log_events

and log_file = !log_file

and log_skipped = !log_skipped

and perf_profiler_data_file = !perf_profiler_data_file

and loop_hoisting = !loop_hoisting

and max_nesting = !max_nesting

and method_decls_info = !method_decls_info

and memcached = !memcached

and memcached_size_mb = !memcached_size_mb

and merge = !merge

and ml_buckets = !ml_buckets

and models_mode = !models_mode

and modified_lines = !modified_lines

and modified_targets = !modified_targets

and monitor_prop_size = !monitor_prop_size

and nelseg = !nelseg

and nullable_annotation = !nullable_annotation

and nullsafe_strict_containers = !nullsafe_strict_containers

and no_translate_libs = not !headers

and only_cheap_debug = !only_cheap_debug

and only_footprint = !only_footprint

and only_show = !only_show

and ownership = !ownership

and passthroughs = !passthroughs

and patterns_modeled_expensive = match patterns_modeled_expensive with k, r -> (k, !r)

and patterns_never_returning_null = match patterns_never_returning_null with k, r -> (k, !r)

and patterns_skip_implementation = match patterns_skip_implementation with k, r -> (k, !r)

and patterns_skip_translation = match patterns_skip_translation with k, r -> (k, !r)

and pmd_xml = !pmd_xml

and precondition_stats = !precondition_stats

and previous_to_current_script = !previous_to_current_script

and printf_args = !printf_args

and print_active_checkers = !print_active_checkers

and print_builtins = !print_builtins

and print_log_identifier = !print_log_identifier

and print_logs = !print_logs

and print_types = !print_types

and print_using_diff = !print_using_diff

and procedures = !procedures

and procedures_attributes = !procedures_attributes

and procedures_definedness = !procedures_definedness

and procedures_filter = !procedures_filter

and procedures_name = !procedures_name

and[@warning "-32"] procedures_per_process = !procedures_per_process

and procedures_source_file = !procedures_source_file

and progress_bar =
  if !progress_bar then
    match !progress_bar_style with
    | `Auto when Unix.(isatty stdin && isatty stderr) ->
        `MultiLine
    | `Auto ->
        `Plain
    | (`Plain | `MultiLine) as style ->
        style
  else `Quiet


and procs_csv = !procs_csv

and project_root = !project_root

and pulse = !pulse

and pulse_max_disjuncts = !pulse_max_disjuncts

and pulse_widen_threshold = !pulse_widen_threshold

and purity = !purity

and quandary = !quandary

and quandaryBO = !quandaryBO

and quandary_endpoints = !quandary_endpoints

and quandary_sanitizers = !quandary_sanitizers

and quandary_sources = !quandary_sources

and quandary_sinks = !quandary_sinks

and quiet = !quiet

and racerd = !racerd

and racerd_guardedby = !racerd_guardedby

and reactive_mode = !reactive || InferCommand.(equal Diff) command

and reactive_capture = !reactive_capture

and reanalyze = !reanalyze

and relative_path_backtrack = !relative_path_backtrack

and report = !report

and report_current = !report_current

and report_custom_error = !report_custom_error

and report_force_relative_path = !report_force_relative_path

and report_formatter = !report_formatter

and report_hook = !report_hook

and report_previous = !report_previous

and reports_include_ml_loc = !reports_include_ml_loc

and resource_leak = !resource_leak

and results_dir = !results_dir

and seconds_per_iteration = !seconds_per_iteration

and select = !select

and show_buckets = !print_buckets

and siof = !siof

and siof_check_iostreams = !siof_check_iostreams

and siof_safe_methods = !siof_safe_methods

and skip_analysis_in_path = !skip_analysis_in_path

and skip_analysis_in_path_skips_compilation = !skip_analysis_in_path_skips_compilation

and skip_duplicated_types = !skip_duplicated_types

and skip_translation_headers = !skip_translation_headers

and source_preview = !source_preview

and source_files = !source_files

and source_files_cfg = !source_files_cfg

and source_files_filter = !source_files_filter

and source_files_type_environment = !source_files_type_environment

and source_files_procedure_names = !source_files_procedure_names

and source_files_freshly_captured = !source_files_freshly_captured

and sources = !sources

and sourcepath = !sourcepath

and spec_abs_level = !spec_abs_level

and sqlite_lock_timeout = !sqlite_lock_timeout

and sqlite_vfs = !sqlite_vfs

and starvation = !starvation

and starvation_skip_analysis = !starvation_skip_analysis

and starvation_strict_mode = !starvation_strict_mode

and stats_report = !stats_report

and subtype_multirange = !subtype_multirange

and custom_symbols =
  (* Convert symbol lists to regexps just once, here *)
  match !custom_symbols with
  | `Assoc sym_lists ->
      List.Assoc.map ~f:get_symbols_regexp sym_lists
  | `List [] ->
      []
  | _ ->
      L.(die UserError)
        "--custom-symbols must be dictionary of symbol lists not %s"
        (Yojson.Basic.to_string !custom_symbols)


and symops_per_iteration = !symops_per_iteration

and keep_going = !keep_going

and test_determinator = !test_determinator

and test_determinator_clang = !test_determinator_clang

and test_filtering = !test_filtering

and profiler_samples = !profiler_samples

and testing_mode = !testing_mode

and threadsafe_aliases = !threadsafe_aliases

and topl_properties = !topl_properties

and trace_error = !trace_error

and trace_events = !trace_events

and trace_ondemand = !trace_ondemand

and trace_join = !trace_join

and trace_rearrange = !trace_rearrange

and tracing = !tracing

and tv_commit = !tv_commit

and tv_limit = !tv_limit

and tv_limit_filtered = !tv_limit_filtered

and type_size = !type_size

and uninit = !uninit

and uninit_interproc = !uninit_interproc

and unsafe_malloc = !unsafe_malloc

and use_cost_threshold = !use_cost_threshold

and worklist_mode = !worklist_mode

and write_dotty = !write_dotty

and write_html = !write_html

and write_html_whitelist_regex = !write_html_whitelist_regex

and xcode_developer_dir = !xcode_developer_dir

and xcpretty = !xcpretty

(** Configuration values derived from command-line options *)

let captured_dir = results_dir ^/ captured_dir_name

let clang_frontend_action_string =
  String.concat ~sep:" and "
    ((if capture then ["translating"] else []) @ if linters then ["linting"] else [])


let dynamic_dispatch =
  CLOpt.mk_bool ~long:"dynamic-dispatch" ~default:biabduction
    "Specify treatment of dynamic dispatch in Java code: false 'none' treats dynamic dispatch as \
     a call to unknown code and true triggers lazy dynamic dispatch. The latter mode follows the \
     JVM semantics and creates procedure descriptions during symbolic execution using the type \
     information found in the abstract state"
    ~in_help:InferCommand.[(Analyze, manual_java)]


let dynamic_dispatch = !dynamic_dispatch

let specs_library = !specs_library

let quandaryBO_filtered_issues =
  if quandaryBO then
    IssueType.
      [ buffer_overrun_u5
      ; buffer_overrun_l5
      ; buffer_overrun_l4
      ; untrusted_buffer_access
      ; untrusted_heap_allocation ]
    |> List.filter ~f:(fun issue ->
           let enabled = issue.IssueType.enabled || not filtering in
           IssueType.set_enabled issue true ; not enabled )
  else []


(** Check if a Java package is external to the repository *)
let java_package_is_external package =
  match external_java_packages with
  | [] ->
      false
  | _ ->
      List.exists external_java_packages ~f:(fun (prefix : string) ->
          String.is_prefix package ~prefix )


let is_in_custom_symbols list_name symbol =
  match List.Assoc.find ~equal:String.equal custom_symbols list_name with
  | Some regexp ->
      Str.string_match regexp symbol 0
  | None ->
      false
