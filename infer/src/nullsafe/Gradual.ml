open! IStd

module N = struct
  type t = unit

  let pp _ _ = ()

  let equal _ _ = true
end

module Lattice = AbstractDomain.Flat (N)
module Domain = AbstractDomain.Map (Var) (Lattice)

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  type extras = Summary.t

  let pp_session_name _ _ = ()

  let report summary loc msg =
    let trace = Errlog.make_trace_element 1 loc msg [] in
    Reporting.log_error summary ~loc ~ltr:[trace] IssueType.null_dereference ""

  let exec_instr astate {ProcData.pdesc; extras} _ (instr : HilInstr.t) =
    let summary = extras in
    match instr with
    | Assign (_, _, loc) ->
      report summary loc "Hello, world!" ;
      astate
    | _ -> astate
end

module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (ProcCfg.Exceptional))

let checker {Callbacks.summary; proc_desc; tenv} =
    let initial = Domain.empty in
    let proc_data = ProcData.make proc_desc tenv summary in
  ignore (Analyzer.compute_post proc_data ~initial) ;
  summary
