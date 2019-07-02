open! IStd

module N = struct
  type t = unit

  let pp _ _ = ()

  let equal _ _ = true
end

type inner = N
module Lattice = AbstractDomain.Flat (N)
module Domain = AbstractDomain.Map (Var) (Lattice)

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  type extras = Summary.t

  let pp_session_name _ _ = ()

  let exec_instr astate {ProcData.pdesc; extras} _ (instr : HilInstr.t) =
    let summary = extras in
    match instr with
    | Assign (_, _, loc) ->
      Reporting.log_error summary ~loc IssueType.null_dereference "Hello, world!" ;
      astate
    | _ -> astate
end

module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (ProcCfg.Exceptional))

let checker {Callbacks.summary; proc_desc; tenv} =
    let initial = Domain.empty in
    let proc_data = ProcData.make proc_desc tenv summary in
  ignore (Analyzer.compute_post proc_data ~initial) ;
  summary
