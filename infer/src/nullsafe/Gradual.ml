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

  let exec_instr astate {ProcData.pdesc; tenv; extras} _ (instr : HilInstr.t) =
    let summary = extras
    in
    match instr with
    | Metadata _ ->
      astate
    | Assign (_, _, loc)
    | Assume (_, _, _, loc)
    | Call (_, _, _, _, loc) ->
      let report issue msg =
        let trace = Errlog.make_trace_element 1 loc msg [] in
        Reporting.log_warning summary ~loc ~ltr:[trace] issue ""
      in
      let field_annot fieldname =
        let struct_name = Typ.Name.Java.from_string (Typ.Fieldname.Java.get_class fieldname) in
        match Tenv.lookup tenv struct_name with
        | None ->
          Lattice.top
        | Some struct_typ ->
          let nullable = Annotations.field_has_annot fieldname struct_typ Annotations.ia_is_nullable in
          if nullable then Lattice.top else Lattice.v ()
      in
      let rec check_chain (access : HilExp.AccessExpression.t) =
        match access with
        | Base (var, _) -> (
          match Domain.find_opt var astate with
          | None -> Lattice.top
          | Some l -> l )
        | FieldOffset (sub, fieldname) ->
          ignore (check_chain sub) ;
          field_annot fieldname
        | ArrayOffset (sub, _, index) ->
          ignore (check_chain sub) ;
          (
            match index with
            | Some exp -> ignore (check_exp exp)
            | _ -> ()
          ) ;
          Lattice.top
        | Dereference sub ->
          (
            let l = check_chain sub in
            if Lattice.is_top l then
            let message = Format.asprintf "%a" HilExp.AccessExpression.pp access in
            report IssueType.gradual_dereference message
          ) ;
          Lattice.v ()
        | _ ->
          Lattice.top
      and check_exp (exp : HilExp.t) =
        match exp with
        | AccessExpression access ->
          check_chain access
        | UnaryOperator (_, subexp, _)
        | Exception subexp
        | Sizeof (_, Some subexp) ->
          ignore (check_exp subexp) ;
          Lattice.v ()
        | BinaryOperator (_, left, right) ->
          ignore (check_exp left) ;
          ignore (check_exp right) ;
          Lattice.v ()
        | Cast (_, subexp) ->
          ignore (check_exp subexp) ;
          if HilExp.is_null_literal exp then Lattice.top else Lattice.v ()
        | Constant _ when HilExp.is_null_literal exp ->
          Lattice.top
        | _ ->
          Lattice.v ()
      in
      match instr with
      | Metadata _ -> astate (* should be unreachable *)
      | Assign (lhs, rhs, _) ->
        ignore (check_chain lhs) ;
        let l = check_exp rhs in
        (
          match lhs with
          | Base (var, _) ->
            Domain.add var l astate
          | FieldOffset (_, fieldname) ->
            (
              if not (Lattice.(<=) ~lhs:l ~rhs:(field_annot fieldname)) then
              let message = Typ.Fieldname.to_string fieldname in
              report IssueType.gradual_field message
            ) ;
            astate
          | _ ->
            astate
        )
      | Assume (cond, _, _, _) ->
        ignore (check_exp cond) ;
        astate
      | Call (lhs, proc, args, _, _) ->
        List.fold_left args ~init:() ~f:(fun _ arg -> ignore (check_exp arg)) ;
        astate
end

module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (ProcCfg.Exceptional))

let checker {Callbacks.summary; proc_desc; tenv} =
  let initial = Domain.empty in
  let proc_data = ProcData.make proc_desc tenv summary in
  ignore (Analyzer.compute_post proc_data ~initial) ;
  summary
