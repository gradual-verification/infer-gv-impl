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

  module Vars = Caml.Set.Make(Var)

  type checked = { assume : Vars.t; deny: Vars.t }

  type param = { arg : HilExp.t; annot: Lattice.t }

  type proc_info = { args : param list; l : Lattice.t }

  let exec_instr astate { ProcData.tenv; extras } _ (instr : HilInstr.t) =
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
      let proc_annot procname =
        let nullable = Annotations.pname_has_return_annot
          procname
          ~attrs_of_pname:Summary.proc_resolve_attributes
          Annotations.ia_is_nullable in
        if nullable then Lattice.top else Lattice.v ()
      in
      let args_annot procname =
        match Summary.proc_resolve_attributes procname with
        | Some { method_annotation = { params } } ->
          List.map params ~f:(fun annot ->
            if Annotations.ia_is_nullable annot
            then Lattice.top
            else Lattice.v ()
          )
        | _ ->
          []
      in
      let rec combine (args : HilExp.t list) (annots : Lattice.t list) : param list =
        match args with
        | [] ->
          []
        | arg :: args ->
          let annot, annots = (
            match annots with
            | [] -> (Lattice.top, [])
            | annot :: annots -> (annot, annots)
          ) in
          { arg; annot } :: combine args annots
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
      let rec checked_vars (exp : HilExp.t) =
        match exp with
        | UnaryOperator (Unop.LNot, subexp, _) ->
          let { assume; deny } = checked_vars subexp in
          { assume = deny; deny = assume }
        | BinaryOperator (Binop.Eq, AccessExpression (Base (var, _)), subexp)
        | BinaryOperator (Binop.Eq, subexp, AccessExpression (Base (var, _))) ->
          (
            match Lattice.get (check_exp subexp) with
            | Some _ ->
              { assume = Vars.singleton var; deny = Vars.empty }
            | _ ->
              let assume = (
                match subexp with
                | AccessExpression (Base (var', _)) ->
                  (
                    match Domain.find_opt var astate with
                    | Some l ->
                      (
                        match Lattice.get l with
                        | Some _ -> Vars.singleton var'
                        | _ -> Vars.empty
                      )
                    | _ -> Vars.empty
                  )
                | _ -> Vars.empty
              ) in
              { assume; deny = Vars.empty }
          )
        | BinaryOperator (Binop.Ne, left, right) ->
          let rewritten = HilExp.BinaryOperator (Binop.Eq, left, right) in
          let { assume; deny } = checked_vars rewritten in
          { assume = deny; deny = assume }
        | BinaryOperator (Binop.LAnd, left, right) ->
          let { assume = assume_left; deny = deny_left } = checked_vars left in
          let { assume = assume_right; deny = deny_right } = checked_vars right in
          { assume = Vars.union assume_left assume_right;
            deny = Vars.inter deny_left deny_right }
        | BinaryOperator (Binop.LOr, left, right) ->
          let { assume = assume_left; deny = deny_left } = checked_vars left in
          let { assume = assume_right; deny = deny_right } = checked_vars right in
          { assume = Vars.inter assume_left assume_right;
            deny = Vars.union deny_left deny_right }
        | _ ->
          ignore (check_exp exp) ;
          { assume = Vars.empty; deny = Vars.empty }
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
        List.fold_left (Vars.elements (checked_vars cond).assume) ~init:astate
          ~f:(fun astate var -> Domain.add var (Lattice.v ()) astate)
      | Call ((var, _), proc, args, _, _) ->
        let { args; l } = (
          match proc with
          | Direct (Typ.Procname.Java procname as fullname) ->
            let args = combine args (args_annot fullname) in
            let l = proc_annot fullname in
            if Typ.Procname.Java.is_static procname then { args; l } else (
              match args with
              | [] ->
                { args; l }
              | { arg = receiver } :: tail ->
                (
                  let rec_l = check_exp receiver in
                  if Lattice.is_top rec_l then
                  let message = Format.asprintf "%a" HilExp.pp receiver in
                  report IssueType.gradual_dereference message
                ) ;
                { args = tail; l }
            )
          | Indirect access ->
            ignore (check_chain access) ;
            { args = combine args []; l = Lattice.top }
          | _ ->
            { args = combine args []; l = Lattice.top }
        ) in
        List.fold_left args ~init:() ~f:(fun _ { arg; annot } ->
          let arg_l = check_exp arg in
          if not (Lattice.(<=) ~lhs:arg_l ~rhs:annot) then
          let message = Format.asprintf "%a" HilExp.pp arg in
          report IssueType.gradual_argument message
        ) ;
        Domain.add var l astate
end

module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (ProcCfg.Exceptional))

let checker { Callbacks.summary; proc_desc; tenv } =
  let initial = Domain.empty in
  let proc_data = ProcData.make proc_desc tenv summary in
  ignore (Analyzer.compute_post proc_data ~initial) ;
  summary
