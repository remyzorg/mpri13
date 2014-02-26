open String
open Name
open XAST
open Types
open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

let string_of_type ty      = ASTio.(XAST.(to_string pprint_ml_type ty))


let rec program p = handle_error List.(fun () ->
    flatten (fst (Misc.list_foldmap block ElaborationEnvironment.initial p))
  )

and tn_of_class tname = TName ("class_" ^ (namet tname))

and n_of_inst tname = Name ("inst_" ^ (namet tname))
  

and block env = function
  | BTypeDefinitions ts ->
    let env = type_definitions env ts in
    ([BTypeDefinitions ts], env)
  | BDefinition d ->
    let d, env = value_binding env d in
    ([BDefinition d], env)
  | BClassDefinition c ->
    let elaborated_class = TypeDefs (c.class_position, [elaborate_class c]) in
    let env = type_definitions env elaborated_class in
    let elaborated_members, env = check_class_definition env c in
    ([BTypeDefinitions elaborated_class; BDefinition elaborated_members] , env)
  | BInstanceDefinitions is ->
    let elaborated_instances, env = check_instance_definitions env is in
    ([BDefinition elaborated_instances], env)

and type_definitions env (TypeDefs (_, tdefs)) =
  let env = List.fold_left env_of_type_definition env tdefs in
  List.fold_left type_definition env tdefs

and env_of_type_definition env = function
  | (TypeDef (pos, kind, t, _)) as tdef ->
    bind_type t kind tdef env
  | (ExternalType (p, ts, t, os)) as tdef ->
    bind_type t (kind_of_arity (List.length ts)) tdef env

and type_definition env = function
  | TypeDef (pos, _, t, dt) -> datatype_definition t env dt
  | ExternalType (p, ts, t, os) -> env

and datatype_definition t env = function
  | DAlgebraic ds ->
    List.fold_left algebraic_dataconstructor env ds
  | DRecordType (ts, ltys) ->
    List.fold_left (label_type ts t) env ltys

and label_type ts rtcon env (pos, l, ty) =
  let env' = List.fold_left (fun env x -> bind_type_variable x env) env ts in
  check_wf_type env' KStar ty;
  bind_label pos l ts ty rtcon env

and algebraic_dataconstructor env (_, DName k, ts, kty) =
  check_wf_scheme env ts kty;
  bind_scheme (Name k) ts kty env

and introduce_type_parameters env ts =
  List.fold_left (fun env t -> bind_type_variable t env) env ts

and check_wf_scheme env ts ty =
  check_wf_type (introduce_type_parameters env ts) KStar ty

and check_wf_type env xkind = function
  | TyVar (pos, t) ->
    let tkind = lookup_type_kind pos t env in
    check_equivalent_kind pos xkind tkind

  | TyApp (pos, t, tys) ->
    let kt = lookup_type_kind pos t env in
    check_type_constructor_application pos env kt tys

and check_type_constructor_application pos env k tys =
  match tys, k with
  | [], KStar -> ()
  | ty :: tys, KArrow (k, ks) ->
    check_wf_type env k ty;
    check_type_constructor_application pos env ks tys
  | _ -> raise (IllKindedType pos)

and check_equivalent_kind pos k1 k2 =
  match k1, k2 with
    | KStar, KStar -> ()
    | KArrow (k1, k2), KArrow (k1', k2') ->
      check_equivalent_kind pos k1 k1';
      check_equivalent_kind pos k2 k2'
    | _ ->
      raise (IncompatibleKinds (pos, k1, k2))

and env_of_bindings env cdefs = List.(
  (function
    | BindValue (_, vs)
    | BindRecValue (_, vs) ->
      fold_left (fun env (ValueDef (_, ts, _, (x, ty), _)) ->
        bind_scheme x ts ty env
      ) env vs
    | ExternalValue (_, ts, (x, ty), _) ->
      bind_scheme x ts ty env
  ) cdefs
)

and check_equal_types pos ty1 ty2 =
  if not (equivalent ty1 ty2) then
    raise (IncompatibleTypes (pos, ty1, ty2))

and type_application pos env x tys =
  List.iter (check_wf_type env KStar) tys;
  let (ts, (_, ty)) = lookup pos x env in
  try
    substitute (List.combine ts tys) ty
  with _ ->
    raise (InvalidTypeApplication pos)

and build_ancestors_path pos env b predicates = 
  let rec search predicates path = 
    if List.mem b predicates then Some (b :: path)
    else match predicates with
    | [] -> None
    | p :: tail ->
        let sups = (lookup_class pos p env).superclasses in
        let explo = search sups (p :: path) in
        begin match explo with
        | None -> search tail path
        | Some _ -> explo
        end
  in
  match search predicates [] with
  | Some p -> p
  | None -> [b]


and build_ancestors_access pos path ty tys =
  let rec construct path =
    match path with
    | [] -> assert false
    | [cn] ->
        let record = record_name cn ty in
        EVar (pos, record, tys)
    | tname :: (b :: _ as tail) ->
        let lbl = superclass_field_name b tname in
        ERecordAccess (pos, construct tail, lbl)
  in
  construct path
        
and is_predicate cn predicates =
  List.exists (function ClassPredicate (cl, _) -> cl = cn) predicates
      
    
and expression predicates env = function
  | EVar (pos, ((Name s) as x), tys) as xvar ->

    let tys' = type_application pos env x tys in

    begin match destruct_tyarrow tys' with
    | None -> (EVar (pos, x, tys), tys')
    | Some (ity, oty) ->
      begin
      match class_of_ident_type pos env ity with
      | None -> (EVar (pos, x, tys), tys')
      | Some (cn, ty) ->

          let pl = List.map (fun (ClassPredicate (cl, _)) -> cl) predicates in
          let path = build_ancestors_path pos env cn pl in
          let right = build_ancestors_access pos path ty tys in

          let right_with_preds =
            (try
               let i = lookup_instance pos (cn, TName (name_of_type ty)) env in
               List.fold_left (fun acc_expr (ClassPredicate (cl, tn)) ->
                 let v = EVar (pos, n_of_inst cl,
                               [TyVar (pos, tn)]) in
                 EApp (pos, acc_expr, v)
               ) right i.instance_typing_context
             with UnboundInstance _ -> right) in
          let app = EApp (pos, xvar, right_with_preds) in
          app, oty
      end
    end


  | ELambda (pos, ((x, aty) as b), e') ->
    check_wf_type env KStar aty;
    let env = bind_simple x aty env in
    let (e, ty) = expression predicates env e' in
    (ELambda (pos, b, e), ntyarrow pos [aty] ty)

  | EApp (pos, a, b) ->
    let a, a_ty = expression predicates env a in
    let b, b_ty = expression predicates env b in
    begin match destruct_tyarrow a_ty with
      | None ->
        raise (ApplicationToNonFunctional pos)
      | Some (ity, oty) ->
        check_equal_types pos b_ty ity;
        (EApp (pos, a, b), oty)
    end

  | EBinding (pos, vb, e) ->
    let vb, env = value_binding env vb in
    let e, ty = expression predicates env e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, tvs, e) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression predicates env e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables
        are useless. *)
    expression predicates env e

  | EDCon (pos, DName x, tys, es) ->
    let ty = type_application pos env (Name x) tys in
    let (itys, oty) = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let es =
        List.map2 (fun e xty ->
          let (e, ty) = expression predicates env e in
          check_equal_types pos ty xty;
          e
        ) es itys
      in
      (EDCon (pos, DName x, tys, es), oty)

  | EMatch (pos, s, bs) ->
    let (s, sty) = expression predicates env s in
    let bstys = List.map (branch predicates env sty) bs in
    let bs = fst (List.split bstys) in
    let tys = snd (List.split bstys) in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression predicates env e in
    let (ts, lty, rtcon) = lookup_label pos l env in
    let ty =
      match ty with
        | TyApp (_, r, args) ->
          if rtcon <> r then
            raise (LabelDoesNotBelong (pos, l, r, rtcon))
          else
            begin try
              let s = List.combine ts args in
              Types.substitute s lty
            with _ ->
              (** Because we only well-kinded types and only store
                  well-kinded types in the environment. *)
              assert false
            end
        | _ ->
          raise (RecordExpected (pos, ty))
    in
    (ERecordAccess (pos, e, l), ty)

  | ERecordCon (pos, n, i, []) ->
    (** We syntactically forbids empty records. *)
    assert false

  | ERecordCon (pos, n, i, rbs) ->
    let rbstys = List.map (record_binding predicates env) rbs in
    let rec check others rty = function
      | [] ->
        List.rev others, rty
      | (RecordBinding (l, e), ty) :: ls ->
        if List.exists (fun (RecordBinding (l', _)) -> l = l') others then
          raise (MultipleLabels (pos, l));

        let (ts, lty, rtcon) = lookup_label pos l env in
        let (s, rty) =
          match rty with
            | None ->
              let rty = TyApp (pos, rtcon, i) in
              let s =
                try
                  List.combine ts i
                with _ ->
                  raise (InvalidRecordInstantiation pos)
              in
              (s, rty)
            | Some (s, rty) ->
              (s, rty)
        in
        check_equal_types pos ty (Types.substitute s lty);
        check (RecordBinding (l, e) :: others) (Some (s, rty)) ls
    in
    let (ls, rty) = check [] None rbstys in
    let rty = match rty with
      | None -> assert false
      | Some (_, rty) -> rty
    in
    (ERecordCon (pos, n, i, ls), rty)

  | ((EPrimitive (pos, p)) as e) ->
    (e, primitive pos p)

and primitive pos = function
  | PIntegerConstant _ ->
    TyApp (pos, TName "int", [])

  | PUnit ->
    TyApp (pos, TName "unit", [])

  | PCharConstant _ ->
    TyApp (pos, TName "char", [])

and branch predicates env sty (Branch (pos, p, e)) =
  let denv = pattern env sty p in
  let env = concat pos env denv in
  let (e, ty) = expression predicates env e in
  (Branch (pos, p, e), ty)

and concat pos env1 env2 =
  List.fold_left
    (fun env (_, (x, ty)) -> bind_simple x ty env)
    env1 (values env2)

and linear_bind pos env (ts, (x, ty)) =
  assert (ts = []); (** Because patterns only bind monomorphic values. *)
  try
    ignore (lookup pos x env);
    raise (NonLinearPattern pos)
  with UnboundIdentifier _ ->
    bind_simple x ty env

and join pos denv1 denv2 =
  List.fold_left (linear_bind pos) denv2 (values denv1)

and check_same_denv pos denv1 denv2 =
  List.iter (fun (ts, (x, ty)) ->
    assert (ts = []); (** Because patterns only bind monomorphic values. *)
    try
      let (_, (_, ty')) = lookup pos x denv2 in
      check_equal_types pos ty ty'
    with _ ->
      raise (PatternsMustBindSameVariables pos)
  ) (values denv1)

and pattern env xty = function
  | PVar (_, name) ->
    bind_simple name xty ElaborationEnvironment.empty

  | PWildcard _ ->
    ElaborationEnvironment.empty

  | PAlias (pos, name, p) ->
    linear_bind pos (pattern env xty p) ([], (name, xty))

  | PTypeConstraint (pos, p, pty) ->
    check_equal_types pos pty xty;
    pattern env xty p

  | PPrimitive (pos, p) ->
    check_equal_types pos (primitive pos p) xty;
    ElaborationEnvironment.empty

  | PData (pos, (DName x), tys, ps) ->
    let kty = type_application pos env (Name x) tys in
    let itys, oty = destruct_ntyarrow kty in
    if List.(length itys <> length ps) then
      raise (InvalidDataConstructorApplication pos)
    else
      let denvs = List.map2 (pattern env) itys ps in (
        check_equal_types pos oty xty;
        List.fold_left (join pos) ElaborationEnvironment.empty denvs
      )

  | PAnd (pos, ps) ->
    List.fold_left
      (join pos)
      ElaborationEnvironment.empty
      (List.map (pattern env xty) ps)

  | POr (pos, ps) ->
    let denvs = List.map (pattern env xty) ps in
    let denv = List.hd denvs in
    List.(iter (check_same_denv pos denv) (tl denvs));
    denv

and record_binding predicates env (RecordBinding (l, e)) =
  let e, ty = expression predicates env e in
  (RecordBinding (l, e), ty)

and value_binding env = function
  | BindValue (pos, vs) ->
    let (vs, env) = Misc.list_foldmap value_definition env vs in
    (BindValue (pos, vs), env)

  | BindRecValue (pos, vs) ->
    let env = List.fold_left value_declaration env vs in
    let (vs, _) = Misc.list_foldmap value_definition env vs in
    (BindRecValue (pos, vs), env)

  | ExternalValue (pos, ts, ((x, ty) as b), os) ->
      let env = bind_scheme x ts ty env in
      (ExternalValue (pos, ts, b, os), env)

and eforall pos ts e =
  match ts, e with
    | ts, EForall (pos, [], ((EForall _) as e)) ->
      eforall pos ts e
    | [], EForall (pos, [], e) ->
      e
    | [], EForall (pos, _, _) ->
      raise (InvalidNumberOfTypeAbstraction pos)
    | [], e ->
      e
    | x :: xs, EForall (pos, t :: ts, e) ->
      if x <> t then
        raise (SameNameInTypeAbstractionAndScheme pos);
      eforall pos xs (EForall (pos, ts, e))
    | _, _ ->
      raise (InvalidNumberOfTypeAbstraction pos)


and value_definition env (ValueDef (pos, ts, ps, (x, xty), e)) =
  let env' = introduce_type_parameters env ts in
  check_wf_scheme env ts xty;

  begin match destruct_tyarrow xty with
  | None -> if ps <> [] then raise (InvalidOverloading pos)
  | _ -> ()
  end;

  let e = eforall pos ts e in
  let e, ty = expression ps env' e in
  check_equal_types pos xty ty;

  let e_with_pred = List.fold_left (
    fun acc_expr (ClassPredicate (cl, tparam)) ->
      let inst_type = TyApp (
        pos, tn_of_class cl, [TyVar (pos, tparam)]) in
      ELambda (pos, (n_of_inst cl, inst_type), acc_expr)
  ) e ps
  in
  let ty_with_preds = List.fold_left (
    fun acc_ty (ClassPredicate (cl, tparam)) ->
    let cltype = TyApp (pos, TName ("class_" ^ (namet cl)),
                        [TyVar (pos, tparam)]) in
    TyApp (pos, TName "->", [cltype; acc_ty])
  ) ty ps in
  let b = x, ty_with_preds in

  if is_value_form e_with_pred then begin
    (ValueDef (pos, ts, [], b, EForall (pos, ts, e_with_pred)),
     bind_scheme x ts ty_with_preds env)
  end else begin
    if ts <> [] then raise (ValueRestriction pos)
    else (ValueDef (pos, [], [], b, e_with_pred),
          bind_simple x ty_with_preds env)
  end

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =

  let ps_tys = List.map (fun (ClassPredicate (cl, tparam)) ->
    TyApp (pos, TName ("class_" ^ (namet cl)), [TyVar (pos, tparam)])
  ) ps in
  let extended_ty = ntyarrow pos ps_tys ty in
  bind_scheme x ts extended_ty env


and is_value_form = function
  | EVar _
  | ELambda _
  | EPrimitive _ ->
    true
  | EDCon (_, _, _, es) ->
    List.for_all is_value_form es
  | ERecordCon (_, _, _, rbs) ->
    List.for_all (fun (RecordBinding (_, e)) -> is_value_form e) rbs
  | EExists (_, _, t)
  | ETypeConstraint (_, t, _)
  | EForall (_, _, t) ->
    is_value_form t
  | _ ->
    false

and name_of_type = function
  | TyApp (_, (TName n), tys) ->
    n ^ (String.concat "" (List.map name_of_type tys))
  | _ -> ""

and record_name cn ty =
  let nt = name_of_type ty in
  let s = if nt = "" then "inst_" else nt in
  Name (s ^ (namet cn))

and class_of_ident_type pos env = function
  | TyApp (_, (TName n as tn), [param]) ->
    begin try
      let cn = lookup_class_type env tn in
      Some (cn, param)
    with Not_found -> None end
  | _ -> None


(* and is_member_of_typeclass name env = *)


  
      
and elaborate_class_member c (pos, (LName name as lname), ty) =
  let param = n_of_inst c.class_name in
  let ty_with_param = TyApp (
    pos, tn_of_class c.class_name, [TyVar (pos, c.class_parameter)]) in
  ValueDef (
    pos, [c.class_parameter], [],
    (Name name, TyApp (pos, TName "->", [ty_with_param; ty])),
    (EForall (pos, [c.class_parameter],
    ELambda (
      pos, (param, ty_with_param),
      ERecordAccess (pos, EVar (pos, param, [(* EqX *)]), lname)))))


and superclass_field_name cl super  = 
    LName ("super_" ^ (namet cl) ^ "_" ^ (namet super))
    
and elaborate_class c =
    (* class_members   : (position * lname * mltype) list; *)
  let pos = c.class_position in
  let superclasses = List.map (fun super ->
    let field = superclass_field_name c.class_name super in
    let ty = TyApp (pos, tn_of_class super, [TyVar (pos, c.class_parameter)]) in
    (pos, field, ty)
  ) c.superclasses in
  
  let dty = DRecordType ([c.class_parameter], c.class_members @ superclasses) in
  TypeDef (c.class_position, kind_of_arity 1, tn_of_class c.class_name, dty)


and elaborate_class_members pos c =
  let mem_values = List.map (elaborate_class_member c) c.class_members in
  (BindValue (pos, mem_values))


and check_class_definition env c =
  let pos = c.class_position in
  (* check existence of superclasses *)
  List.iter (fun e -> ignore (lookup_class pos e env)) c.superclasses;
  (* check double in superclass*)
  if Misc.forall_tail List.mem c.superclasses
  then raise (AlreadyDefinedAsSuperclass pos);
  let double_members =
    Misc.forall_tail (fun (_, name1, _) t ->
      Format.printf "OKOK : %d @." (List.length c.class_members);
      (try ignore (lookup pos (Name (namel name1)) env);
           raise (AlreadyDefinedMember pos) with
      | UnboundIdentifier _ -> () );
      List.for_all (fun (_, name2, _) -> name1 <> name2) t) c.class_members
  in
  if double_members then raise (AlreadyDefinedMember pos);
  List.iter (fun (pos, LName name, ty) ->
    check_wf_scheme env [c.class_parameter] ty) c.class_members;
  let env = bind_class c.class_name c env in
  let v = elaborate_class_members pos c in
  let env = bind_class_type env (tn_of_class c.class_name) c in
  value_binding env v


and elaborate_instance env i =
  let pos = i.instance_position in
  let tname = tn_of_class i.instance_class_name in
  let params = List.map (fun p -> TyVar (pos, p)) i.instance_parameters in
  let ty_inst = TyApp (pos, i.instance_index, params) in
  let ty =(TyApp (pos, tname, [ty_inst])) in
  let name = record_name i.instance_class_name ty_inst in
  let c = lookup_class pos i.instance_class_name env in
  let fields = List.fold_left (fun fields super ->
    let lname = superclass_field_name c.class_name super in
    let expr = EVar (pos, record_name super ty_inst, params) in
    RecordBinding (lname, expr) :: fields
  ) i.instance_members c.superclasses in
  let expr = ERecordCon (pos, name, [ty_inst], fields) in
  let expr_with_abs = List.fold_left (fun acc_expr param ->
    EForall (pos, [param], acc_expr)) expr i.instance_parameters
  in
  ValueDef (pos, i.instance_parameters,
            i.instance_typing_context,
            (name, ty), expr_with_abs)


and check_instance_definitions env is =
  let check_name_cm lname (_, LName lname, _) = lname = lname in
  let instance_member pos env c
      i params (RecordBinding (LName imname as lname, expr)) =
    let pos = i.instance_position in

    (* add instance parameters to the environnement *)
    let local_env = introduce_type_parameters env i.instance_parameters in
    let _, tyim = expression [] local_env expr in
    let (ts, subt, _) = lookup_label pos lname local_env in

    (* substitute the class parameter by the
       instance index in the class member type *)

    let tycm =
      substitute (List.combine ts [TyApp (pos, i.instance_index, params)]) subt
    in check_equal_types pos tyim tycm
  in

  let instance_definition env i =
    let pos = i.instance_position in
    let c = lookup_class pos i.instance_class_name env in
    let params = List.map (fun p -> TyVar (pos, p)) i.instance_parameters in
    if i.instance_index = TName "->" then raise (IllKindedType pos);

    (* check if members are properly implemented*)
    List.iter (fun (_, namei, _) ->
      List.iter (fun (RecordBinding (namem, _)) ->
        if namei <> namem then raise (MemberNotImplemented (pos, namei))
      ) i.instance_members
    ) c.class_members;

    let env = List.fold_left (fun acc (RecordBinding (LName s, _)) ->
      try bind_scheme (Name s) [c.class_parameter]  (
        let _, _, t = List.find (check_name_cm s) c.class_members in t)
            acc
      with Not_found -> raise (UnboundMember (pos, c.class_name, LName s))
    ) env i.instance_members in

    List.iter (instance_member pos env c i params) i.instance_members
  in

  let env = List.fold_left bind_instance env is in
  List.iter (instance_definition env) is;
  match is with [] -> assert false | i::_ ->
  let bvs = BindRecValue
    (i.instance_position, List.map (elaborate_instance env) is)
  in
  value_binding env bvs

