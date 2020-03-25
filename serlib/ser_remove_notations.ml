open Constrexpr

(* Generic mapper functions for some Coq structure used by Vernacexpr *)
module Map =
struct

let glob_red_flag f flag =
  Genredexpr.{ flag with rConst = List.map f flag.rConst }

let red_expr_gen fa fb fc expr =
  let open Genredexpr in
  match expr with
  | Red b -> Red b
  | Hnf -> Hnf
  | Simpl (flag, occ) ->
    let flag = glob_red_flag fb flag in
    let occ = Option.map (fun (occ_expr, union) ->
        (occ_expr, Util.map_union fb fc union)) occ in
    Simpl (flag, occ)
  | Cbv flag -> Cbv (glob_red_flag fb flag)
  | Cbn flag -> Cbn (glob_red_flag fb flag)
  | Lazy flag -> Lazy (glob_red_flag fb flag)
  | Unfold l ->
    Unfold (List.map (fun (occ_expr, b) -> occ_expr, fb b) l)
  | Fold l -> Fold (List.map fa l)
  | Pattern l ->
    Pattern (List.map (fun (occ_expr, a) -> occ_expr, fa a) l)
  | ExtraRedExpr s -> ExtraRedExpr s
  | CbvVm o ->
    let o = Option.map (fun (occ_expr, union) ->
        (occ_expr, Util.map_union fb fc union)) o
    in CbvVm o
  | CbvNative o ->
    let o = Option.map (fun (occ_expr, union) ->
        (occ_expr, Util.map_union fb fc union)) o
    in CbvNative o

let with_coercion f (cflag, x) = (cflag, f x)

let hint_info_gen f h =
  Typeclasses.{
    hint_priority = h.hint_priority;
    hint_pattern = Option.map f h.hint_pattern
  }

let module_signature f = function
  | Declaremods.Enforce x -> Declaremods.Enforce (f x)
  | Declaremods.Check l ->
    let l = List.map f l in
    Declaremods.Check l
end

(* Specialized mapper for our remove_notation procedure *)
let map_constr_pattern_expr
    (f: constr_expr -> constr_expr)
    (e: constr_pattern_expr) =
  f e

let map_raw_red_expr f =
  Map.red_expr_gen f (fun x -> x) (map_constr_pattern_expr f)

let map_definition_expr f = function
  | Vernacexpr.ProveBody (l, cexpr) -> Vernacexpr.ProveBody (l, f cexpr)
  | Vernacexpr.DefineBody (l, o, cexpr, ocexpr) ->
    let o = Option.map (map_raw_red_expr f) o in
    Vernacexpr.DefineBody (l, o, f cexpr, Option.map f ocexpr)

let rec map_cases_pattern_expr f cpe =
  CAst.map (map_cases_pattern_expr_r f) cpe
and map_cases_pattern_expr_r f = function
    | CPatAlias (cpe, l) -> CPatAlias (map_cases_pattern_expr f cpe, l)
    | CPatCstr (q, clo, cl) ->
      let clo = Option.map (List.map (map_cases_pattern_expr f)) clo in
      let cl = List.map (map_cases_pattern_expr f) cl in
      CPatCstr (q, clo, cl)
    | CPatAtom qo -> CPatAtom qo
    | CPatOr cl -> CPatOr (List.map (map_cases_pattern_expr f) cl)
    | CPatNotation (n, subst, cl) ->
      let subst = map_cases_pattern_notation_substitution f subst in
      let cl = List.map (map_cases_pattern_expr f) cl in
      CPatNotation (n, subst, cl)
    | CPatPrim p -> CPatPrim p
    | CPatRecord qcl ->
      CPatRecord (List.map
                    (fun (q, c) -> (q, map_cases_pattern_expr f c)) qcl)
    | CPatDelimiters (s, c) ->
      CPatDelimiters (s, map_cases_pattern_expr f c)
    | CPatCast (c, cexpr) ->
      CPatCast (map_cases_pattern_expr f c, f cexpr)
and map_cases_pattern_notation_substitution f (cl, cll) =
  let cl = List.map (map_cases_pattern_expr f) cl in
  let cll = List.map (List.map (map_cases_pattern_expr f)) cll in
  (cl, cll)

let map_local_binder_expr f = function
  | CLocalAssum (l, b, cexpr) -> CLocalAssum (l, b, f cexpr)
  | CLocalDef (l, cexpr, ocexpr) ->
    CLocalDef (l, f cexpr, Option.map f ocexpr)
  | CLocalPattern ast ->
    let ast = CAst.map (fun (cpe, ocexpr) ->
        (map_cases_pattern_expr f cpe, Option.map f ocexpr)) ast in
    CLocalPattern ast

let map_proof_expr f (id, (bl, cexpr)) =
  (id, (List.map (map_local_binder_expr f) bl, f cexpr))

let rec map_recursion_order_expr f roe =
  CAst.map (map_recursion_order_expr_r f) roe
and map_recursion_order_expr_r f = function
  | CStructRec l -> CStructRec l
  | CWfRec (l, cexpr) -> CWfRec (l, f cexpr)
  | CMeasureRec (lo, cexpr, ocexpr) ->
    CMeasureRec (lo, f cexpr, Option.map f ocexpr)

let map_local_decl_expr f = function
  | Vernacexpr.AssumExpr (l, cexpr) -> Vernacexpr.AssumExpr (l, f cexpr)
  | Vernacexpr.DefExpr (l, cexpr, ocexpr) ->
    Vernacexpr.DefExpr (l, f cexpr, Option.map f ocexpr)

(* let map_constructor_expr f = *)
(*   Map.with_coercion (fun (l, cexpr) -> (l, f cexpr)) *)

(* let map_inductive_params_expr f (bl, obl) = *)
(*   (List.map (map_local_binder_expr f) bl, *)
(*    Option.map (List.map (map_local_binder_expr f)) obl) *)

let map_constructor_list_or_record_decl_expr f = function
  (* TODO: understand why rewriting in here makes the
   * evaluation fail
   *)
  | Vernacexpr.Constructors cl ->
    Vernacexpr.Constructors cl
    (* Vernacexpr.Constructors (List.map (map_constructor_expr f) cl) *)
  | Vernacexpr.RecordDecl (lo, l) ->
    let l =
      List.map (fun (ldecl, recf) -> (map_local_decl_expr f ldecl, recf)) l in
    Vernacexpr.RecordDecl (lo, l)

let map_inductive_expr (f: constr_expr -> constr_expr)
    (ie: Vernacexpr.inductive_expr) : Vernacexpr.inductive_expr =
  let _ = f in
  let  (i, bl, ocexpr, kind, constructors) = ie in
  (i,
   List.map (map_local_binder_expr f) bl,
   Option.map f ocexpr,
   kind,
   map_constructor_list_or_record_decl_expr f constructors
  )

let map_fix_expr_gen fa f expr =
  Vernacexpr.{
    fname = expr.fname;
    univs = expr.univs;
    rec_order = fa expr.rec_order;
    binders = List.map (map_local_binder_expr f) expr.binders;
    rtype = f expr.rtype;
    body_def = Option.map f expr.body_def;
    notations = expr.notations (* leave the notation part as is *)
  }

let map_fixpoint_expr f =
  map_fix_expr_gen (Option.map (map_recursion_order_expr f)) f

let map_cofixpoint_expr f =
  map_fix_expr_gen (fun () -> ()) f

let map_hint_info_expr f = Map.hint_info_gen (map_constr_pattern_expr f)

(* module related stuff *)
let map_with_declaration_ast f t =
  match t with
  | CWith_Module _ -> t
  | CWith_Definition (ids, univo, cexpr) ->
    CWith_Definition (ids, univo, f cexpr)

let rec map_with_module_ast_r f t =
  match t with
  | CMident _ -> t
  | CMapply (m0, m1) ->
    CMapply (map_with_module_ast f m0, map_with_module_ast f m1)
  | CMwith (m, wda) ->
    CMwith (map_with_module_ast f m, map_with_declaration_ast f wda)
and map_with_module_ast f m = CAst.map (map_with_module_ast_r f) m

let map_module_ast_inl f (m, d) =
  (map_with_module_ast f m, d)

let map_module_binder f (b, lid, m) =
  (b, lid, map_module_ast_inl f m)

(* hints_expr *)
let map_reference_or_constr f e =
  let open Hints in
  match e with
  | HintsReference _ -> e
  | HintsConstr cexpr -> HintsConstr (f cexpr)

let map_hints_expr f e =
  let open Hints in
  match e with
  | HintsResolve l ->
    let l = List.map (fun (info, b, e) ->
        (map_hint_info_expr f info,
         b,
         map_reference_or_constr f e)) l in
    HintsResolve l
  | HintsImmediate l ->
    let l = List.map (map_reference_or_constr f) l in
    HintsImmediate l
  | HintsExtern (i, ocexpr, gen) ->
    let ocexpr = Option.map f ocexpr in
    HintsExtern (i, ocexpr, gen)
  | _ -> e

(* searchable, locatable, ... *)
let map_search_about_item f s =
  let open Vernacexpr in
  match s with
  | SearchSubPattern cpe ->
    let cpe = map_constr_pattern_expr f cpe in
    SearchSubPattern cpe
  | SearchString _ -> s

let map_searchable f s =
  let open Vernacexpr in
  match s with
  | SearchPattern cpe ->
    let cpe = map_constr_pattern_expr f cpe in
    SearchPattern cpe
  | SearchRewrite cpe ->
    let cpe = map_constr_pattern_expr f cpe in
    SearchRewrite cpe
  | SearchHead cpe ->
    let cpe = map_constr_pattern_expr f cpe in
    SearchHead cpe
  | SearchAbout l ->
    let l = List.map (fun (b, s) ->
        (b, map_search_about_item f s)) l in
    SearchAbout l
  | Search l ->
    let l = List.map (fun (b, s) ->
        (b, map_search_about_item f s)) l in
    Search l

let map_comment f c =
  match c with
  | Vernacexpr.CommentConstr c ->
    Vernacexpr.CommentConstr (f c)
  | _ -> c

(* Duplicated from serapi_protocol
   TODO: expose it correctly ?
 *)
let context_of_st m = match m with
  | `Valid (Some { Vernacstate.lemmas = Some lemma; _ } ) ->
    Vernacstate.LemmaStack.with_top_pstate lemma
      ~f:(fun p -> Pfedit.get_current_context p)
  | _ ->
    let env = Global.env () in Evd.from_env env, env


let remove_notation env evar_map cexpr =
  let ci = Constrintern.interp_constr env evar_map cexpr in
  Constrextern.extern_constr true env evar_map (fst ci)

let remove_notation_ast ~doc ~sid (ast: Vernacexpr.vernac_control) =
  let open Vernacexpr in
  let st = Stm.state_of_id ~doc sid in
  let sigma, env = context_of_st st in
  let f = remove_notation env sigma in
  let strip ast =
    match ast with
    (* Syntax *)
    | VernacInfix (l, cexpr, o) ->
      VernacInfix (l, f cexpr, o)

    (* Gallina *)
    | VernacDefinition (kind, name_decl, def_expr) ->
      let def_expr = map_definition_expr f def_expr in
      VernacDefinition (kind, name_decl, def_expr)
    | VernacStartTheoremProof (kind, plist) ->
      VernacStartTheoremProof (kind, List.map (map_proof_expr f) plist)
    | VernacExactProof cexpr -> VernacExactProof (f cexpr)
    | VernacAssumption (d, i, cl) ->
      let cl =
        List.map (Map.with_coercion (fun (il, cexpr) -> (il, f cexpr))) cl in
      VernacAssumption (d, i, cl)
    (* !! We don't strip the notation part of VernacInductive as they
     * !! contain notations.
     *)
    | VernacInductive (ocumul, priv, flag, ll) ->
      let ll =
        List.map (fun (i, d) ->
            (map_inductive_expr f i, d)) ll in
      VernacInductive (ocumul, priv, flag, ll)
    | VernacFixpoint (d, fl) ->
      VernacFixpoint (d, List.map (map_fixpoint_expr f) fl)
    | VernacCoFixpoint (d, cofl) ->
      VernacCoFixpoint (d, List.map (map_cofixpoint_expr f) cofl)

    (* Gallina extensions *)

    (* Type classes *)
    | VernacInstance (name, bl, cexpr, body, hint) ->
      let bl = List.map (map_local_binder_expr f) bl in
      let cexpr = f cexpr in
      let body = Option.map (fun (b, c) -> (b, f c)) body in
      let hint = Map.hint_info_gen f hint in
      VernacInstance (name, bl, cexpr, body, hint)
    | VernacDeclareInstance (name, binders, typ, info) ->
      let binders = List.map (map_local_binder_expr f) binders in
      let typ = f typ in
      let info = Map.hint_info_gen f info in
      VernacDeclareInstance (name, binders, typ, info)
    | VernacContext binders ->
      let binders = List.map (map_local_binder_expr f) binders in
      VernacContext binders
    | VernacExistingInstance l ->
      let l = List.map (fun (q, h) -> (q, Map.hint_info_gen f h)) l in
      VernacExistingInstance l

    (* Modules and Module Types *)
    | VernacDeclareModule (b, id, mbinders, mast) ->
      let mbinders = List.map (map_module_binder f) mbinders in
      let mast = map_module_ast_inl f mast in
      VernacDeclareModule (b, id, mbinders, mast)
    | VernacDefineModule (b, id, mbinders, msig, mast) ->
      let mbinders = List.map (map_module_binder f) mbinders in
      let msig = Map.module_signature (map_module_ast_inl f) msig in
      let mast = List.map (map_module_ast_inl f) mast in
      VernacDefineModule (b, id, mbinders, msig, mast)
    | VernacDeclareModuleType (id, mbinders, mast0, mast1) ->
      let mbinders = List.map (map_module_binder f) mbinders in
      let mast0 = List.map (map_module_ast_inl f) mast0 in
      let mast1 = List.map (map_module_ast_inl f) mast1 in
      VernacDeclareModuleType (id, mbinders, mast0, mast1)
    | VernacInclude mast ->
      let mast = List.map (map_module_ast_inl f) mast in
      VernacInclude mast

    (* Solving *)
    | VernacSolveExistential (i, cexpr) ->
      VernacSolveExistential (i, f cexpr)

    (* Auxiliary file and library management *)

    (* State management *)

    (* Resetting *)

    (* Commands *)
    | VernacHints (l, h) ->
      let h = map_hints_expr f h in
      VernacHints (l, h)
    | VernacSyntacticDefinition (ident, (idl, cexpr), flag) ->
      let cexpr = f cexpr in
      VernacSyntacticDefinition (ident, (idl, cexpr), flag)
    | VernacReserve l ->
      let l = List.map (fun (l, cexpr) -> (l, f cexpr)) l in
      VernacReserve l
    | VernacCheckMayEval (rreo, ogs, cexpr) ->
      let rreo = Option.map (map_raw_red_expr f) rreo in
      let cexpr = f cexpr in
      VernacCheckMayEval (rreo, ogs, cexpr)
    | VernacGlobalCheck cexpr ->
      VernacGlobalCheck (f cexpr)
    | VernacDeclareReduction (s, rre) ->
      let rre = map_raw_red_expr f rre in
      VernacDeclareReduction (s, rre)
    | VernacSearch (s, go, sr) ->
      let s = map_searchable f s in
      VernacSearch (s, go, sr)
    | VernacPrimitive (id, op_or_type, ocexpr) ->
      let ocexpr = Option.map f ocexpr in
      VernacPrimitive (id, op_or_type, ocexpr)
    | VernacComments l ->
      let l = List.map (map_comment f) l in
      VernacComments l

    (* Proof management *)

    (* For extension *)

    (* All commands that don't involve constr_expr *)
    | _ -> ast
  in
  let strip ast =
    Vernacexpr.{ ast with expr = Constrextern.without_symbols strip ast.expr } in
  CAst.map strip ast
