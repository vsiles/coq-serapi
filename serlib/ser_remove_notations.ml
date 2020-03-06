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
end

(* Specialized mapper for constr_pattern_expr *)
let map_constr_pattern_expr
    (f: constr_expr -> constr_expr)
    (e: constr_pattern_expr) =
  f e

(* Specialized mapper for raw_red_expr *)
let map_raw_red_expr f =
  Map.red_expr_gen f (fun x -> x) (map_constr_pattern_expr f)

(* Specialized mapper for definition_expr *)
let map_definition_expr f = function
  | Vernacexpr.ProveBody (l, cexpr) -> Vernacexpr.ProveBody (l, f cexpr)
  | Vernacexpr.DefineBody (l, o, cexpr, ocexpr) ->
    let o = Option.map (map_raw_red_expr f) o in
    Vernacexpr.DefineBody (l, o, f cexpr, Option.map f ocexpr)

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
  let st = Stm.state_of_id ~doc sid in
  let sigma, env = context_of_st st in
  let strip ast =
    match ast with
    | Vernacexpr.VernacDefinition (kind, name_decl, def_expr) ->
      let f = remove_notation env sigma in
      let def_expr = map_definition_expr f def_expr in
      Vernacexpr.VernacDefinition (kind, name_decl, def_expr)
    | Vernacexpr.VernacNotation _ -> ast
    | Vernacexpr.VernacInductive _ -> ast
    | _ -> failwith "strip_ast not supported"
  in
  let strip ast =
    Vernacexpr.{ ast with expr = Constrextern.without_symbols strip ast.expr } in
  CAst.map strip ast
