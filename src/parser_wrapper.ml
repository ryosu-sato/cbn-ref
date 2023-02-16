open Util
open Asttypes
open Typedtree
module P = Path (* Path is shadowed by Type.Path *)
open Type
open Type_util
open Syntax
open Term_util

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check "Parser_wrapper" end)
module Dbg_orig = Debug.Make(struct let check = Flag.Debug.make_check "Parser_wrapper.orig" end)

module Types = struct
  open Asttypes
  include Types
  let get_id (ty:type_expr) = ty.id
  let get_level (ty:type_expr) = ty.level
  let get_desc (ty:type_expr) = ty.desc

  let rec row_fields row =
    match get_desc row.row_more with
    | Tvariant row' ->
        row.row_fields @ row_fields row'
    | _ ->
        row.row_fields

  let rec row_repr_no_fields row =
    match get_desc row.row_more with
    | Tvariant row' -> row_repr_no_fields row'
    | _ -> row

  type row_desc_repr =
    Row of { fields: (label * row_field) list;
             more:   type_expr;
             closed: bool;
             fixed:  fixed_explanation option;
             name:   (P.t * type_expr list) option }

  let row_repr row =
    let fields = row_fields row in
    let row = row_repr_no_fields row in
    Row { fields;
          more = row.row_more;
          closed = row.row_closed;
          fixed = row.row_fixed;
          name = row.row_name }

  let row_field_repr fi = fi

  let create desc =
    Private_type_expr.create desc ~level:0 ~scope:0 ~id:0
end
open Types

let from_list ~f xs =
  List.map f xs

let from_option ~f ~env x =
  match x with
  | None -> None
  | Some y ->
      let y = f ~env y in
       Some y

let name_of_ident = Id.normalize_name -| Ident.name

let rec from_type_expr ~tenv ty0 : typ =
  let from = from_type_expr ~tenv in
  let typ = Ctype.correct_levels ty0 in (* Need? *)
  if false then Format.printf "ty0: %a@." Printtyp.type_expr ty0;
  match Types.get_desc typ with
  | Tvar _ -> unsupported "%s Tvar" __FUNCTION__
  | Tarrow(_, typ1, typ2, _) -> TFun(from typ1, from typ2)
  | Ttuple _ -> unsupported "%s" __FUNCTION__
  | Tconstr(path, [], _) when P.name path = "int" -> Ty.int
  | Tconstr(path, [], _) when P.name path = "bool" -> Ty.bool
  | Tconstr(path, [], _) when P.name path = "unit" -> Ty.unit
  | Tconstr _ -> unsupported "%s" __FUNCTION__
  | Tobject _ -> unsupported "%s" __FUNCTION__
  | Tfield _ -> unsupported "Tfield"
  | Tnil -> unsupported "Tnil"
  | Tlink ty -> from ty
  | Tsubst _ -> unsupported "Tsubst"
  | Tvariant _ -> unsupported "%s" __FUNCTION__
  | Tunivar _ -> unsupported "%s" __FUNCTION__
  | Tpoly(typ,[]) -> from typ
  | Tpoly _ -> unsupported "Tsubst"
  | Tpackage _ -> unsupported "Tsubst"

and from_core_type ~tenv (ty:core_type) =
  from_type_expr ~tenv ty.ctyp_type

and take_arg_types ~tenv ty n =
  if n = 0 then
    []
  else
    match
      ty
      |> Ctype.correct_levels
      |> Ctype.full_expand ~may_forget_scope:false tenv
      |> Types.get_desc
    with
    | Tarrow(_,ty1,ty2,_) ->
        let ty = from_type_expr ~tenv ty1 in
        let tys = take_arg_types ~tenv ty2 (n-1) in
        ty::tys
    | _ -> invalid_arg "%s@." __FUNCTION__

and from_ident x typ =
  let id = 0 in
  Id.make ~id (name_of_ident x) typ

and lid_of (path:P.t) typ =
  match path with
  | Pident id -> Id.make (Ident.name id) typ
  | Pdot _ -> unsupported "%s" __FUNCTION__
  | Papply (_, _) -> assert false

and from_ident_path (path:P.t) typ = Id.make ~id:0 (P.name path) typ

and get_label_name prefix label =
  prefix ^ label.lbl_name

and from_constant = function
  | Const_int n -> Int n
  | _ -> unsupported "%s" __FUNCTION__


and is_var_case case =
  match case with
  | {c_lhs={pat_desc=Tpat_var _}; c_guard=None} -> true
  | {c_lhs={pat_desc=Tpat_alias({pat_desc=Tpat_any},_,_)}; c_guard=None} -> true
  | _ -> false

and from_pattern {pat_desc; pat_env=tenv; pat_type=typ} =
  let ty = from_type_expr ~tenv typ in
  match pat_desc with
  | Tpat_any -> Id.new_var ~name:"_" ty
  | Tpat_var(x,_) -> from_ident x ty
  | _ -> unsupported "%s" __FUNCTION__

and from_let_rec pats =
  let xs = from_list pats ~f:(fun {vb_pat} -> from_pattern vb_pat) in
  let ts = from_list pats ~f:(fun {vb_expr} -> from_expression vb_expr) in
  List.combine xs ts

and binops =
   ["=", make_eq;
   "<>", make_neq;
   "<",  make_lt;
   ">",  make_gt;
   "<=", make_leq;
   ">=", make_geq;
   "&&", make_and;
   "||", make_or;
   "+",  make_add;
   "-",  make_sub;
   "*",  make_mul]

and primitives () =
  let binops = List.map (fun (s,f) -> "Stdlib."^s, f) binops @@@ binops in
  let make_binop (s,f) =
    s,
    function [t1;t2] -> f t1 t2
           | [t1] ->
               let x = Id.new_var t1.typ in
               let y = Id.new_var t1.typ in
               let t = f (Term.var x) (Term.var y) in
               make_app (make_funs [x;y] t) [t1]
           | _ -> assert false
  in
  ["@@", (function t1::ts -> Term.(t1 @@ ts) | _ -> assert false);
   "~-", (function [t] -> Term.(~- t) | _ -> assert false);
   "not", (function [t] -> Term.(not t) | _ -> assert false);
  ]
  @ List.map make_binop binops
  |> Fmap.(list (fst Id.normalize_name))

and conv_primitive_app (t:term) ts =
  let prim = primitives () in
  match t.desc with
  | Var x ->
      begin
        match List.find ((=) (Id.name x) -| fst) prim with
        | _, f -> f ts
        | exception Not_found -> make_app t ts
      end
  | _ -> make_app t ts

and from_expression {exp_desc; exp_type; exp_env=tenv} =
  let typ = from_type_expr ~tenv exp_type in
  match exp_desc with
  | Texp_ident(path, _, _) ->
      let x = from_ident_path path typ in
      make_var x
  | Texp_constant c ->
       (make (Const (from_constant c)) typ)
  | Texp_let(_, pats, e) ->
      let bindings = from_let_rec pats in
      let t = from_expression e in
      make_let bindings t
  | Texp_apply(e, args) -> (* TODO: fix the evaluation when `xs <> []` *)
      let t = from_expression e in
      let xs,ts =
        let tys = take_arg_types ~tenv:e.exp_env e.exp_type (List.length args) in
        List.L.fold_right2 args tys ~init:([],[])
          ~f:(fun (label,arg) ty (xs,ts) ->
            let (t),xs =
              match label, arg with
              | Optional _, Some e ->
                  (* I don't know why, but the type environment of e is not appropriate for this context *)
                  from_expression {e with exp_env=tenv}, xs
              | _, Some e ->
                  from_expression e, xs
              | _, None ->
                  let x = Id.new_var ty in
                  Term.var x, x::xs
            in
            xs, t::ts)
      in
      Term.funs xs @@ conv_primitive_app t ts
  | Texp_ifthenelse(e1,e2,e3) ->
      let t1 = from_expression e1 in
      let t2 = from_expression e2 in
      let t3 =
        match e3 with
        | None ->  unit_term
        | Some e3 -> from_expression e3
      in
      make_if t1 t2 t3
  | Texp_sequence(e1,e2) ->
      let _t1 = from_expression e1 in
      let _t2 = from_expression e2 in
      assert false
  | Texp_assert e ->
      let t = from_expression e in
      let base = Type.ValE._TBase typ in
      let t' =
        if t.desc = Const False
        then make_fail base
        else make_assert t (default_value_of base)
      in
      t'
  | Texp_function {cases = [{c_lhs; c_guard = None; c_rhs}]; partial = Total} ->
      let ty = from_type_expr ~tenv:c_lhs.pat_env c_lhs.pat_type in
      let x =
        match c_lhs.pat_desc with
        | Tpat_var(x, _) -> from_ident x ty
        | Tpat_any -> Id.new_var ~name:"u" ty
        | Tpat_alias({pat_desc = Tpat_any}, x, _) -> from_ident x ty
        | _ -> unsupported "%s Texp_function" __FUNCTION__
      in
      let t = from_expression c_rhs in
      make_fun x t
  | Texp_function _ -> unsupported "%s Texp_function" __FUNCTION__
  | Texp_match (_, _, _) -> unsupported "%s Texp_match" __FUNCTION__
  | Texp_try (_, _) -> unsupported "%s Texp_try" __FUNCTION__
  | Texp_tuple _ -> unsupported "%s Texp_tuple" __FUNCTION__
  | Texp_construct(loc, _, []) when Longident.flatten (loc.txt) = ["true"] -> true_term
  | Texp_construct(loc, _, []) when Longident.flatten (loc.txt) = ["false"] -> false_term
  | Texp_construct(loc, _, []) when Longident.flatten (loc.txt) = ["()"] -> unit_term
  | Texp_construct (_, _, _) -> unsupported "%s Texp_construct" __FUNCTION__
  | Texp_variant (_, _) -> unsupported "%s Texp_variant" __FUNCTION__
  | Texp_record _ -> unsupported "%s Texp_record" __FUNCTION__
  | Texp_field (_, _, _) -> unsupported "%s Texp_field" __FUNCTION__
  | Texp_setfield (_, _, _, _) -> unsupported "%s Texp_setfield" __FUNCTION__
  | Texp_array _ -> unsupported "%s Texp_array" __FUNCTION__
  | Texp_while (_, _) -> unsupported "%s Texp_while" __FUNCTION__
  | Texp_for (_, _, _, _, _, _) -> unsupported "%s Texp_for" __FUNCTION__
  | Texp_send (_, _, _) -> unsupported "%s Texp_send" __FUNCTION__
  | Texp_new (_, _, _) -> unsupported "%s Texp_new" __FUNCTION__
  | Texp_instvar (_, _, _) -> unsupported "%s Texp_instvar" __FUNCTION__
  | Texp_setinstvar (_, _, _, _) -> unsupported "%s Texp_setinstvar" __FUNCTION__
  | Texp_override (_, _) -> unsupported "%s Texp_override" __FUNCTION__
  | Texp_letmodule (_, _, _, _, _) -> unsupported "%s Texp_letmodule" __FUNCTION__
  | Texp_letexception (_, _) -> unsupported "%s Texp_letexception" __FUNCTION__
  | Texp_lazy _ -> unsupported "%s Texp_lazy" __FUNCTION__
  | Texp_object (_, _) -> unsupported "%s Texp_object" __FUNCTION__
  | Texp_pack _ -> unsupported "%s Texp_pack" __FUNCTION__
  | Texp_letop _ -> unsupported "%s Texp_letop" __FUNCTION__
  | Texp_unreachable -> unsupported "%s  " __FUNCTION__
  | Texp_extension_constructor (_, _) -> unsupported "%s Texp_extension_constructor" __FUNCTION__
  | Texp_open (_, _) -> unsupported "%s Texp_open" __FUNCTION__


and from_str_item str_item =
  match str_item.str_desc with
  | Tstr_eval(e,_) ->
      let t = from_expression e in
      [Id.new_var ~name:"u" t.typ, t]
  | Tstr_value(Recursive,pats) ->
      let bindings = from_let_rec pats in
      bindings
  | Tstr_value(Nonrecursive,pats) ->
      let decls =
        from_list pats
          ~f:(fun {vb_pat;vb_expr} ->
            let x = from_pattern vb_pat in
            let t = from_expression vb_expr in
            (x, t))
      in
      decls
  | Tstr_primitive _ -> unsupported "%s" __FUNCTION__
  | Tstr_type _ -> unsupported "%s" __FUNCTION__
  | Tstr_typext _ -> unsupported "%s" __FUNCTION__
  | Tstr_exception _ -> unsupported "%s" __FUNCTION__
  | Tstr_module _ -> unsupported "%s" __FUNCTION__
  | Tstr_recmodule _ -> unsupported "%s" __FUNCTION__
  | Tstr_modtype _ -> unsupported "%s" __FUNCTION__
  | Tstr_open _ -> unsupported "%s" __FUNCTION__
  | Tstr_class _ -> unsupported "%s" __FUNCTION__
  | Tstr_class_type _ -> unsupported "%s" __FUNCTION__
  | Tstr_include _ -> unsupported "%s" __FUNCTION__
  | Tstr_attribute _ -> unsupported "%s" __FUNCTION__

and from_structure struc =
  Dbg_orig.printf "struc: @[%a@." Printtyped.implementation struc;
  List.L.fold_left
    struc.str_items
    ~init:[]
    ~f:(fun decls str_item -> decls @ from_str_item str_item)

let from_top_level_phrase (tenv, acc) ptop =
  match ptop with
  | Parsetree.Ptop_dir _ -> unsupported "toplevel_directive"
  | Parsetree.Ptop_def struc ->
      let struc',_,_,tenv' = Typemod.type_structure tenv struc in
      let decls' = from_structure struc' in
      tenv', acc @ decls'

let () = Compmisc.init_path ()

let parse_lexbuf ?tenv lb =
  let tenv = Option.default_delayed Compmisc.initial_env tenv in
  lb
  |> Parse.use_file
  |> List.fold_left from_top_level_phrase (tenv,[])

let parse_string ?tenv s =
  let lb = Lexing.from_string s in
  lb.Lexing.lex_curr_p <- {pos_fname = "-"; pos_lnum = 1; pos_cnum = 0; pos_bol = 0};
  parse_lexbuf ?tenv lb

let parse_file ?tenv filename =
  IO.CPS.open_in filename IO.input_all
  |> parse_string ?tenv
  |> snd
