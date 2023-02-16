open Util
open Type
open Type_util
open Syntax

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

(*** TERM CONSTRUCTORS ***)

let type_of_const = function
  | Unit -> Ty.unit
  | True -> Ty.bool
  | False -> Ty.bool
  | Int _ -> Ty.int
  | Rand ty -> ty
  | Fail b -> TBase b
  | BinOp (Eq | Lt | Gt | Leq | Geq) -> Ty.(fun_ int (fun_ int bool))
  | BinOp (And | Or | Imply) -> Ty.(fun_ bool (fun_ bool bool))
  | BinOp (Add | Sub | Mult | Div) -> Ty.(fun_ int (fun_ int int))
  | Not -> Ty.(fun_ bool bool)

let make_const c = make (Const c) (type_of_const c)

let unit_term = make (Const Unit) Ty.unit
let true_term = make (Const True) Ty.bool
let false_term = make (Const False) Ty.bool
let make_fail b = make (Const (Fail b)) (TBase b)
let make_bool b = if b then true_term else false_term
let make_var x = make (Var x) (Id.typ x)
let make_int n = make (Const(Int n)) Ty.int

let default_value_of b =
  match b with
  | TUnit -> unit_term
  | TBool -> true_term
  | TInt -> make_int 0

(* Note: only for type preserving transformations *)
let make_trans f =
  let rec tr t =
    match f tr t with
    | None ->
        let desc =
          match t.desc with
          | Const _ -> t.desc
          | Var _ -> t.desc
          | Fun(x, t1) -> Fun(x, tr t1)
          | App(t1, ts) -> App(tr t1, List.map tr ts)
          | If(t1, t2, t3) -> If(tr t1, tr t2, tr t3)
          | Let(defs, t1) -> Let(Fmap.(list (snd tr)) defs, tr t1)
          | Fix(x, t) -> Fix(x, tr t)
        in
        {t with desc}
    | Some t -> t
  in
  tr

let rec make_app t ts =
  let ty = t.typ in
  match t.desc, ty, ts with
  | _, _, [] -> t
  | App(t1,ts1), TFun(_,typ), t2::ts2 ->
      make_app (make (App(t1,ts1@[t2])) typ) ts2
  | _, TFun(_,typ), t2::ts ->
      make_app (make (App(t,[t2])) typ) ts
  | _ ->
      let pr = Syntax.pp_term in
      Format.eprintf "Untypable(make_app) FUN:  %a@." pr t;
      Format.eprintf "                    ARGS: %a@." Print_.(list pr) ts;
      assert false

let make_app_raw t ts =
  let t' = make_app t ts in
  {t' with desc = App(t,ts)}

let make_let bindings t2 =
  make (Let(bindings, t2)) t2.typ

let make_fun x t =
  let ty = TFun(Id.typ x, t.typ) in
  let desc = Fun(x, t) in
  make desc ty

let make_funs = List.fold_right make_fun

let make_not t =
  match t.desc with
  | Const True -> false_term
  | Const False -> true_term
  | App({desc = Const Not}, [t]) -> t
  | _ -> make_app (make_const Not) [t]

let make_binop c t1 t2 =
  make_app (make_const (BinOp c)) [t1; t2]

let make_and t1 t2 =
  if t1 = false_term then
    false_term
  else if t1 = true_term then
    t2
  else if t2 = true_term then
    t1
  else
    make_binop And t1 t2

let make_ands ts = List.fold_right make_and ts true_term

let make_or t1 t2 =
  if t1 = true_term then
    true_term
  else if t1 = false_term then
    t2
  else if t2 = false_term then
    t1
  else
    make_binop Or t1 t2

let make_ors ts = List.fold_right make_or ts false_term

let make_imply t1 t2 = (* DO NOT USE IN PROGRAM *)
  if t1 = false_term then
    true_term
  else if t2 = true_term then
    true_term
  else if t1 = true_term then
    t2
  else
    make_binop Imply t1 t2

let make_add t1 t2 =
  if t2.desc = Const (Int 0) then
    t1
  else if t1.desc = Const (Int 0) then
    t2
  else
    make_binop Add t1 t2

let make_sub t1 t2 =
  if t2.desc = Const (Int 0) then
    t1
  else
    make_binop Sub t1 t2

let make_mul t1 t2 =
  if t2.desc = Const (Int 1) then
    t1
  else if t1.desc = Const (Int 1) then
    t2
  else
    make_binop Mult t1 t2

let make_div t1 t2 =
    make_binop Div t1 t2

let make_neg t = make_sub (make_int 0) t

let make_if t1 t2 t3 =
  match t1.desc with
  | Const True -> t2
  | Const False -> t3
  | _ -> make (If(t1, t2, t3)) t2.typ

let make_eq t1 t2 =
  match t1.desc, t2.desc with
  | Const c1, Const c2 -> make_bool (c1 = c2)
  | _ when t1 = t2 -> true_term
  | _ -> make_binop Eq t1 t2

let make_neq t1 t2 =
  make_not (make_eq t1 t2)

let make_lt t1 t2 =
  make_binop Lt t1 t2

let make_gt t1 t2 =
  make_binop Gt t1 t2

let make_leq t1 t2 =
  make_binop Leq t1 t2

let make_geq t1 t2 =
  make_binop Geq t1 t2

let make_binop op =
  match op with
  | Eq -> make_eq
  | Lt -> make_lt
  | Gt -> make_gt
  | Leq -> make_leq
  | Geq -> make_geq
  | And -> make_and
  | Or -> make_or
  | Imply -> make_imply
  | Add -> make_add
  | Sub -> make_sub
  | Mult -> make_mul
  | Div -> make_div

let make_assert t1 t2 = make_if t1 t2 (make_fail (Type.ValE._TBase t2.typ))

(* [x |- t1] t2 *)
let rec subst x t1 t2 =
  let sbst = subst x t1 in
  let desc =
    match t2.desc with
    | Const _ -> t2.desc
    | Var y when Id.(x = y) -> t1.desc
    | Var _ -> t2.desc
    | Fun(y, _) when Id.(x = y) -> t2.desc
    | Fun(y, t2') -> Fun(y, sbst t2')
    | App(t2', ts) -> App(sbst t2', List.map sbst ts)
    | If(t21, t22, t23) -> If(sbst t21, sbst t22, sbst t23)
    | Let(defs, _) when Id.List.mem_assoc x defs -> t2.desc
    | Let(defs, t2') -> Let(Fmap.(list (snd sbst)) defs, sbst t2')
    | Fix(y, _) when Id.(x = y) -> t2.desc
    | Fix(y, t2') -> Fix(y, sbst t2')
  in
  {t2 with desc}

let subst_var x y t = subst x (make_var y) t

let rec get_fv t =
  let get_fv_excep t x = List.filter_out Id.(eq x) @@ get_fv t in
  match t.desc with
  | Const _ -> []
  | Var x -> [x]
  | Fun(x, t) -> get_fv_excep t x
  | App(t, ts) -> get_fv t @@@ List.rev_flatten_map get_fv ts
  | If(t1, t2, t3) -> List.rev_flatten_map get_fv [t1; t2; t3]
  | Let(defs, t) ->
      get_fv t @@@ List.rev_flatten_map (snd |- get_fv) defs
      |> List.filter_out (Id.List.mem_assoc -$- defs)
  | Fix(f, t) -> get_fv_excep t f
let get_fv t = Id.List.unique @@ get_fv t

let rec decomp_ands t =
  match t.desc with
  | App({desc = Const (BinOp And)}, [t1; t2]) ->
      decomp_ands t1 @ decomp_ands t2
  | App({desc = Const (BinOp And)}, _) -> invalid_arg "%s" __FUNCTION__
  | App({desc = Const (BinOp Eq)}, [t1; t2]) when t1.desc = t2.desc -> []
  | _ -> [t]

let rec alpha_rename t =
  let desc =
    match t.desc with
    | Const _ -> t.desc
    | Var _ -> t.desc
    | Fun(x, t1) ->
        let x' = Id.new_var_id x in
        Fun(x', alpha_rename @@ subst_var x x' t1)
    | App(t1, ts) -> App(alpha_rename t1, List.map alpha_rename ts)
    | If(t1, t2, t3) -> If(alpha_rename t1, alpha_rename t2, alpha_rename t3)
    | Let(defs, t1) ->
        let xs = List.map (fst |- Id.new_var_id) defs in
        let defs' = List.map2 (fun x' (x,t) -> x', alpha_rename @@ subst_var x x' t) xs defs in
        let t1' = List.fold_left2 (fun t x' (x,_) -> subst_var x x' t) t1 xs defs in
        Let(defs', alpha_rename t1')
    | Fix _ -> unsupported "%s" __FUNCTION__
  in
  {t with desc}

let rec size_of_term t =
  match t.desc with
  | Const _ -> 1
  | Var _ -> 1
  | Fun(_, t) -> 2 + size_of_term t
  | App(t1, ts) -> 1 + List.sum (List.map size_of_term (t1::ts))
  | If(t1, t2, t3) -> size_of_term t1 + size_of_term t2 + size_of_term t3
  | Let(defs, t1) -> size_of_term t1 + List.sum (List.map (fun (_,t) -> 2 + size_of_term t) defs)
  | Fix(_, t) -> 2 + size_of_term t
let size_of_program p =
  p
  |> List.map (fun (_,(xs,t)) -> 2 + List.length xs + size_of_term t)
  |> List.sum

module Term = struct
  let unit = unit_term
  let tt = true_term
  let true_ = true_term
  let ff = false_term
  let false_ = false_term
  let fail = make_fail
  let var = make_var
  let vars = List.map make_var
  let int = make_int
  let bool = make_bool
  let (@) = make_app
  let (@@) = make_app
  let let_ = make_let
  let fun_ = make_fun
  let funs = make_funs
  let not = make_not
  let (&&) = make_and
  let ands = make_ands
  let (||) = make_or
  let ors = make_ors
  let (=>) = make_imply
  let (+) = make_add
  let (-) = make_sub
  let ( * ) = make_mul
  let (/) = make_div
  let (~-) = make_neg
  let if_ = make_if
  let (=) = make_eq
  let (<>) = make_neq
  let (<) = make_lt
  let (>) = make_gt
  let (<=) = make_leq
  let (>=) = make_geq
  let (<|) t1 op = make_binop op t1 and (|>) mb t2 = mb t2
end
