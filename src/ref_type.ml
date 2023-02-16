open Util
open Type
open Syntax
open Type_util
open Term_util

module S = Strictness

type t =
  | TBase of term * base * id * term
  | TFun of id * t * bool * t (* tree denotes strict functions *)
[@@deriving show]

let _TBase(c,b,x,t) = TBase(c,b,x,t)
let _TFun(x,ty1,b,ty2) = TFun(x,ty1,b,ty2)

module Val = struct
  let _TBase  = function TBase(c,b,x,t)    -> Some (c, b, x, t)        | _ -> None
  let _TFun   = function TFun(x,ty1,b,ty2) -> Some (x, ty1, b, ty2) | _ -> None
end

module ValE = struct
  let _TBase ty = match Val._TBase ty with Some x -> x | _ -> invalid_arg "%s" __FUNCTION__
  let _TFun ty  = match Val._TFun ty  with Some x -> x | _ -> invalid_arg "%s" __FUNCTION__
end

module Is = struct
  let _TBase  = function TBase _  -> true | _ -> false
  let _TFun   = function TFun _   -> true | _ -> false
end

let rec decomp_tfun typ =
  match typ with
  | TFun(x,ty1,b,ty2) ->
      let xs,ty2 = decomp_tfun ty2 in
      (x,ty1,b) :: xs, ty2
  | _ -> [], typ

let rec print fm typ =
  match typ with
  | TBase(c,b,x,t) when Id.(x = dummy_var) && c = Term.tt && t = Term.tt -> Format.printf "@[%a@]" Print.T.base b
  | TBase(c,b,x,t) when Id.(x = dummy_var) && t = Term.tt -> Format.printf "@[%a => %a@]" Print.term c Print.T.base b
  | TBase(c,b,x,t) when Id.(x = dummy_var) && c = Term.tt -> Format.printf "@[@[{_ : %a | %a}@]@]" Print.T.base b Print.term t
  | TBase(c,b,x,t) when Id.(x = dummy_var) -> Format.printf "(@[%a => @[{_ : %a | %a}@]@])" Print.term c Print.T.base b Print.term t
  | TBase(c,b,x,t) when c = Term.tt -> Format.printf "@[{%a:%a | %a}@]" Id.print x Print.T.base b Print.term t
  | TBase(c,b,x,t) -> Format.printf "(@[%a => @[{%a:%a | %a}@]@])" Print.term c Id.print x Print.T.base b Print.term t
  | TFun _ ->
      let rec aux fm (xtybs, ty2) =
        match xtybs with
        | [] ->
            print fm ty2
        | (x,ty1,b)::tys' ->
            let arrow = if b then "-o" else "->" in
            Format.fprintf fm "@[<hov 2>%a:%a %s@ %a@]" Id.print x print ty1 arrow aux (tys',ty2)
      in
      Format.fprintf fm "(%a)" aux @@ decomp_tfun typ

let simple_base b = TBase(Term.tt, b, dummy_var, Term.tt)

let new_predicate xs =
  let xs = List.filter (Id.typ |- Type.Is._TBase) xs in
  let ty = List.fold_right (fun x ty -> Type.TFun(Id.typ x, ty)) xs Ty.bool in
  let p = Id.new_predicate ty in
  let args = List.map Term.var xs in
  Term.(var p @ args)

let remove_gaurd ty =
  match ty with
  | TBase(_, base, x, p2) -> TBase(Term.tt, base, x, p2)
  | _ -> ty

let rec make_template sol xs (ty : S.ty) : t =
  match ty with
  | TBase base ->
      let x = Id.new_var (S.to_simple ty) in
      let p1 = new_predicate xs in
      let p2 = new_predicate (x::xs) in
      TBase(p1, base, x, p2)
  | TFun(ty1, l, ty2) ->
      let x = Id.new_var @@ Strictness.to_simple ty1 in
      let ty1' = remove_gaurd @@ make_template sol xs ty1 in
      let ty2' = make_template sol (x::xs) ty2 in
      TFun(x, ty1', sol l, ty2')

let type_of_base_const c =
  let ty = type_of_const c in
  let base = Type.ValE._TBase ty in
  let x = Id.new_var (type_of_const c) in
  TBase(Term.tt, base, x, Term.(var x = make_const c))

let type_of_binop op =
  match type_of_const (BinOp op) with
  | TFun(TBase b1, TFun(TBase b2, TBase b3)) ->
      let ty1 = simple_base b1 in
      let ty2 = simple_base b2 in
      let x = Id.new_var (TBase b1) in
      let y = Id.new_var (TBase b2) in
      let r = Id.new_var (TBase b3) in
      let ty3 = TBase(Term.tt, b3, r, Term.(var r = make_binop op (var x) (var y))) in
      TFun(x, ty1, true, TFun(y, ty2, true, ty3))
  | _ -> assert false

let type_of_const c =
  match c with
  | Unit -> TBase(Term.tt, TUnit, dummy_var, Term.tt)
  | True
  | False
  | Int _ -> type_of_base_const c
  | Rand (TBase base) -> TBase(Term.tt, base, dummy_var, Term.tt)
  | Rand _ -> unsupported "%s" __FUNCTION__
  | Fail b -> TBase(Term.ff, b, dummy_var, Term.ff)
  | BinOp op -> type_of_binop op
  | Not -> assert false

let rec subst_var x y ty =
  let sbst = Term_util.subst_var x y in
  let sbst_ty = subst_var x y in
  match ty with
  | TBase(c, b, z, t) -> TBase(sbst c, b, z, sbst t)
  | TFun(z, ty1, b, ty2) ->
      assert Id.(x <> z);
      TFun(z, sbst_ty ty1, b, sbst_ty ty2)

let rec simple_ref ty =
  match ty with
  | TBase(_,b,x,_) -> TBase(Term.tt, b, x, Term.tt)
  | TFun(x,ty1,_,ty2) -> TFun(x, simple_ref ty1, false, simple_ref ty2)
