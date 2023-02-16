open Util
open Type
open Type_util

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let print_base fm b =
  match b with
  | TUnit -> Format.fprintf fm "unit"
  | TBool -> Format.fprintf fm "bool"
  | TInt -> Format.fprintf fm "int"

let rec print fm typ =
  match typ with
  | TBase b -> print_base fm b
  | TVar {contents=Some typ} -> print fm typ
  | TVar {contents=None} -> unsupported "TVar"
  | TFun _ ->
      let rec aux fm (tys, typ) =
        match tys with
        | [] ->
            print fm typ
        | ty::tys' ->
            Format.fprintf fm "@[<hov 2>%a ->@ %a@]" print ty aux (tys',typ)
      in
      Format.fprintf fm "(%a)" aux @@ decomp_tfuns typ

let typ fm typ = Format.fprintf fm "@[%a@]" print typ
let base = print_base
