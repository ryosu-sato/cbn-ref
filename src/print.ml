open Format
open Util
open! Type
open Type_util
open Syntax

module Debug_attr = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__ ^ ".attr") end)
module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let rec print_typ fm t = Print_typ.typ fm t
and print_ids fm xs =
  if xs <> [] then
    let p_id = print_id in
    print_list p_id "@ " ~first:true fm xs

and print_id fm x =
  Id.print fm x

and print_id_typ fm x = fprintf fm "(@[%a:%a@])" print_id x print_typ (Id.typ x)

(* priority (low -> high)
   9 : Seq
   10 : Local, If, Match, TryWith
   15 : Fun
   20 : Pair
   30 : Or
   40 : And
   50 : Eq, Lt, Gt, Leq, Geq, MemSet, Subset
   60 : Cons, AddSet
   65 : Add, Sub
   70 : Mult, Div
   80 : Raise, App, Not, Ref, SetRef
   90 : Field
   100 : Deref
*)

and paren pri p = if pri < p then "","" else "(",")"

and print_binop fm = function
  | Eq -> fprintf fm "="
  | Lt -> fprintf fm "<"
  | Gt -> fprintf fm ">"
  | Leq -> fprintf fm "<="
  | Geq -> fprintf fm ">="
  | And -> fprintf fm "&&"
  | Or -> fprintf fm "||"
  | Imply -> fprintf fm "=>"
  | Add -> fprintf fm "+"
  | Sub -> fprintf fm "-"
  | Mult -> fprintf fm "*"
  | Div -> fprintf fm "/"

and print_termlist pri fm ts =
  print_list (print_term pri) "@ " fm ts

and print_const fm c =
  match c with
  | Unit -> fprintf fm "()"
  | True -> fprintf fm "true"
  | False -> fprintf fm "false"
  | Int n when n<0 -> fprintf fm "(%d)" n
  | Int n -> fprintf fm "%d" n
  | Rand typ' -> fprintf fm "rand_val[%a]" print_typ typ'
  | Fail _ -> fprintf fm "fail"
  | BinOp op -> print_binop fm op
  | Not -> fprintf fm "not"

and print_term pri fm t =
  fprintf fm "@[%a@]" (print_desc pri) t.desc

and print_let_decls fm bindings =
  let first = ref true in
  let print_binding fm (f,t1) =
    let pre =
      if !first then
        "let"
      else
        "and"
    in
    let xs,t1' = decomp_funs t1 in
    fprintf fm "@[<hov 2>%s @[<hov 2>%a%a : %a@] =@ %a@]" pre print_id f print_ids xs Print_typ.typ t1.typ (print_term 0) t1';
    first := false
  in
  print_list ~bopen:(Format.pp_open_hvbox -$- 0) print_binding "@ " fm bindings

and print_desc pri fm desc =
  let pr_t = print_term in
  match desc with
  | Const c -> print_const fm c
  | Var x -> print_id fm x
  | Fun(x,t1) ->
      let xs,t =
        if !!Debug.check then
          [x], t1
        else
          decomp_funs (make desc Ty.int)
      in
      let p = 15 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<hov 2>fun@[%a@] ->@ %a%s@]" s1 print_ids xs (pr_t 0) t s2
  | App({desc = Const Not}, [{desc = App({desc = Const (BinOp Eq)}, [t1; t2])}]) ->
      let p = 50 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[%a@ <>@ %a@]%s" s1 (pr_t p) t1 (pr_t p) t2 s2
  | App({desc = Const (BinOp Mult)}, [{desc=Const (Int -1)}; {desc=Var x}]) ->
      let p = 70 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[-%a@]%s" s1 print_id x s2
  | App({desc = Const (BinOp op)}, [t1; t2]) ->
      let p = match op with Mult|Div -> 70 | Add|Sub -> 65 | And -> 40 | Or -> 30 |Imply -> 25 | _ -> 50 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[%a@ %a@ %a@]%s" s1 (pr_t p) t1 print_binop op (pr_t p) t2 s2
  | App({desc = Const Not}, [t]) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[not@ %a@]%s" s1 (pr_t p) t s2
  | App(t, ts) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[<hov 2>%s%a@ %a%s@]" s1 (pr_t p) t (print_termlist  p) ts s2
  | If(t1, t2, t3) ->
      let p = 10 in
      let s1,s2 = paren pri (if t3.desc = Const Unit then p else p+1) in
      fprintf fm "%s@[<hv>if@[@ %a@]@ then@ " s1 (pr_t p) t1;
      pp_print_if_newline fm ();
      pp_print_string fm "  ";
      fprintf fm "@[%a@]" (pr_t p) t2;
      if t3.desc <> Const Unit then
        begin
          fprintf fm "@ else@ ";
          pp_print_if_newline fm ();
          pp_print_string fm "  ";
          fprintf fm "@[%a@]" (pr_t p) t3
        end;
      fprintf fm "@]%s" s2
  | Let([], t) -> pr_t pri fm t
  | Let(decl, t2) ->
      let p = 10 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<hov>@[<hv>%a@]@ in@ @[<hov>%a@]@]%s" s1 print_let_decls decl (pr_t p) t2 s2
  | Fix(f, t) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[fix %a.@ %a@]%s" s1 print_id f (pr_t p) t s2

let print_term fm = print_term 0 fm

let string_of_const c = Format.asprintf "%a" print_const c
let string_of_binop op = Format.asprintf "%a" print_binop op
let string_of_typ typ = Format.asprintf "%a" print_typ typ
let string_of_constr desc =
  match desc with
  | Const _ -> "Const"
  | Var _ -> "Var"
  | Fun _ -> "Fun"
  | App _ -> "App"
  | If _ -> "If"
  | Let _ -> "Let"
  | Fix _ -> "Fix"

let typ = print_typ
let id fm = print_id fm
let id_typ fm = print_id_typ fm
let const fm = print_const fm
let desc fm = print_desc 0 fm
let term fm = print_term fm
let desc_constr fm = pp_print_string fm -| string_of_constr

include Print_

let program = list (id * (list id * term))

module T = Print_typ
