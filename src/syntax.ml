open Util
open Type_util

type binop = Eq | Lt | Gt | Leq | Geq | And | Or | Imply | Add | Sub | Mult | Div

and typ = Type.t
and id = typ Id.t

and const = (* only base type constants *)
  | Unit
  | True
  | False
  | Int of int
  | Rand of typ
  | Fail of Type.base
  | BinOp of binop
  | Not

and term =
  {desc : desc;
   typ : typ;
   attr : attr list}

and attr = unit

and desc =
  | Const of const
  | Var of id
  | Fun of id * term
  | App of term * term list
  | If of term * term * term
  | Let of (id * term) list * term
  | Fix of id * term

and rec_flag = Nonrecursive | Recursive

and program = (id * (id list * term)) list
[@@deriving show {with_path = false}]

let typ t = t.typ
let desc t = t.desc
let attr t = t.attr

let _Const c = Const c
let _Var x = Var x
let _Fun x t = Fun(x, t)
let _App t ts = App(t, ts)
let _If t1 t2 t3 = If(t1, t2, t3)
let _Let defs t = Let(defs, t)

module Val = struct
  let _Const = function {desc=Const c} -> Some c | _ -> None
  let _Var = function {desc=Var x} -> Some x | _ -> None
  let _Fun = function {desc=Fun(x, t)} -> Some(x, t) | _ -> None
  let _App = function {desc=App(t, ts)} -> Some(t, ts) | _ -> None
  let _If = function {desc=If(t1, t2, t3)} -> Some(t1, t2, t3) | _ -> None
end

module ValE = struct
  let _Const    = function {desc=Const c} -> c                       | _ -> invalid_arg "%s" __FUNCTION__
  let _Var      = function {desc=Var x} -> x                         | _ -> invalid_arg "%s" __FUNCTION__
  let _Fun      = function {desc=Fun(x, t)} -> (x, t)                | _ -> invalid_arg "%s" __FUNCTION__
  let _App      = function {desc=App(t, ts)} -> (t, ts)              | _ -> invalid_arg "%s" __FUNCTION__
  let _If       = function {desc=If(t1, t2, t3)} -> (t1, t2, t3)     | _ -> invalid_arg "%s" __FUNCTION__
end

module Is = struct
  let _Const = function {desc=Const _} -> true | _ -> false
  let _Var   = function {desc=Var _} -> true   | _ -> false
  let _Fun   = function {desc=Fun _} -> true   | _ -> false
  let _App   = function {desc=App _} -> true   | _ -> false
  let _If    = function {desc=If _} -> true    | _ -> false
end

let dummy_var = Id.new_var ~name:"_DUMMY_" Ty.unit

let make ?(attr=[]) desc typ =
  {desc; typ; attr}

let rec decomp_funs t =
  match Val._Fun t with
  | None -> [], t
  | Some(x,t') ->
      let xs,t'' = decomp_funs t' in
      x::xs, t''

module ID = struct
  type t = id
  let compare = Id.compare
end

module IdSet = Set.Make(ID)
