open Util
open Type
open! Type_util
open Syntax
open Term_util

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let (++) = IntSet.union
let (+>) = IntSet.add

type ty =
  | TBase of base
  | TFun of ty * label * ty

and label = int
(* label 0 means strict *)
(* label -1 means non-strict *)

let strict_label = 0
let nonstrict_label = -1

type state =
  {mutable updated: bool;
   mutable unused: IntSet.t} (* the set of variables (labels) that may be unused *)

type env =
  {env: (key, label * ty) Hashtbl.t;
   mutable counter: int}
and key = string

let rec print_ty fm (ty:ty) =
  match ty with
  | TBase base -> Print_typ.base fm base
  | TFun(ty1, l, ty2) ->
      Format.fprintf fm "(%a [%d]-> %a)" print_ty ty1 l print_ty ty2

let rec print_ty_sol tbl fm (ty:ty) =
  let pr = print_ty_sol tbl in
  match ty with
  | TBase base -> Print_typ.base fm base
  | TFun(ty1, l, ty2) ->
      let ar = if IntSet.mem l tbl then "->" else "=>" in
      Format.fprintf fm "(%a %s %a)" pr ty1 ar pr ty2

let print_env_raw ?sol pr fm {env} =
  let pr (x,(l,ty)) =
    let s =
      match sol with
      | None -> string_of_int l
      | Some s when IntSet.mem l s -> "n"
      | _ -> "s"
    in
    Format.fprintf fm "%s :%s: %a@\n" x s pr ty
  in
  Format.fprintf fm "@[";
  List.iter pr @@ Hashtbl.to_list env;
  Format.fprintf fm "@]"

let print_env fm env = print_env_raw print_ty fm env
let print_env_sol sol fm env = print_env_raw ~sol (print_ty_sol sol) fm env

let create_env () =
  {env = Hashtbl.create 100;
   counter = 1}

let create_state () =
  {updated = false;
   unused = IntSet.singleton (-1)}

let clear st l =
  if not (IntSet.mem l st.unused) then
    begin
      Dbg.printf "clear %d@." l;
      st.updated <- true;
      st.unused <- l +> st.unused
    end

let new_label env =
  let l = env.counter in
  env.counter <- l + 1;
  l

let key_of x = Id.to_string x

let label_of {env} x =
  Hashtbl.find env (key_of x)
  |> fst

let rec to_simple (ty:ty) : typ =
  match ty with
  | TBase base -> TBase base
  | TFun(ty1,_,ty2) -> TFun(to_simple ty1, to_simple ty2)

let rec make_template ?(nl=new_label) env (ty:typ) : ty =
  match ty with
  | TBase base -> TBase base
  | TFun(ty1, ty2) ->
      let l = nl env in
      let ty1 = make_template env ty1 in
      let ty2 = make_template env ty2 in
      TFun(ty1, l, ty2)
  | _ -> unsupported "%s" __FUNCTION__

let type_of_strict_function = make_template ~nl:(fun _ -> strict_label)

let rec type_of env t =
  match t.desc with
  | Const c -> type_of_strict_function env (type_of_const c)
  | Var x -> snd (Hashtbl.find env.env (key_of x))
  | Fun _ -> invalid_arg "%s" __FUNCTION__
  | App(t1, ts) ->
      let rec app ty ts =
        match ty, ts with
        | _, [] -> ty
        | TFun(_,_,ty'), _::ts' -> app ty' ts'
        | _ -> assert false
      in
      app (type_of env t1) ts
  | If (_, t1, t2) ->
      let ty1 = type_of env t1 in
      let ty2 = type_of env t2 in
      (match ty1,ty2 with TBase _, TBase _ -> () | _ -> assert false); (* Assumption *)
      ty1
  | Let _ -> invalid_arg "%s" __FUNCTION__
  | Fix _ -> invalid_arg "%s" __FUNCTION__

let labels_of_arg env t n =
  let ty = type_of env t in
  let rec aux acc_rev n ty =
    if n = 0 then
      List.rev acc_rev
    else
      match ty with
      | TFun(_,l,ty') -> aux (l::acc_rev) (n-1) ty'
      | _ -> invalid_arg "%s" __FUNCTION__
  in
  aux [] n ty

(* returns a function that
   takes an interpretation of label
   and returns a set of labels that correspond used variables *)
let rec need env t =
  match t.desc with
  | Const _ -> fun _ -> IntSet.empty
  | Var x -> fun _ -> IntSet.singleton (label_of env x)
  | App(t1, ts) ->
      let s1 = need env t1 in
      let ss = List.map (need env) ts in
      let ls = labels_of_arg env t1 (List.length ts) in
      fun st -> List.fold_left2 (fun acc s l -> if IntSet.mem l st.unused then acc else s st ++ acc) (s1 st) ss ls
  | If(t1, t2, t3) ->
      let s1 = need env t1 in
      let s2 = need env t2 in
      let s3 = need env t3 in
      fun st -> IntSet.(union (s1 st) (inter (s2 st) (s3 st)))
  | Let(defs, t1) ->
      let add (x,t) =
        let l = new_label env in
        let ty = type_of env t in
        Hashtbl.add env.env (key_of x) (l, ty)
      in
      List.iter add defs;
      let ss = List.map (snd |- need env) defs in
      let s1 = need env t1 in
      fun st -> List.fold_left (fun acc s -> s st ++ acc) (s1 st) ss
  | _ ->
      Format.eprintf "t: %a@." Print.term t;
      unsupported "%s" __FUNCTION__

let rec add_fun_arg ty xs env =
  match ty, xs with
  | TBase _, [] -> ()
  | TFun(ty1,l,ty2), x::xs' ->
      Hashtbl.add env (key_of x) (l,ty1);
      add_fun_arg ty2 xs' env
  | _ -> invalid_arg "%s" __FUNCTION__

let gen_prog env (prog:program) =
  let add (f,_) =
    let ty = make_template env @@ Id.typ f in
    Hashtbl.add env.env (key_of f) (strict_label, ty)
  in
  List.iter add prog;
  let gen_aux acc (f, (xs, t)) =
    add_fun_arg (snd (Hashtbl.find env.env (key_of f))) xs env.env;
    let needs = need env t in
    let xs_set = List.fold_left (fun acc x -> label_of env x +> acc) IntSet.empty xs in
    let update st =
      st
      |> needs
      |@> (fun _ -> Dbg.printf "t: %a@." Print.term t)
      |@> (fun s -> Dbg.printf "needs: %a@.@." Print.(list int) (IntSet.elements s))
      |> IntSet.diff xs_set
      |> IntSet.iter (clear st)
    in
    fun st -> acc st; update st
  in
  List.fold_left gen_aux ignore prog

type result =
  {typ_of : id -> ty;
   label_of : id -> label;
   sol : label -> bool}

(* assumed that all the varibalse are unique *)
let infer (prog:program) : result =
  let state = create_state () in
  let env = create_env () in
  let update = gen_prog env prog in
  Dbg.printf "ENV: %a@." print_env env;
  state.updated <- true;
  while state.updated do
    Dbg.printf "LOOP@.";
    state.updated <- false;
    update state;
  done;
  Dbg.printf "ENV: @[%a@." (print_env_sol state.unused) env;
  let typ_of x = snd @@ Hashtbl.find env.env (key_of x) in
  let label_of = label_of env in
  let sol l = not (IntSet.mem l state.unused) in
  {typ_of; label_of; sol}
