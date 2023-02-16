open Util
open Type
open! Type_util
open Syntax
open Term_util

module S = Strictness
module R = Ref_type

module Dbg = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type env = (id * (bool * R.t)) list

let (++) p1 p2 =
  if p2 = false_term then
    false_term
  else
    Term.(p1 && p2)
let (=>) b c = if b then c else Term.tt
let rec (&&) (ty:R.t) p : R.t =
  match ty with
  | TBase(c, b, x, p') -> TBase(c, b, x, Term.(p' && p))
  | TFun(x, ty1, b, ty2) -> TFun(x, ty1, b, ty2 && p)

let print_bind fm (x,(b,ty)) =
    if Id.(x = dummy_var) then
      match ty with
      | R.TBase(_, _, _, c) -> Format.fprintf fm "%a" Print.term c
      | _ -> assert false
    else
      let col = if b then "::" else ":" in
      Format.fprintf fm "%a %s %a" Print.id x col R.print ty
let print_env fm env =
  Format.fprintf fm "[%a]" (print_list ~bopen:(Format.pp_open_hvbox -$- 0) print_bind ";@ ") env

let rec decomp_let (r:S.result) t =
  match t.desc with
  | Let((x,t1)::defs, t2) ->
      let b = r.sol (r.label_of x) in
      Some (x, b, t1), {t with desc = Let(defs, t2)}
  | Let([], t2) -> decomp_let r t2
  | _ -> None, t

let add_cond cond (env:env) =
  (dummy_var, (true, R.TBase(Term.tt, TUnit, dummy_var, cond)))::env

let cond (env:env) =
  List.L.fold_left env
    ~init:Term.tt
    ~f:(fun acc (x,(_,ty)) ->
      match Id.(x = dummy_var), ty with
      | true, R.TBase(_,_,_,p) -> acc ++ p
      | _ -> acc)

let scond (env:env) =
  List.L.fold_left env
    ~init:Term.tt
    ~f:(fun acc (x,(b,ty)) ->
      match Id.(x = dummy_var), b, ty with
      | true, _, R.TBase(_,_,_,p) -> acc ++ p
      | _, true, R.TBase(p1,_,y,p2) -> acc ++ Term.(p1 => subst_var y x p2)
      | _ -> acc)

let gen_pred env p =
  let asm =
    List.L.fold_left env
      ~init:Term.tt
      ~f:(fun acc (x,(_,ty)) ->
        match Id.(x = dummy_var), ty with
        | true, R.TBase(_,_,_,p) -> acc ++ p
        | _ -> acc)
    |> decomp_ands
    |> List.unique
    |> Term.ands
  in
  let r = Term.(asm => p) in
  Dbg.printf "      gen_pred [... |- %a]:  %a@.@." Print.term p Print.term r;
  r

let rec gen_sub env (ty1:R.t) (ty2:R.t) =
  let r =
    match ty1, ty2 with
    | TBase(c1,b1,x1,p1), TBase(c2,b2,x2,p2) ->
        let p2' = subst_var x2 x1 p2 in
        assert (b1 = b2);
        let env1 = add_cond (cond env ++ c2) env in
        let env2 = add_cond p1 env1 in
        Dbg.printf "      gen_sub env: @[%a@." print_env env;
        Dbg.printf "      gen_sub (cond env): @[%a@." Print.term (cond env);
        Dbg.printf "      gen_sub c2: @[%a@." Print.term c2;
        Dbg.printf "      gen_sub env1: @[%a@." print_env env1;
        let r1 = gen_pred env1 c1 in
        Dbg.printf "      gen_sub env2: @[%a@.@." print_env env2;
        let r2 = gen_pred env2 p2' in
        r1 ++ r2
    | TFun(x1,ty11,b1,ty12), TFun(x2,ty21,_,ty22) ->
        let ty22' = R.subst_var x2 x1 ty22 in
        let env' = (x1, (b1, ty11))::env in
        gen_sub env ty21 ty11 ++ gen_sub env' ty12 ty22'
    | _ -> assert false
  in
  Dbg.printf "    @[gen_sub [@[%a <:@ %a@]]:@\n  %a@.@." R.print ty1 R.print ty2 Print.term r;
  r

let base_fv_of env =
  env
  |> List.filter (snd |- snd |- R.Is._TBase)
  |> List.map fst
  |> Id.List.remove_all -$- dummy_var

let floor_env env = Fmap.(list (snd (fst (const false)))) env

let rec gen_term (r:S.result) (env:env) t (ty:R.t) =
  let gen = gen_term r in
  match decomp_let r t with
  | None, {desc = Var x} ->
      Dbg.printf "  @[<2>gen_term[%a]: VAR %a@." R.print ty Print.id x;
      let _,x_ty = List.assoc x env in
      gen_sub env x_ty ty
  | Some (x, _, {desc = Const c}), t1 ->
      Dbg.printf "  @[<2>gen_term[%a, %a]: Const %a@." R.print ty Print.id x Print.const c;
      let c_ty = R.type_of_const c in
      let bind = (x, (true, c_ty)) in
      let env' = bind::env in
      Dbg.printf "  @[<2>BIND %a@.@." print_bind bind;
      gen env' t1 ty
  | Some (x, b, {desc = App({desc = Var y}, [{desc = Var z}])}), t1 ->
      Dbg.printf "  @[<2>gen_term[%a, %a]: App %a %a@." R.print ty Print.id x Print.id y Print.id z;
      let ty1,b',ty2 =
        match List.assoc y env with
        | _, TFun(w, ty1, b, ty2) -> ty1, b, R.subst_var w z ty2
        | _, ty ->
            Format.printf "env: %a@." print_env env;
            Format.printf "y: %a@." Print.id y;
            Format.printf "ty: %a@." R.print ty;
            assert false
      in
      let _,z_ty = List.assoc z env in
      let c1 = gen_sub env z_ty ty1 in
      let z_pre, z_post =
        match Id.List.assoc z env with
        | true, R.TBase(p1,_,y,p2) -> p1, subst_var y z p2
        | _ -> Term.tt, Term.tt
      in
      let c3 = gen_pred env z_pre in
      let bind = x, (b, ty2 && z_post) in
      Dbg.printf "  @[<2>BIND %a@.@." print_bind bind;
      let env' = add_cond (b' => z_post) (bind::env) in
      let c2 = gen env' t1 ty in
      c1 ++ c2 ++ c3
  | None, {desc = If({desc = Var x}, t2, t3)} ->
      Dbg.printf "  @[<2>gen_term[%a]: If %a@." R.print ty Print.id x;
      let b,ty_x = Id.List.assoc x env in
      assert b;
      let c_x = scond [x, (b, ty_x)] in
      Dbg.printf "c_x: %a@." Print.term c_x;
      let env' = add_cond c_x env in
      let c1 = gen_sub env ty_x (R.simple_base TBool) in
      let c2 = gen (add_cond Term.(var x) env') t2 ty in
      let c3 = gen (add_cond Term.(not (var x)) env') t3 ty in
      c1 ++ c2 ++ c3
  | _ ->
      Format.eprintf "t: %a@." Print.term t;
      unsupported "%s" __FUNCTION__


let make_target (env:env) f =
  let _,ty = List.assoc f env in
  let ty' = R.simple_ref ty in
  gen_sub env ty ty'

let gen (r:S.result) (p:program) =
  let env0 : env =
    p
    |> List.map (fun (f,_) ->
           let f_ty = R.make_template r.sol [] @@ r.typ_of f in
           f, (true, f_ty))
  in
  Dbg.printf "env0: @[%a@]@.@." print_env env0;
  let aux (f,(xs,t)) =
    let _,f_ty = Id.List.assoc f env0 in
    let rec add_arg_to_env fv args ty env =
      match args, ty with
      | [], R.TBase(p1, base, x, p2) ->
          add_cond p1 env, R.TBase(Term.tt, base, x, p2)
      | x::args', TFun(y,ty1,b,ty2) ->
          let ty2' = R.subst_var y x ty2 in
          let ty1' =
            match ty1 with
            | TBase(c, b, x', t) -> R.TBase(c, b, x', Term.(t && var x' = var x))
            | _ -> ty1
          in
          let env' = (x, (b, ty1')) :: env in
          add_arg_to_env (x::fv) args' ty2' env'
      | _ -> assert false
    in
    let env,ty = add_arg_to_env [] xs f_ty env0 in
    Dbg.printf "GEN_TERM[%a]: @[@[%a@." R.print ty Print.term t;
    Dbg.printf "  env: %a@." print_env env;
    gen_term r env t ty
    |@> Dbg.printf "CONSTRAINT[%a]: %a@." Print.id f Print.term
  in
  let target = make_target env0 (fst @@ List.last p) in
  Dbg.printf "CONSTRAINT[target]: %a@." Print.term target;
  target :: List.map aux p
