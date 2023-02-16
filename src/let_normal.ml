open Util
open Syntax
open Term_util

let rec normalize_top t =
  let defs,t' = normalize_term t in
  Term.let_ defs t'
and normalize_term t =
  let normalize_to_var t =
    let defs,t' = normalize_term t in
    match t'.desc with
    | Var x -> defs, x
    | _ ->
        let x = Id.new_var t'.typ in
        defs @ [x,t'], x
  in
  match t.desc with
  | Const _ ->
      let x = Id.new_var t.typ in
      [x, t], Term.var x
  | Var _ -> [], t
  | Fun _ -> unsupported "%s" __FUNCTION__
  | App(t1,ts) ->
      let defs1,f = normalize_to_var t1 in
      let defss,xs = List.split_map normalize_to_var ts in
      let defs2,r =
        List.L.fold_left xs ~init:([],f) ~f:(fun (defs,f) x ->
            let t = Term.(var f @ [var x]) in
            let r = Id.new_var ~name:"r" t.typ in
            defs@[r,t], r)
      in
      defs1 @ List.flatten defss @ defs2, Term.var r
  | If(t1,t2,t3) ->
      let defs,x = normalize_to_var t1 in
      let t2' = normalize_top t2 in
      let t3' = normalize_top t3 in
      defs, Term.(if_ (var x) t2' t3')
  | Let(defs, t1) ->
      let defs' =
        List.L.flatten_map defs ~f:(fun (x,t) ->
            let defs,t' = normalize_term t in
            defs @ [x,t'])
      in
      let defs1,t1' = normalize_term t1 in
      defs'@defs1, t1'
  | Fix _ -> unsupported "%s" __FUNCTION__

let rec eta_expand t =
  match t.typ with
  | TVar _ -> assert false
  | TBase _ -> [], t
  | TFun(ty, _) ->
      let x = Id.new_var ty in
      let xs,t' = eta_expand Term.(t @ [var x]) in
      x::xs, t'

let inline_let_var =
  make_trans (fun tr t ->
      match t.desc with
      | Let(defs, t1) ->
          begin
            match List.partition (snd |- Is._Var) defs with
            | [], _ -> None
            | map, defs' ->
                let desc = Let(defs', tr t1) in
                {t with desc}
                |> List.fold_right (Fun.uncurry subst) map
                |> Option.some
          end
      | _ -> None)


let normalize p =
  List.L.map p ~f:(fun (f,(xs,t)) ->
      let ys,t = eta_expand t in
      let xs = xs @ ys in
      f, (xs, inline_let_var @@ normalize_top t))
