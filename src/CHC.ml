open Util
open Type
open Syntax
open Type_util
open Term_util

(*
type head = HAtom of term | HApp of app
and app = id * term list
and clause =
  {head : head;
   apps : app list;
   cond : term}
 *)
type result = Sat | Unsat | Unknown

let print_typ fm ty =
  match ty with
  | TBase TUnit -> Format.fprintf fm "Int"
  | TBase TInt -> Format.fprintf fm "Int"
  | TBase TBool -> Format.fprintf fm "Bool"
  | _ ->
      Format.printf "ERROR: %a@." Print.typ ty;
      unsupported "%s" __FUNCTION__

let rec print_term_as_sexp fm t =
  let print_list fm ts = print_list ~bopen:(Format.pp_open_hvbox -$- 0) print_term_as_sexp "@ " fm ts in
  match t.desc with
  | Const Unit -> Format.fprintf fm "0"
  | Const True -> Format.fprintf fm "true"
  | Const False -> Format.fprintf fm "false"
  | Const (Int n) when n < 0 -> Format.fprintf fm "(- %d)" n
  | Const (Int n) -> Format.fprintf fm "%d" n
  | Const (BinOp Eq) -> Format.fprintf fm "="
  | Const (BinOp Lt) -> Format.fprintf fm "<"
  | Const (BinOp Gt) -> Format.fprintf fm ">"
  | Const (BinOp Leq) -> Format.fprintf fm "<="
  | Const (BinOp Geq) -> Format.fprintf fm ">="
  | Const (BinOp And) -> Format.fprintf fm "and"
  | Const (BinOp Or) -> Format.fprintf fm "or"
  | Const (BinOp Imply) -> Format.fprintf fm "=>"
  | Const (BinOp Add) -> Format.fprintf fm "+"
  | Const (BinOp Sub) -> Format.fprintf fm "-"
  | Const (BinOp Mult) -> Format.fprintf fm "*"
  | Const (BinOp Div) -> Format.fprintf fm "/"
  | Const Not -> Format.fprintf fm "not"
  | Var x -> Print.id fm x
  | App({desc = Const (BinOp And)}, _) ->
      let ts = decomp_ands t in
      Format.fprintf fm "@[(and %a)@]" print_list ts
  | App(t1, ts) -> Format.fprintf fm "@[(%a %a)@]" print_term_as_sexp t1 print_list ts
  | _ ->
      Format.printf "ERROR: %a@." Print.term t;
      unsupported "%s" __FUNCTION__

let print_header fm =
  Format.fprintf fm "(set-logic HORN)@\n"

let print_declare fm p =
  let tys,ty = decomp_tfuns @@ Id.typ p in
  Format.fprintf fm "(declare-fun %a (%a) %a)@\n" Print.id p (print_list print_typ "@ ") tys print_typ ty

let print_as_assert fm t =
  let xs = get_fv t |> List.filter_out Id.is_predicate in
  let pr fm x = Format.fprintf fm "(%a %a)" Print.id x print_typ (Id.typ x) in
  if xs = [] && !Flag.solver <> HoIce then
    Format.fprintf fm "(@[assert @[%a@]@])@\n" print_term_as_sexp t
  else
    Format.fprintf fm "(@[assert (@[<hov 2>forall (%a)@ @[%a@]@])@])@\n" (print_list pr "@ ") xs print_term_as_sexp t

let print_footer fm =
  Format.fprintf fm "(check-sat)@\n";
  if false then Format.fprintf fm "(get-model)@\n";
  Format.fprintf fm "(exit)@\n"

let print_as_smt2 fm ts =
  let ps =
    ts
    |> List.flatten_map get_fv
    |> Id.List.unique
    |> List.filter Id.is_predicate
  in
  print_header fm;
  List.iter (print_declare fm) ps;
  List.iter (print_as_assert fm) ts;
  print_footer fm

let rec flatten t =
  match t.desc with
  | App({desc = Const (BinOp Imply)}, [t1; t2]) ->
      t2
      |> flatten
      |> List.map (fun (t21, t22) -> t1::t21, t22)
  | _ ->
      t
      |> decomp_ands
      |> List.map (Pair.pair [])
let flatten t =
  t
  |> flatten
  |> List.map (fun (ts,t) -> Term.(ands ts => t))

let solve ts : result =
  let ts = List.rev_map_flatten flatten ts in
  let file = Filename.change_extension !Flag.input "smt2" in
  if not !Flag.silent then Format.printf "Output to %s@." file;
  IO.CPS.open_out file (fun cout ->
      let fm = Format.formatter_of_out_channel cout in
      Format.pp_set_margin fm 120;
      Format.fprintf fm "%a@." print_as_smt2 ts);
  let cmd =
    let solver =
      match !Flag.solver with
      | HoIce -> "hoice"
      | Z3 -> "z3"
    in
    Format.sprintf "%s %s" solver file
  in
  match
    Unix.CPS.open_process_in cmd IO.input_all
    |> String.split ~by:"\n"
  with
  | "sat", _ -> Sat
  | "unsat", _ -> Unsat
  | "unknown", _ -> Unknown
  | _ -> Unknown
