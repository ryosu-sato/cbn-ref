open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let decomp_funs p =
  List.map (Pair.map_snd Syntax.decomp_funs) p

let has_option s = Array.exists ((=) s) Sys.argv

let () = Flag.Debug.debug_module := try String.split_on_char ',' @@ Sys.getenv "DEBUG" with _ -> []
let () = Format.set_margin 120
let () = Flag.silent := Sys.getenv_opt "S" <> None || has_option "-s" || has_option "-exp"
let () =
  Flag.solver :=
    if has_option "-hoice" then
      HoIce
    else if has_option "-z3" then
      Z3
    else
      match Sys.getenv_opt "SOLVER" with
      | None -> HoIce
      | Some s when String.lowercase s = "hoice" -> HoIce
      | Some s when String.lowercase s = "z3" -> Z3
      | Some s -> failwith "Unknown solver %s" s
let () = Flag.exp := has_option "-exp"

let count_size r p =
  r := Term_util.size_of_program p

let main () =
  Flag.input := Sys.argv.(1);
  let size = ref 0 in
  let program =
    !Flag.input
    |> Parser_wrapper.parse_file
    |@not!Flag.silent&> Format.printf "INPUT: %a@." Print.(list (id * term))
    |> Fmap.(list (snd Term_util.alpha_rename))
    |> decomp_funs
    |@> count_size size
    |> Let_normal.normalize
    |@not!Flag.silent&> Format.printf "NORMALIZE: %a@." Print.program
  in
  let r = Strictness.infer program in
  let constraints = VC.gen r program in
  if !Flag.exp then Format.printf "%d, " !size;
  match CHC.solve constraints with
  | Sat -> Format.printf "Safe@."
  | _ -> Format.printf "Unknown@."

let () =
  if !Sys.interactive then
    ()
  else
    main ()
