open Util

let input = ref ""
let silent = ref false
let exp = ref false

type solver = HoIce | Z3
let solver = ref HoIce

module Debug = struct
  let check_fun_arg_typ = false
  let check_typ = false
  let check_tmodule = ref false
  let debuggable_modules : string list ref = ref []
  let debug_module : string list ref = ref []
  let abst = ref false
  let input_cex = ref false
  let minimize = ref false

  let print_ref_typ () = List.mem "Ref_type" !debug_module
  let make_check s =
    let s' = String.remove_prefix_if_any ~prefix:"Dune__exe__" s in
    debuggable_modules := s'::!debuggable_modules;
    fun () -> !debug_module = ["ALL"] || List.mem s' !debug_module
  let set_debug_modules mods =
    let modules = String.split_on_string ~by:"," mods in
    let check m =
      if not @@ List.mem m !debuggable_modules then
        failwith {|Module "%s" is not registered for debug@.|} m
    in
    List.iter check modules;
    debug_module := modules @ !debug_module
  let print f =
    if !debug_module <> [] then Format.printf f else Format.iprintf f
end
