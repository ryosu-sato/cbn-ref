open! Util
open Type

let rec decomp_tfuns typ =
  match typ with
  | TFun(x,typ) ->
      let xs,typ = decomp_tfuns typ in
      x :: xs, typ
  | _ -> [], typ

let new_var ?(name="x") typ =
  Id.new_var ~name typ

let make_tfun typ1 typ2 = TFun(typ1, typ2)

module Ty = struct
  let unit = TBase TUnit
  let bool = TBase TBool
  let int = TBase TInt
  let fun_ = make_tfun
end
