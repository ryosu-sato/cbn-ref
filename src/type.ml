open Util

type base =
  | TUnit
  | TBool
  | TInt

and t =
  | TBase of base
  | TVar of t option ref
  | TFun of t * t
[@@deriving show {with_path = false}]

let _TBase b = TBase b
let _TVar r = TVar r
let _TFun(ty1,ty2) = TFun(ty1, ty2)

module Val = struct
  let _TBase    = function TBase b    -> Some b       | _ -> None
  let _TVar     = function TVar r     -> Some r       | _ -> None
  let _TFun     = function TFun(x,ty) -> Some (x, ty) | _ -> None
end

module ValE = struct
  let _TBase    = function TBase b    -> b     | _ -> invalid_arg "%s" __FUNCTION__
  let _TVar     = function TVar r     -> r     | _ -> invalid_arg "%s" __FUNCTION__
  let _TFun     = function TFun(x,ty) -> x, ty | _ -> invalid_arg "%s" __FUNCTION__
end

module Is = struct
  let _TBase    = function TBase _    -> true | _ -> false
  let _TVar     = function TVar _     -> true | _ -> false
  let _TFun     = function TFun _     -> true | _ -> false
end
