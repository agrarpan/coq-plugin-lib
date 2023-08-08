(*
 * Utilities for constants
 *)

open Constr
open Names

(* --- Constructing constants --- *)

(* Define a constant from an ID in the current path *)
let make_constant id =
  mkConst (Constant.make1 (Lib.make_kn id))

(* --- Opening constants --- *)

(* 
 * Safely extract the body of a constant, instantiating any universe variables 
 *)
let open_constant env const =
  let (term, auctx) = Option.get @@ Global.body_of_constant const in
  let instance, (_, constr) = UnivGen.fresh_instance auctx in
  let uctx = Univ.UContext.make (instance, constr) in
  let term = Vars.subst_instance_constr (Univ.UContext.instance uctx) term in
  let env = Environ.push_context uctx env in
  env, term
