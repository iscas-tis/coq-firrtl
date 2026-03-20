open Hifirrtl_lang
(* reflect a pair of natural number to its string name, accorfing to its type. *)

let rec size_of_ftype = function
| Ast.Gtyp _ -> Stdlib.Int.succ 0
| Atyp (t0, n) -> (size_of_ftype t0) * n
| Btyp b -> size_of_fields b

and size_of_fields = function
| Fnil -> 0
| Fflips (_, _, t0, fs) -> (size_of_ftype t0) + (size_of_fields fs)

let rec store_pair v offset num ft map_p2s =
  match ft with
  | Ast.Gtyp _ -> Transhiast.IntPairMap.add (num, offset) v map_p2s
  | Atyp (atyp, n) ->
    let rec store_pair_array n0 offset' map_p2s' =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> map_p2s')
        (fun n' ->
        store_pair_array n' (offset' + (size_of_ftype atyp))
          (store_pair (v^"_"^(Stdlib.Int.to_string (n0-1-n'))) offset' num atyp map_p2s'))
        n0
    in store_pair_array n offset map_p2s
  | Btyp btyp -> store_pair_btyp v offset num btyp map_p2s

and store_pair_btyp v offset num btyp map_p2s =
  match btyp with
  | Fnil -> map_p2s
  | Fflips (fv, _, ft, ff) ->
    store_pair_btyp (v^"_"^fv) (offset + (size_of_ftype ft)) num ff
      (store_pair (v^"_"^fv) offset num ft map_p2s)
