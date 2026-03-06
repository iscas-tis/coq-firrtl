open Hifirrtl_lang
open Extraction.Ssrnat
open Extraction.Eqtype

module StringMap = Map.Make(String)

let rec type_of_hfexpr e tmap =
  match e with
  | Ast.Econst (t0, _) -> Some t0
  | Ecast (u, e1) ->
    (match u with
     | AsClock ->
       (match type_of_hfexpr e1 tmap with
        | Some _ -> Some Fclock
        | None -> None)
     | AsAsync ->
       (match type_of_hfexpr e1 tmap with
        | Some _ -> Some Fasyncreset
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> Some (Fsint w)
           | Fsint w -> Some (Fsint w)
           | _ -> Some (Fsint (Stdlib.Int.succ 0)))
        | None -> None))
  | Eprim_unop (e0, e1) ->
    (match e0 with
     | Upad n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> Some (Fuint (maxn w n))
           | Fsint w -> Some (Fsint (maxn w n))
           | _ -> None)
        | None -> None)
     | Ushl n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> Some (Fuint (addn w n))
           | Fsint w -> Some (Fsint (addn w n))
           | _ -> None)
        | None -> None)
     | Ushr n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> Some (Fuint (maxn (subn w n) 0))
           | Fsint w -> Some (Fsint (maxn (subn w n) (Stdlib.Int.succ 0)))
           | _ -> None)
        | None -> None)
     | Ucvt ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> Some (Fsint (addn w (Stdlib.Int.succ 0)))
           | Fsint w -> Some (Fsint w)
           | _ -> None)
        | None -> None)
     | Uneg ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> Some (Fsint (addn w (Stdlib.Int.succ 0)))
           | Fsint w -> Some (Fsint (addn w (Stdlib.Int.succ 0)))
           | _ -> None)
        | None -> None)
     | Unot ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> Some (Fuint w)
           | Fsint w -> Some (Fuint w)
           | _ -> None)
        | None -> None)
     | Uextr (n1, n2) ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w ->
             if (&&) (leq n2 n1) (leq (Stdlib.Int.succ n1) w)
             then Some (Fuint (addn (subn n1 n2) (Stdlib.Int.succ 0)))
             else None
           | Fsint w ->
             if (&&) (leq n2 n1) (leq (Stdlib.Int.succ n1) w)
             then Some (Fuint (addn (subn n1 n2) (Stdlib.Int.succ 0)))
             else None
           | _ -> None)
        | None -> None)
     | Uhead n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> if leq n w then Some (Fuint n) else None
           | Fsint w -> if leq n w then Some (Fuint n) else None
           | _ -> None)
        | None -> None)
     | Utail n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w -> if leq n w then Some (Fuint (subn w n)) else None
           | Fsint w -> if leq n w then Some (Fuint (subn w n)) else None
           | _ -> None)
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint _ -> Some (Fuint (Stdlib.Int.succ 0))
           | Fsint _ -> Some (Fuint (Stdlib.Int.succ 0))
           | _ -> None)
        | None -> None))
  | Eprim_binop (e0, e1, e2) ->
    (match e0 with
     | Badd ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint w2 ->
                   Some (Fuint (addn (maxn w1 w2) (Stdlib.Int.succ 0)))
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fsint w2 ->
                   Some (Fsint (addn (maxn w1 w2) (Stdlib.Int.succ 0)))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | Bsub ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint w2 ->
                   Some (Fuint (addn (maxn w1 w2) (Stdlib.Int.succ 0)))
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fsint w2 ->
                   Some (Fsint (addn (maxn w1 w2) (Stdlib.Int.succ 0)))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | Bmul ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint w2 -> Some (Fuint (addn w1 w2))
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fsint w2 -> Some (Fsint (addn w1 w2))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | Bdiv ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint _ -> Some (Fuint w1)
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fsint _ -> Some (Fsint (addn w1 (Stdlib.Int.succ 0)))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | Brem ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint w2 -> Some (Fuint (minn w1 w2))
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fsint w2 -> Some (Fsint (minn w1 w2))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | Bcomp _ ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint _ ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint _ -> Some (Fuint (Stdlib.Int.succ 0))
                 | _ -> None)
              | None -> None)
           | Fsint _ ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fsint _ -> Some (Fuint (Stdlib.Int.succ 0))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | Bdshl ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint w2 ->
                   Some (Fuint
                     (subn
                       (addn
                         (expn (Stdlib.Int.succ (Stdlib.Int.succ 0)) w2) w1)
                       (Stdlib.Int.succ 0)))
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint w2 ->
                   Some (Fsint
                     (subn
                       (addn
                         (expn (Stdlib.Int.succ (Stdlib.Int.succ 0)) w2) w1)
                       (Stdlib.Int.succ 0)))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | Bdshr ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint _ -> Some (Fuint w1)
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint _ -> Some (Fsint w1)
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | Bcat ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint w2 -> Some (Fuint (addn w1 w2))
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fsint w2 -> Some (Fuint (addn w1 w2))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Fuint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fuint w2 -> Some (Fuint (maxn w1 w2))
                 | _ -> None)
              | None -> None)
           | Fsint w1 ->
             (match type_of_hfexpr e2 tmap with
              | Some f0 ->
                (match f0 with
                 | Fsint w2 -> Some (Fuint (maxn w1 w2))
                 | _ -> None)
              | None -> None)
           | _ -> None)
        | None -> None))
  | Emux (c, e1, e2) ->
    (match type_of_hfexpr c tmap with
     | Some f ->
       (match f with
        | Fuint _ ->
          (match type_of_hfexpr e1 tmap with
           | Some f0 ->
             (match f0 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f1 ->
                   (match f1 with
                    | Fuint w2 -> Some (Fuint (maxn w1 w2))
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f1 ->
                   (match f1 with
                    | Fsint w2 -> Some (Fsint (maxn w1 w2))
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | None -> None)
        | _ -> None)
     | None -> None)
  | Eref h ->
    (match h with
     | Eid v -> Some (StringMap.find v tmap)
     | _ -> None)