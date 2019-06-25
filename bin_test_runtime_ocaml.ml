
(* 
 * Here we test the time bounds we claim in Section 6. 
 *
 * First, (lines 13 - 329), we show the result of extracting
 * our code to OCaml using Coq's built-in extraction mechanism.
 * 
 * Next, (lines 332 - 358), we run a few simple benchmarks on
 * that code. 
 *)


(** Extracted Code **)

type bool =
| True
| False

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

(** val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let compose g f x =
  g (f x)

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q -> XI (add p q)
               | XO q -> XO (add p q)
               | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH -> (match y with
             | XI q -> XI (succ q)
             | XO q -> XO (succ q)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module N =
 struct
  (** val succ : n -> n **)

  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Coq_Pos.succ p)

  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val pow : n -> n -> n **)

  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 -> (match n0 with
                | N0 -> N0
                | Npos q -> Npos (Coq_Pos.pow q p0))

  (** val log2 : n -> n **)

  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
     | XH -> N0)
 end

(** val nat_size : n -> nat **)

let nat_size = function
| N0 -> O
| Npos p ->
  let rec nat_pos_size = function
  | XI y -> S (nat_pos_size y)
  | XO y -> S (nat_pos_size y)
  | XH -> S O
  in nat_pos_size p

(** val bin_cdn_wkr : (n -> n) -> n -> n -> nat -> n **)

let rec bin_cdn_wkr f a n0 = function
| O -> N0
| S b' ->
  (match N.leb n0 a with
   | True -> N0
   | False -> N.add (Npos XH) (bin_cdn_wkr f a (f n0) b'))

(** val bin_countdown_to : (n -> n) -> n -> n -> n **)

let bin_countdown_to f a n0 =
  bin_cdn_wkr f a n0 (nat_size (N.sub n0 a))

(** val bin_inv_ack_wkr : (n -> n) -> n -> n -> nat -> n **)

let rec bin_inv_ack_wkr f n0 k = function
| O -> k
| S b' ->
  (match N.leb n0 k with
   | True -> k
   | False ->
     let g = bin_countdown_to f (Npos XH) in
     bin_inv_ack_wkr (compose g f) (g n0) (N.succ k) b')

(** val bin_inv_ack : n -> n **)

let bin_inv_ack n0 =
  match N.leb n0 (Npos XH) with
  | True -> N0
  | False ->
    (match N.leb n0 (Npos (XI XH)) with
     | True -> Npos XH
     | False ->
       (match N.leb n0 (Npos (XI (XI XH))) with
        | True -> Npos (XO XH)
        | False ->
          let f = fun x -> N.sub (N.log2 (N.add x (Npos (XO XH)))) (Npos (XO XH)) in
          bin_inv_ack_wkr f (f n0) (Npos (XI XH)) (nat_size n0)))


(** Testing **)

(* 65536 *)
let bignum1 =
  N.pow (Npos (XO XH)) (N.pow (Npos (XO XH)) (N.pow (Npos (XO XH)) (Npos (XO XH))))

(* 4.3 x 10^9 *)
let bignum2 =
  N.pow bignum1 (Npos (XO XH))

(* 2.0 x 10^19728 *)
let bignum3 =
  N.pow (Npos (XO XH)) bignum1

(* 4.0x 10^39456 *)  
let bignum4 =
  N.pow bignum3 (Npos (XO XH))

let time n f x =
    let t = Sys.time() in
    let ans = f x in
    Printf.printf "Execution time for %s: \t%fs\n" n (Sys.time() -. t); ans;;

print_string "\nFor values encoded in binary: \n";;
time "65536" bin_inv_ack bignum1;;
time "4.3x10^9" bin_inv_ack bignum2;;
time "2x10^19728" bin_inv_ack bignum3;;
time "4x10^39456" bin_inv_ack bignum4;;