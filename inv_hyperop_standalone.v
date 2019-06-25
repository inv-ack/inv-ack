Require Import Omega.


(* ***** UNARY ***** *)

(* Countdown worker function *)
Fixpoint cdn_wkr (f : nat -> nat) (a n k : nat) : nat :=
  match k with
  | 0    => 0
  | S k' => if (n <=? a) then 0 else
              S (cdn_wkr f a (f n) k')
  end.

(* Countdown *)
Definition countdown_to f a n := cdn_wkr f a n n.

(* A function to summarize the initial values of the hyperoperations *)
Definition hyperop_init (a n : nat) : nat :=
  match n with 0 => a | 1 => 0 | _ => 1 end.

(* The inverse hyperop hierarchy *)
Fixpoint inv_hyperop a n b :=
  match n with
  | 0 => b - 1
  | S n' =>
    countdown_to (inv_hyperop a n') (hyperop_init a n') b
  end.


(* ***** BINARY ***** *)

Open Scope N_scope.

(* Supporting function - Used to compute the budget for bin_cdn_wkr and inv_ack_wrk
   Returns length of the binary representation in type "nat" *)
Definition nat_size (n : N) : nat :=
  match n with
  | 0 => 0%nat
  | Npos p => let fix nat_pos_size (x : positive) : nat :=
                  match x with
                  | xH => 1%nat
                  | xI y | xO y => S (nat_pos_size y) end
              in nat_pos_size p
  end.

(* Countdown worker function *)
Fixpoint bin_cdn_wkr (f : N -> N) (a n : N) (b : nat) : N :=
  match b with
  | O    => 0
  | S b' => if (n <=? a) then 0
            else 1 + bin_cdn_wkr f a (f n) b'
  end.

(* Countdown *)
Definition bin_countdown_to (f : N -> N) (a n : N) : N :=
  bin_cdn_wkr f a n (nat_size (n - a)).

Fixpoint bin_inv_hyperop (a : N) (n : nat) (b : N) :=
  match n with
  | 0%nat => b - 1
  | 1%nat => b - a
  | 2%nat => (b + a - 1) / a
  | S n'  => bin_countdown_to (bin_inv_hyperop a n') 1 b
  end.

Close Scope N_scope.