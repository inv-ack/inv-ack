Require Import Omega.
Require Import prelims.

(*
=============================================================================
******* SECTION 2: HYPEROPS, ACKERMANN AND REPEATER *************************
=============================================================================
 *)

(* 
 * We introduce "repeater" and show how to use it to 
 * redefine the hyperoperations and the Ackermann function.
 *
 * We also prove several results about the value of hypeopererations at 
 * small numbers and levels, which are treated as trivial in the paper 
 * but which still need to be rigourously proven here to be used in the 
 * formal proofs that come later.
 *
 * We provide several similar results for the Ackermann function.
 * Note that some results here may not be related to results in the paper, 
 * but appear for reasons of completness.
 *)


(* ****** REPEATER ****** *)

(* 
 * Our version of the classic "iter",
 * renamed to emphasize the "starting value" a 
 * and the duality with "countdown_to", which will be introduced soon 
 *) 
Fixpoint repeater_from (f : nat -> nat) (a : nat) (n : nat) : nat :=
  match n with
  | 0    => a
  | S n' => f (repeater_from f a n')
  end. 

(* Repeater is a functional way to look at repeat. See "repeat" in "prelims.v" *)
Theorem repeater_from_repeat :
  forall a f n, repeater_from f a n = repeat f n a.
Proof.
  intros a f n. induction n; [trivial|].
  simpl. rewrite IHn. trivial.
Qed.



(* ****** HYPEROPS ******* *)

(* A function to summarize the initial values of the hyperoperations *)
Definition hyperop_init (a n : nat) : nat :=
  match n with 0 => a | 1 => 0 | _ => 1 end.

(* Popular definition of the hyperops *)
Fixpoint hyperop_original (a n b : nat) : nat :=
  match n with
  | 0    => 1 + b
  | S n' => let fix hyperop' (b : nat) :=
                match b with
                | 0    => hyperop_init a n'
                | S b' => hyperop_original a n' (hyperop' b')
                end
            in hyperop' b
  end.

(* Our definition for hyperops using repeater *)
Fixpoint hyperop (a n b : nat) : nat :=
  match n with
  | 0    => 1 + b
  | S n' => repeater_from (hyperop a n') (hyperop_init a n') b
  end.

(* Proof that the two definitions are equivalent *)
Theorem hyperop_correct :
  forall n a b, hyperop a n b = hyperop_original a n b.
Proof.
  intros n a. induction n; [trivial|].
  induction b; [trivial|].
  simpl in *. rewrite IHb. trivial.
Qed.

(* A handy theorem to transform goals involving hyperops *)
Theorem hyperop_recursion :
  forall n a b,
    hyperop a (S n) (S b) = hyperop a n (hyperop a (S n) b).
Proof. trivial. Qed.

(* The first few functions in the hyperops. 
   Useful for pointing out their inverse specifically *)

Lemma hyperop_1 : forall a b, hyperop a 1 b = b + a.
Proof.
  intro a. induction b; [|rewrite hyperop_recursion, IHb]; trivial.
Qed.

Lemma hyperop_2 : forall a b, hyperop a 2 b = b * a.
Proof.
  intros a b. induction b; [trivial|].
  rewrite hyperop_recursion, IHb, hyperop_1. simpl; omega.
Qed.

Lemma hyperop_3 : forall a b, hyperop a 3 b = a ^ b.
Proof.
  intros a b. induction b; [trivial|].
  rewrite hyperop_recursion, IHb, hyperop_2.
  simpl. apply Nat.mul_comm.
Qed.

(* A beautiful result about hyperops value at b = 1.
   Used in the proof of the theorem "ack_hyperop",
   which is also just for aesthetics *)
Lemma hyperop_n_1 : forall n a, 2 <= n -> hyperop a n 1 = a.
Proof.
  intros n a Hn. do 2 (destruct n; [omega|]).
  clear Hn. induction n; trivial.
Qed.



(* ****** ACKERMANN FUNCTION ******* *)

(* Popular definition of the Peter-Ackermann function *)
Fixpoint ackermann_original (m n : nat) : nat :=
  match m with
  | 0 => 1 + n
  | S m' => let fix ackermann' (n : nat) : nat :=
                match n with
                | 0 => ackermann_original m' 1
                | S n' => ackermann_original m' (ackermann' n')
                end
            in ackermann' n
  end.

(* Our definition using repeater *)
Fixpoint ackermann (n m : nat) : nat :=
  match n with
  | 0    => S m
  | S n' => repeater_from (ackermann n') (ackermann n' 1) m
  end.

(* Proof that the two definitions are equivalent *)
Theorem ackermann_correct :
  forall n b, ackermann n b = ackermann_original n b.
Proof.
  intros n. induction n; trivial.
  induction b. apply IHn.
  simpl in *. rewrite IHb. trivial.
Qed.

(* Handy lemma to transform goals involving ackermann n 0 *)
Lemma ackermann_initial :
  forall m, ackermann (S m) 0 = ackermann m 1.
Proof. trivial. Qed.

(* Handy lemma to transform goals involving ackermann function *)
Lemma ackermann_recursion :
  forall m n,
    ackermann (S m) (S n) = ackermann m (ackermann (S m) n).
Proof. trivial. Qed.

(* A quick demonstration that the Ackermann "kludge" 
   discussed in S1.1 is stated correctly. *)
Theorem ack_hyperop : forall m n,
    3 + ackermann m n = hyperop 2 m (3 + n).
Proof.
  induction m; [trivial|].
  induction n.
  - replace (3 + 0) with 3 by trivial.
    rewrite hyperop_recursion, ackermann_initial, IHm.
    replace (3 + 1) with 4 by trivial.
    f_equal. clear IHm.
    induction m; [trivial|].
    rewrite hyperop_recursion, hyperop_n_1; [trivial | omega].
  - rewrite ackermann_recursion, IHm.
    replace (3 + S n) with (S (3 + n)) by trivial.
    rewrite hyperop_recursion, IHn; trivial.
Qed.