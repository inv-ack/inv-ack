Require Import Omega.
Require Import Program.Basics.
Require Import Logic.FunctionalExtensionality.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.

(*
==================================================================================
********************* SECTION 4: UPPER INVERSES **********************************
==================================================================================
 *)

(* 
 * In the previous files, we dealt with 
 * increasing functions and expansions.
 * In this file, we formalize upper inverses and 
 * deal with upper inverses of increasing functions. 
 *)


(* ****** UPPER INVERSE ****** *)

(* f is the upper inverse of F. ie, f N is the smallest n such that F n >= N *)
Definition upp_inv_rel (f F : nat -> nat) : Prop :=
    forall n N, f N <= n <-> N <= F n.

(* 
 * An increasing function F has a recursively definable upper inverse.
 * F is increasing (from assumption), so the below definition will 
 * compute its upper inverse.
 *
 * Do NOT use it for functions that are not "always increasing".
 * This is why we are only interested in inverses of increasing functions.
 * Inverses of other functions on naturals are hard to define neatly,
 * and do not behave nicely.
 *
 * This computation implies the upper inverse exists, which is useful for
 * proofs about worker functions later on 
 *)
Fixpoint upp_inv (F : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => let m := upp_inv F n' in if F m =? n' then S m else m
  end.

(* Proof that the definition of upper inverse given above is correct *)
Theorem upp_inv_correct :
    forall F, increasing F -> upp_inv_rel (upp_inv F) F.
Proof.
  intros F HF n N. generalize dependent n.
  induction N; intro n; [simpl; omega|].
  assert (N <= F (upp_inv F N)) as HN by (apply IHN; omega).
  simpl. remember (upp_inv F N) as m. remember (F m =? N) as b.
  symmetry in Heqb. destruct b.
  - rewrite Nat.eqb_eq in Heqb. rewrite <- Heqb.
    apply (incr_twoways _ _ _ HF).
  - rewrite Nat.eqb_neq in Heqb.
    assert (N < F m) as HNm by omega.
    split; rewrite IHN; [|omega].
    rewrite <- IHN; rewrite not_lt;
    rewrite incr_twoways by apply HF; omega.
Qed.

(* Proof that upper inverse is unique *)
Theorem upp_inv_unique :
    forall f F, increasing F -> (upp_inv_rel f F <-> f = upp_inv F).
Proof.
  intros f F HF.
  assert (upp_inv_rel (upp_inv F) F) as H
      by (apply upp_inv_correct; apply HF).
  split; intro; [|rewrite H0; trivial].
  apply functional_extensionality. intro N.
  assert (f N <= upp_inv F N) by now rewrite (H0 _ N), <- (H _ N). 
  assert (upp_inv F N <= f N) by now rewrite (H _ N), <- (H0 _ N). 
  omega.
Qed.

(* Composing F's inverse and F gives identity *)
Theorem upp_inv_compose :
    forall f F, increasing F -> upp_inv_rel f F -> compose f F = id.
Proof.
  intros f F HF HfF. apply functional_extensionality. intro n.
  unfold id, compose.
  assert (f (F n) <= n) as H0 by now rewrite (HfF n (F n)).
  assert (n <= f (F n)) as H1.
  { rewrite not_lt. rewrite (incr_twoways F (f (F n)) n HF).
    rewrite <- not_lt. rewrite <- (HfF (f (F n)) (F n)). trivial. }
  omega.
Qed.

(* Repeat preserves upper inverse relation *)
Lemma upp_inv_repeat : forall k f F,
    upp_inv_rel f F -> upp_inv_rel (repeat f k) (repeat F k).
Proof.
  unfold upp_inv_rel. intros k f F HfF.
  induction k; [intros n N; simpl; reflexivity|].
  intros n N. rewrite repeat_S_comm. split.
  - intro. rewrite IHk in H. simpl. apply HfF. apply H.
  - simpl; rewrite <- HfF, IHk; trivial.
Qed.