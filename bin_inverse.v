Require Import BinNat.
Require Import Omega.
Require Import micromega.Lia.
Require Import Program.Basics.
Require Import Nnat.
Require Import bin_prelims.
Require inverse.


(*
==================================================================================
****************** SECTION 10: BINARY UPPER INVERSES *****************************
==================================================================================
 *)

(* 
 * In the previous files, we dealt with 
 * increasing functions and expansions.
 * In this file, we formalize upper inverses and 
 * deal with upper inverses of increasing functions. 
 *)


(* f is the upper inverse of F: f N is the smallest n such that F n >= N *)
Definition upp_inv_rel (f F : N -> N) : Prop :=
    forall n m, f m <= n <-> m <= F n.

(* This version for N correctly mirrors its nat counterpart *)
Theorem upp_inv_rel_correct : forall f F,
    upp_inv_rel f F <-> inverse.upp_inv_rel (to_nat_func f) (to_nat_func F).
Proof.
  intros f F. unfold upp_inv_rel. unfold inverse.upp_inv_rel.
  unfold to_nat_func. split; intros H n m.
  - repeat rewrite le_nat_N. repeat rewrite N2Nat.id. apply H.
  - specialize (H (N.to_nat n) (N.to_nat m)).
    repeat rewrite le_nat_N in H.
    repeat rewrite N2Nat.id in H. apply H.
Qed.

(* Translation of the upper inverse computation from nat to N *)
Definition upp_inv (F : N -> N) : N -> N :=
  to_N_func (inverse.upp_inv (to_nat_func F)).

Theorem upp_inv_correct :
    forall F, increasing F -> upp_inv_rel (upp_inv F) F.
Proof.
  intros F HF n m. unfold upp_inv. unfold to_N_func.
  rewrite le_N_nat, Nat2N.id. rewrite to_nat_func_incr in HF.
  apply inverse.upp_inv_correct in HF. rewrite (HF _ _).
  unfold to_nat_func. rewrite N2Nat.id. symmetry. apply le_N_nat.
Qed.

Theorem upp_inv_unique :
    forall f F, increasing F -> (upp_inv_rel f F <-> f = upp_inv F).
Proof.
  intros f F.
  rewrite to_nat_func_incr, upp_inv_rel_correct.
  unfold upp_inv. intro HF.
  rewrite inverse.upp_inv_unique by apply HF.
  split; intro. 
  - rewrite <- H. apply N_nat_func_id.
  - rewrite H. symmetry. apply nat_N_func_id.
Qed.