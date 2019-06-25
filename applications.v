Require Import Omega.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.
Require Import inverse.
Require Import countdown.

(*
===================================================================================
*************** SECTION 6: INVERSE HYPEROPS, DIVISION, LOG AND LOG* ***************
===================================================================================
 *)

(* 
 * We use countdown to implement an inverse tower for the Hyperoperation.
 * Interestingly, the 2nd, 3rd and 4th levels of this tower correspond to 
 * divcision, logc base b and log* base b, which are not defined in the 
 * Coq Standard Library. 
 *
 * Our definitions, which use countdown, offer enough versatility and 
 * flexibility to substantiate easy and direct proof for a vast range 
 * of facts about these functions.
 *)


(* ****** INVERSE-HYPEROP TOWER ****** *)

Fixpoint inv_hyperop a n b :=
  match n with
  | 0 => b - 1
  | S n' =>
    countdown_to (inv_hyperop a n') (hyperop_init a n') b
  end.

(* Handy results to transform goals involving inv_hyperop *)
Theorem inv_hyperop_recursion :
  forall n a,
    inv_hyperop a (S n) = countdown_to (inv_hyperop a n) (hyperop_init a n).
Proof. trivial. Qed.

(* Several results about first few levels of inv_hyperop.
   Used to prove correctness of divcision and logc later on. *)

Theorem inv_hyperop_0_contract_strict :
  forall a k, contract_strict_above k (inv_hyperop a 0).
Proof. intro a. split; intro n; simpl; omega. Qed.

Theorem inv_hyperop_1 :
  forall a b, inv_hyperop a 1 b = b - a.
Proof.
  intros a b. rewrite inv_hyperop_recursion. remember (b - a) as m.
  generalize dependent b. induction m.
  - intros b Hb. apply countdown_recursion.
    1: apply inv_hyperop_0_contract_strict.
       unfold hyperop_init; omega.
  - intros b Hb. remember (m + a) as n. rewrite <- (IHm n) by omega.
    replace n with (inv_hyperop a 0 b)
        by (simpl; unfold hyperop_init; omega).
    apply countdown_recursion.
    1: apply inv_hyperop_0_contract_strict.
    unfold hyperop_init; omega.
Qed.

Corollary inv_hyperop_1_repeat :
  forall a k m, repeat (inv_hyperop a 1) k m = m - k * a.
Proof.
  intros a k m. induction k; [simpl; omega|].
  remember (inv_hyperop a 1) as f. simpl.
  rewrite IHk, Heqf, inv_hyperop_1; omega.
Qed.

(* 
 * Main theorem of this section. 
 * Establishes the correctness of the inverse hyperoperations' 
 * definition given in inv_hyperop.v 
 *)
Theorem inv_hyperop_correct :
  forall a n, 2 <= a -> upp_inv_rel (inv_hyperop a n) (hyperop a n).
Proof.
  intros a n Ha.
  assert (forall m, repeatable_from (hyperop_init a m) (hyperop a m)).
  { induction m.
    1: rewrite repeatable_simpl; split; simpl;
      try split; try intros u v; omega.
    destruct m; try destruct m.
    1, 3: try replace (hyperop a (S (S (S m)))) with
            (repeater_from (hyperop a (S (S m)))
               (hyperop_init a (S (S m)))) by trivial;
      apply repeater_repeatable; simpl; try omega; assumption.
    rewrite repeatable_simpl. split; [|simpl; omega].
    intros u v. repeat rewrite hyperop_2. intros.
    apply (mult_lt_compat_r _ _ _ H). omega.
  }
  induction n.
  1: simpl. intros u v. omega.
  destruct (H n) as [_ Hn].
  apply countdown_repeater_upp_inverse; assumption.
Qed.

(* ****** DIVISION AND LOGARITHM ********************************* *)

(* Computes ceiling of b / a *)
Definition divc a b := inv_hyperop a 2 b.

Theorem divc_correct :
  forall a b m, 1 <= a -> divc a b <= m <-> b <= m * a.
Proof.
  intros a b m Ha. destruct a; [omega|].
  unfold divc. rewrite inv_hyperop_recursion.
  rewrite countdown_repeat
      by (split; intro n; rewrite inv_hyperop_1; omega).
  rewrite inv_hyperop_1_repeat. unfold hyperop_init. omega.
Qed.

(* Computes ceiling of logc_a(b) *)
Definition logc a b := inv_hyperop a 3 b.

Theorem logc_correct :
  forall a b m, 2 <= a -> logc a b <= m <-> b <= a ^ m.
Proof.
  intros a b m Ha.
  unfold logc. rewrite <- hyperop_3.
  apply inv_hyperop_correct; trivial.
Qed.

(* Computes log*_a(b).
   Its correctness has already been established in inv_hyperop_correct *)
Definition logstar a b := inv_hyperop a 4 b.