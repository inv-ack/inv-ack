Require Import BinNat.
Require Import Omega.
Require Import micromega.Lia.
Require Import Logic.FunctionalExtensionality.
Require Import Nnat.
Require Import bin_prelims.
Require Import bin_repeater.
Require Import bin_countdown.
Require Import bin_inverse.
Require applications.

(*
===================================================================================
****************** SECTION 12: BINARY INVERSE HYPEROPS ****************************
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


Fixpoint inv_bin_hyperop (a : N) (n : nat) (b : N) :=
  match n with
  | 0%nat => b - 1
  | 1%nat => b - a
  | 2%nat => (b + a - 1) / a
  | S n'  => bin_countdown_to (inv_bin_hyperop a n') 1 b
  end.

Theorem upp_inv_bin_hyperop_0 : forall a,
   upp_inv_rel (inv_bin_hyperop a 0) (bin_hyperop a 0).
Proof.
  intros a b c. unfold bin_hyperop. unfold inv_bin_hyperop. lia.
Qed.

Theorem upp_inv_bin_hyperop_1 : forall a,
    upp_inv_rel (inv_bin_hyperop a 1) (bin_hyperop a 1).
Proof.
  intros a b c. rewrite bin_hyperop_1. unfold inv_bin_hyperop. lia.
Qed.

Theorem upp_inv_bin_hyperop_2 : forall a,
    1 <= a -> upp_inv_rel (inv_bin_hyperop a 2) (bin_hyperop a 2).
Proof.
  intros a Ha b c. unfold inv_bin_hyperop. rewrite bin_hyperop_2.
  repeat rewrite N.le_ngt. repeat rewrite <- N.le_succ_l.
  rewrite le_div_mul_N by lia. repeat rewrite <- N.add_1_l. lia.
Qed.

Theorem inv_bin_hyperop_0_correct : forall a b,
    inv_bin_hyperop a 0 b =
    N.of_nat (applications.inv_hyperop (N.to_nat a) 0 (N.to_nat b)).
Proof. intros a b. simpl. lia. Qed.

Theorem inv_bin_hyperop_1_correct : forall a b,
    inv_bin_hyperop a 1 b =
    N.of_nat (applications.inv_hyperop (N.to_nat a) 1 (N.to_nat b)).
Proof. intros a b. rewrite applications.inv_hyperop_1. simpl. lia. Qed.

Theorem inv_bin_hyperop_2_correct : forall a b,
    1 <= a ->
    inv_bin_hyperop a 2 b =
    N.of_nat (applications.inv_hyperop (N.to_nat a) 2 (N.to_nat b)).
Proof.
  intros a b Ha. fold (applications.divc (N.to_nat a) (N.to_nat b)).
  apply le_antisym.
  - rewrite (upp_inv_bin_hyperop_2 a Ha _ b), bin_hyperop_2, le_N_nat,
     N2Nat.inj_mul, Nat2N.id, <- applications.divc_correct by lia. trivial.
  - rewrite le_N_nat, Nat2N.id, applications.divc_correct, <- N2Nat.inj_mul,
    <- le_N_nat, <- bin_hyperop_2, <- (upp_inv_bin_hyperop_2 a Ha _ b) by lia.
    lia.
Qed.

Lemma countdown_1_bin_contract_1 : forall f,
    bin_contract_strict_above 1 f ->
    bin_contract_strict_above 1 (bin_countdown_to f 1).
Proof.
  intros f Hf1. assert (H:=Hf1). destruct H as [Hf H1f].
  split; intro n; [ |intro Hbn];
    rewrite bin_countdown_repeat by assumption;
      rewrite N.le_ngt; intro;
        apply (repeat_bin_contract_strict _ _ _ _ Hf1) in H.
  - specialize (nat_size_contract (n - 1)).
    rewrite N2Nat.inj_sub. omega.
  - replace (nat_size (n - 1)) with (S (nat_size ((n - 1) / 2))) in H.
    + assert (H0 := nat_size_contract ((n - 1) / 2)).
      simpl in H. rewrite <- Nat.succ_le_mono in H.
      apply (Nat.le_trans _ _ _ H) in H0.
      replace ((n + 1) / 2) with (1 + (n - 1) / 2) in H0.
      rewrite N2Nat.inj_add in H0. simpl in H0.
      omega. rewrite <- N.div_add_l by lia. f_equal. lia.
    + rewrite <- N.div2_div.
      destruct (n - 1); [simpl in H; omega | induction p; trivial].
Qed.

Lemma inv_bin_hyperop_bin_contract : forall a n,
    2 <= a -> (2 <= n)%nat -> bin_contract_strict_above 1 (inv_bin_hyperop a n).
Proof.
  intros a n Ha Hn. destruct n as [|[|n]]; try omega.
  clear Hn. induction n.
  - simpl. split; intro b; [destruct b|intro Hb];
    rewrite N.le_ngt, <- N.le_succ_l, le_div_mul_N.
    1,2,4,6: lia.
    + remember (N.pos p - 1) as b.
      replace (N.succ _) with (N.succ b + 1) by lia.
      replace (_ - 1) with (b + a) by lia.
      rewrite N.mul_add_distr_l, N.mul_1_r,
                <- N.add_le_mono_r, <- N.lt_nge,
                <- N.le_succ_l, <- N.mul_1_l at 1.
      apply N.mul_le_mono_r. lia.
    + remember (b - 1) as c. replace (_ - 1) with (c + a * 1) by lia.
      rewrite <- N.le_sub_le_add_r, <- N.mul_sub_distr_l.
      replace (_ - 1) with (c / 2 + 1). intro.
      assert (2 * (c/2 + 1) <= c) as contra.
      { apply (N.le_trans _ (a * (c/2 + 1)) _); trivial.
        apply N.mul_le_mono_r. apply Ha. }
      rewrite <- le_div_mul_N in contra; lia.
      replace (_ - 1) with ((b + 1)/2) by lia.
      replace (b + 1) with (c + 1 * 2) by lia.
      symmetry. apply N.div_add. lia.
  - replace (inv_bin_hyperop _ _) with
        (bin_countdown_to (inv_bin_hyperop a (S (S n))) 1) by trivial.
    apply countdown_1_bin_contract_1. apply IHn.
Qed.

Theorem inv_bin_hyperop_correct : forall a n,
    2 <= a -> inv_bin_hyperop a n =
              to_N_func (applications.inv_hyperop (N.to_nat a) n).
Proof.
  intros a n Ha. induction n as [|[|[|n]]].
  1,2,3: apply functional_extensionality; intro b.
  - apply inv_bin_hyperop_0_correct.
  - apply inv_bin_hyperop_1_correct.
  - apply inv_bin_hyperop_2_correct. lia.
  - replace (inv_bin_hyperop _ _) with
      (bin_countdown_to (inv_bin_hyperop a (S (S n))) 1) by trivial.
    apply (f_equal to_nat_func) in IHn.
    rewrite <- nat_N_func_id in IHn.
    rewrite bin_countdown_correct
      by (apply inv_bin_hyperop_bin_contract; lia).
    rewrite IHn. f_equal.
Qed.