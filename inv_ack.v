Require Import Omega.
Require Import Program.Basics.
Require Import Logic.FunctionalExtensionality.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.
Require Import inverse.
Require Import countdown.
Require Import applications.

(*
==========================================================================
*************** SECTION 7: THE INVERSE ACKERMANN FUNCTION ****************
==========================================================================
 *)

(* 
 * This section contains the most important application of countdown,
 * the Inverse Ackermann function.
 *
 * We first define an inverse tower for the Ackermann hierarchy, 
 * then write a theorem proving its correctness.
 * 
 * Then we define a structurally terminating definition for the inverse
 * Ackermann function, and prove its correctness using the above theorem.
 *
 * We digress briefly to discuss the two-parameter inverse Ackermann
 * function, which some authors prefer. 
 *
 * Finally, we state and prove the correctness of the time-bound improvement, 
 * on the single-argument inverse Ackermann, which runs in linear time.
 *)


(* ****** INVERSE ACKERMANN HIERARCHY ****** *)

Fixpoint alpha m x :=
  match m with
  | 0 => x - 1
  | S m' => countdown_to (alpha m') 1 (alpha m' x)
  end.

Theorem alpha_correct :
  forall m, contract_strict_above 1 (alpha m) /\
            upp_inv_rel (alpha m) (ackermann m).
Proof.
  induction m.
  1: split; [split; intro; simpl; omega | intros n x; simpl; omega].
  destruct IHm as [IHm0 IHm1]. split.
  - simpl. split; intro n;
             rewrite countdown_antirecursion by apply IHm0;
             apply (countdown_contract_strict 1 _ 1) in IHm0;
             destruct IHm0 as [IHm00 IHm01]; trivial.
    + specialize (IHm00 n); omega.
    + specialize (IHm01 n); omega.
  - intros n x. simpl. rewrite repeater_from_repeat.
    rewrite <- repeat_S_comm.
    apply (upp_inv_repeat (S n) _ _) in IHm1.
    rewrite <- (IHm1 1 x), repeat_S_comm.
    now apply countdown_repeat.
Qed.


(* ****** INVERTABILITY OF ACKERMANN FUNCTION ****** *)

(* Repeatability *)
Lemma ack_repeatable : forall i, repeatable_from 0 (ackermann i).
Proof.
  induction i; split; try split;
    intro n; try intro m; simpl; try omega;
      apply (repeatable_monotone 0 1 _) in IHi; try omega;
        repeat rewrite repeater_from_repeat;
        repeat rewrite <- repeat_S_comm;
        repeat rewrite <- repeater_from_repeat;
        apply (repeater_repeatable _ 0 _) in IHi; try omega;
          destruct IHi as [IHi0 IHi1];
          [intro; apply IHi0; omega | |];
          apply (Nat.le_trans _ (S (S n)) _); try apply IHi1; omega.
Qed.

(* 
 * Ackermann at level 1. It is useful for two purposes:
 *  (1) Computes alpha 1 below, which is used in hard-coding the second level
 *      for linear runtime.
 *  (2) Serves to prove base case for "ack_incr_by_lvl"  
 *)
Lemma ack_1 : forall n, ackermann 1 n = (S (S n)).
Proof.
  induction n; [|rewrite ackermann_recursion; rewrite IHn]; trivial.
Qed.

(* Alpha at level 1. Used in hard-coding the second level for linear runtime *)
Lemma alpha_1 : alpha 1 = (fun n => n - 2).
Proof.
  assert (upp_inv_rel (alpha 1) (ackermann 1)) as H
      by apply alpha_correct.
  assert (upp_inv_rel (fun n => n - 2) (ackermann 1)) as H'
      by (intros n m; rewrite ack_1; omega). 
  rewrite upp_inv_unique in H
      by (intros n m; repeat rewrite ack_1; omega).
  rewrite upp_inv_unique in H'
      by (intros n m; repeat rewrite ack_1; omega).
  now rewrite H'. 
Qed.

(* 
 * The two results below show that the diagonal Ackermann function is increasing,
 * and therefore has a proper upper inverse. 
 * We need them to compute the inverse 
 * value for the inv_ack correctness proof later. 
 *)

(* Strict Increasing With Level *)
Lemma ack_incr_by_lvl : forall n, increasing (fun i => ackermann i n).
Proof.
  intro n. rewrite incr_S. intro i. generalize dependent n.
  induction i; intro n. 1: rewrite ack_1; simpl; omega.
  remember (S i) as p. destruct n. 1: simpl;
  apply ack_repeatable; omega.
  rewrite ackermann_recursion. apply ack_repeatable.
  assert (Hi := IHi).
  rewrite Heqp in IHi. specialize (IHi (S n)).
  rewrite ackermann_recursion in IHi.
  rewrite <- incr_twoways in IHi by apply ack_repeatable.
  apply (Nat.lt_trans _ (ackermann (S i) n) _); trivial.
  clear IHi. induction n; [now simpl|].
  repeat rewrite ackermann_recursion.
  apply (Nat.lt_trans _ (ackermann i (ackermann (S p) n)) _).
  1: apply ack_repeatable; assumption. apply Hi.
Qed.

(* Diagonal Strict Increasing *)
Lemma diag_ack_incr : increasing (fun n => ackermann n n).
Proof.
  intros n m Hnm.
  apply (Nat.lt_trans _ (ackermann n m) _);
    [apply ack_repeatable | apply ack_incr_by_lvl]; assumption.
Qed.

(* Small helper lemma - alpha decreases by level *)
Lemma alpha_decr_by_lvl : forall i n, alpha (S i) n <= alpha i n.
Proof.
  intros i n. 
  destruct (alpha_correct i) as [_ Hi].
  destruct (alpha_correct (S i)) as [_ HSi].
  rewrite (HSi (alpha i n) n).
  apply (Nat.le_trans _ (ackermann i (alpha i n)) _).
  - rewrite <- (Hi (alpha i n) n). trivial.
  - assert (H := ack_incr_by_lvl (alpha i n) i (S i)). omega.
Qed.


(* ****** INVERSE ACKERMANN FUNCTION ****** *)

Fixpoint inv_ack_wkr (f : nat -> nat) (n k b : nat) : nat :=
  match b with
  | 0    => k
  | S b' => if (n <=? k) then k
              else let g := (countdown_to f 1) in
                   inv_ack_wkr (compose g f) (g n) (S k) b'
  end.

(* 
 * IMPORTANT:
 * A new computational definition of inverse Ackermann, runtime O(n^2) 
 *)
Definition inv_ack n := inv_ack_wkr (alpha 0) (alpha 0 n) 0 n.


(* Proof of Correctness of the above: *)
(* First, an intermediate lemma about inv_ack_wkr *)
Lemma inv_ack_wkr_intermediate :
  forall i n b,
    i < alpha i n -> i < b ->
    inv_ack_wkr (alpha 0) (alpha 0 n) 0 b =
    inv_ack_wkr (alpha (S i)) (alpha (S i) n) (S i) (b - (S i)).
Proof.
  intros i n b. rewrite <- Nat.leb_gt.
  generalize dependent b. generalize dependent n.
  induction i.
  - simpl. intros n b Hn Hb. unfold inv_ack_wkr.
    destruct b; try omega. unfold compose. rewrite Hn.
    replace (S b - 1) with b by omega. trivial.
  - intros n b Hn Hb. rewrite IHi; [| |omega].
    + remember (S i) as p.
      replace (alpha (S p)) with
        (compose (countdown_to (alpha p) 1) (alpha p)) by trivial.
      unfold inv_ack_wkr.
      remember (b - p) as c. destruct c; try omega.
      rewrite Hn. replace (b - S p) with c by omega.
      trivial.
    + rewrite Nat.leb_gt. rewrite Nat.leb_gt in Hn.
      apply (Nat.lt_le_trans _ (alpha (S i) n) _);
        [omega|apply alpha_decr_by_lvl].
Qed.

(* Proof that inv_ack correctly calculates the inverse of the 
   diagonal Ackermann-Peter function *)
Theorem inv_ack_correct :
  upp_inv_rel inv_ack (fun k => ackermann k k).
Proof.
  rewrite upp_inv_unique by apply diag_ack_incr.
  assert (forall n N : nat,
             upp_inv (fun k : nat => ackermann k k) N <= n
             <-> alpha n N <= n) as H.
  { intros n N.
    rewrite (upp_inv_correct (fun k : nat => ackermann k k)
                                diag_ack_incr n N).
    destruct (alpha_correct n) as [_ Hm]. symmetry. apply Hm. }
  apply functional_extensionality. intro n.
  remember (upp_inv (fun k : nat => ackermann k k) n) as m.
  unfold inv_ack. assert (H0 := H). destruct m.
  - specialize (H 0 n). rewrite <- Heqm in H.
    assert (n <= 1) as Hn by (simpl in H; omega). 
    destruct n; simpl; trivial; destruct n; simpl; trivial; omega.
  - specialize (H m n). rewrite <- Heqm in H.
    assert (m < alpha m n) as Hn by omega.
    assert (S m < n) as Hmn.
    { destruct (alpha_correct m) as [_ Hm]. rewrite <- not_le in Hn.
      rewrite (Hm m n) in Hn. rewrite <- not_le. intro.
      assert (ackermann m m <= m) by omega.
      destruct (ack_repeatable m) as [_ Hackm].
      destruct Hackm as [_ Hackm]. specialize (Hackm m). omega. }
    rewrite (inv_ack_wkr_intermediate m n n Hn). 2: omega.
    assert (alpha (S m) n <=? (S m) = true).
      { rewrite Nat.leb_le. specialize (H0 (S m) n).
        rewrite <- Heqm in H0. omega. }
    unfold inv_ack_wkr.
    remember (n - S m) as p. destruct p; [omega|].
    rewrite H1. trivial.
Qed.

(* ********* DIGRESSION: TWO PARAMETER INVERSE ACKERMANN ************* *)

(* Two parameter Inverse Ackerman worker function *)
Fixpoint two_params_inv_ack_wkr (f : nat -> nat) (n k b : nat) : nat :=
  match b with
  | 0    => 0
  | S b' => if (n <=? k) then 0
              else let g := (countdown_to f 1) in
                   S (two_params_inv_ack_wkr (compose g f) (g n) k b')
  end.

(* Two parameters Inverse Ackermann function *)
Definition two_params_inv_ack (m n : nat) : nat :=
  let f := (fun x => x - 2) in
    let n' := (Nat.log2_up n) in
      1 + two_params_inv_ack_wkr f (f n') (m / n) n'.

(* Correctness proofs begin here *)
(* First, a lemma about the worker function's inner working *)
Lemma two_params_inv_ack_wkr_intermediate :
    forall i n k b, k < alpha i n -> i <= b ->
      two_params_inv_ack_wkr (alpha 1) (alpha 1 n) k b =
        i + two_params_inv_ack_wkr (alpha (S i)) (alpha (S i) n) k (b - i).
Proof.
  induction i; intros n k b Hin Hib.
  1: rewrite Nat.add_0_l; f_equal; omega.
  rewrite IHi.
  2: apply (Nat.lt_le_trans _ (alpha (S i) n) _ Hin),
              alpha_decr_by_lvl.
  2: omega.
  unfold two_params_inv_ack_wkr at 1.
  replace (b - i) with (S (b - (S i))) by omega.
  rewrite <- Nat.leb_gt in Hin. rewrite Hin.
  fold two_params_inv_ack_wkr.
  rewrite <- Nat.add_succ_comm. trivial.
Qed.

(* Correctness theorem for two_params_inv_ack *)
Theorem two_params_inv_ack_correct :
    forall m n, two_params_inv_ack m n =
      1 + upp_inv (fun x => ackermann (S x) (m / n)) (Nat.log2_up n).
Proof.
  intros m n. unfold two_params_inv_ack.
  remember (Nat.log2_up n) as b. remember (m / n) as a.
  replace (b - 2) with (alpha 1 b) by (rewrite alpha_1; trivial).
  rewrite <- alpha_1. f_equal. clear Heqb Heqa m n.
  remember (fun x => two_params_inv_ack_wkr
                       (alpha 1) (alpha 1 x) a x) as f.
  replace (two_params_inv_ack_wkr (alpha 1) (alpha 1 b) a b)
              with (f b) by (rewrite Heqf; trivial).
  remember (fun x => ackermann (S x) a) as F.
  assert (increasing F) as HF.
  { intros x y. rewrite HeqF. rewrite Nat.succ_lt_mono.
    apply ack_incr_by_lvl. }
  remember (upp_inv F b) as p. destruct p.
  - assert (alpha 1 b <= a) as Hab.
    { destruct (alpha_correct 1) as [_ H]. rewrite (H a b).
      replace (ackermann 1 a) with (F 0) by (rewrite HeqF; trivial).
      rewrite <- (upp_inv_correct F HF 0 b). omega. }
    rewrite Heqf. rewrite <- Nat.leb_le in Hab.
    unfold two_params_inv_ack_wkr. destruct b;
      [|rewrite Hab]; trivial.
  - assert (~ b <= F p) as Hp by
          (rewrite <- (upp_inv_correct F HF p b); omega). 
    rewrite HeqF in Hp. destruct (alpha_correct (S p)) as [_ H].
    rewrite <- (H a b), <- Nat.lt_nge in Hp. rewrite Heqf.
    rewrite (two_params_inv_ack_wkr_intermediate (S p) _ _ _ Hp).

    + unfold two_params_inv_ack_wkr. destruct (b - S p); [omega|].
      replace (ackermann (S p) a) with (F p)
          by (rewrite HeqF; trivial).
      replace (alpha (S (S p)) b <=? a) with true; [omega|].
      symmetry. rewrite Nat.leb_le.
      destruct (alpha_correct (S (S p))) as [_ H1]. rewrite (H1 a b).
      replace (ackermann (S (S p)) a) with (F (S p))
          by (rewrite HeqF; trivial).
      rewrite <- (upp_inv_correct F HF (S p) b). omega.
    + rewrite Nat.lt_nge, (H a b), <- Nat.lt_nge in Hp.
      apply (Nat.le_trans _ (ackermann (S p) a) _); [|omega].
      clear Heqp Hp H. induction (S p) as [|k]; [omega|].
      rewrite Nat.le_succ_l.
      apply (Nat.le_lt_trans _ (ackermann k a) _ IHk).
      apply ack_incr_by_lvl. omega.
Qed.


(* ***** LINEAR-TIME INVERSE ACKERMANN BY HARD-CODING SECOND LEVEL ***** *)

(* IMPORTANT: A new computational definition for inverse Ackerman *)
(* We hardcode the second 'alpha' level for runtime O(n). *)
Definition inv_ack_linear n :=
  match n with
  | 0 | 1 => 0
  | _     => let f := (fun x => x - 2) in inv_ack_wkr f (f n) 1 (n - 1)
  end.

(* Correctness proof *)
Theorem inv_ack_linear_correct : inv_ack_linear = inv_ack.
Proof.
  apply functional_extensionality. intro n.
  unfold inv_ack, inv_ack_linear.
  destruct n; try destruct n; trivial.
  rewrite (inv_ack_wkr_intermediate 0 _ _) by (simpl; omega).
  rewrite alpha_1; trivial.
Qed.

(* Please see inv_ack_test.v for a demonstration of the time bound. *)