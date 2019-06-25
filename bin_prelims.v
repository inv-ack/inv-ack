Require Import BinNat.
Require Import Nnat.
Require Import micromega.Lia.
Require Import Logic.FunctionalExtensionality.
Require Import Omega.
Require Import prelims.

Require increasing_expanding.

Open Scope N_scope.


(*
=============================================================================
***************** SECTION 8: BINARY PRELIMINARIES ***************************
=============================================================================
 *)

(* 
 * This file contains recurrently useful results and definitions
 * that are used throughout the subsequent files.
 *
 * We first discuss conversions between N (binary) and nat (unary) and 
 * vice-versa.
 * 
 * Next, we present increasing functions when inputs are in N.
 *)

Lemma le_antisym: forall m n : N,
    (m <= n) -> (n <= m) -> (m = n).
Proof. intros. lia. Qed.

(* ****** N TO nat COMPARISON CONVERSION ******** *)

Lemma le_N_nat : forall m n : N,
    (m <= n) <-> (N.to_nat m <= N.to_nat n)%nat.
Proof.
  intros m n. rewrite <- N.compare_le_iff.
  rewrite N2Nat.inj_compare. apply Nat.compare_le_iff.
Qed.

Lemma le_nat_N : forall m n : nat,
    (m <= n)%nat <-> (N.of_nat m <= N.of_nat n).
Proof.
  intros m n. rewrite <- Nat.compare_le_iff.
  rewrite Nat2N.inj_compare. apply N.compare_le_iff.
Qed.

Lemma lt_N_nat : forall m n : N,
    (m < n) <-> (N.to_nat m < N.to_nat n)%nat.
Proof.
  intros m n. rewrite <- N.compare_lt_iff.
  rewrite N2Nat.inj_compare. apply Nat.compare_lt_iff.
Qed.

Lemma lt_nat_N : forall m n : nat,
    (m < n)%nat <-> (N.of_nat m < N.of_nat n).
Proof.
  intros m n. rewrite <- Nat.compare_lt_iff.
  rewrite Nat2N.inj_compare. apply N.compare_lt_iff.
Qed.

(* LEMMAS ABOUT DIV THAT ARE NOT IN STANDARD LIBRARY *)

Lemma le_div_mul_N : forall a b q : N,
    b <> 0 -> (q <= a / b) <-> (b * q <= a).
Proof.
  intros a b q Hb. split; intro H.
  - rewrite N.le_ngt. intro contra.
    apply N.div_lt_upper_bound in contra; [lia | trivial].
  - apply N.div_le_lower_bound; trivial.
Qed.

Lemma le_div_mul_nat : forall a b q : nat,
    (b <> 0)%nat -> (q <= a / b)%nat <-> (b * q <= a)%nat.
Proof.
  intros a b q Hb. split; intro H.
  - rewrite Nat.le_ngt. intro contra.
    apply Nat.div_lt_upper_bound in contra; [omega | trivial].
  - apply Nat.div_le_lower_bound; trivial.
Qed.

Lemma div_sub : forall a b c,
    c <> 0 -> (a - c * b) / c = a / c - b.
Proof.
  intros a b c Hc. destruct (N.le_gt_cases a (c * b)) as [H|H].
  - replace (a / c - b) with 0 by
        (symmetry; rewrite N.sub_0_le;
    apply N.div_le_upper_bound; trivial).
    rewrite <- N.sub_0_le in H. rewrite H. apply N.div_0_l, Hc.
  - replace a with (a - c * b + b * c) at 2 by lia.
    rewrite N.div_add by trivial. lia.
Qed.

Lemma div_nat_N : forall m n,
    m / n = N.of_nat (N.to_nat m / N.to_nat n).
Proof.
  intros m n. destruct n; [destruct m|]; trivial.
  apply le_antisym.
  - rewrite le_N_nat, Nat2N.id, le_div_mul_nat,
    <- N2Nat.inj_mul, <- le_N_nat, <- le_div_mul_N; lia.
  - rewrite le_div_mul_N, <- (N2Nat.id (Npos p)), <- Nat2N.inj_mul,
    Nat2N.id, <- N2Nat.id, <- le_nat_N, <- le_div_mul_nat; lia.
Qed.

(* ****** REPEATED APPLICATION ************ *)

Fixpoint repeat (f: N -> N) (rep : nat) (n : N) : N :=
  match rep with
  | O => n
  | S rep' => f (repeat f rep' n)
  end.

Theorem repeat_S_comm :
    forall f k n, repeat f (S k) n = repeat f k (f n).
Proof.
  induction k; trivial. intro. simpl in *. rewrite IHk. trivial.
Qed.

Theorem repeat_plus :
    forall f k l n, repeat f (k + l) n = repeat f k (repeat f l n).
Proof.
  induction k; trivial. simpl; intros; rewrite IHk; trivial.
Qed.


(* ****** INCREASING FUNCTIONS ****** *)
Definition increasing (f : N -> N) : Prop :=
    forall n m, n < m -> f n < f m.


(* ****** NAT_SIZE ************ *)

(* Length of the binary representation *)
Definition nat_size (n : N) : nat :=
  match n with
  | 0 => 0%nat
  | Npos p => let fix nat_pos_size (x : positive) : nat :=
                  match x with
                  | xH => 1%nat
                  | xI y | xO y => S (nat_pos_size y) end
              in nat_pos_size p
  end.

(* nat_size is increasing *)
Lemma nat_size_incr :
    forall m n, m <= n -> (nat_size m <= nat_size n)%nat.
Proof.
  intros m n Hmn.
  destruct m as [|pm]. simpl. omega.
  destruct n as [|pn]. lia.
  generalize dependent pm.
  induction pn;
    intros; [ | |replace (Npos pm) with 1 by lia; trivial];
      destruct pm; simpl; try omega; apply le_n_S; apply IHpn; lia.
Qed.


(* Binary contraction contracts size *)
Lemma div2_nat_size :
    forall m n, 0 < n ->
      m <= n / 2 -> (1 + nat_size m <= nat_size n)%nat.
Proof.
  intros m n Hn Hmn. apply (Nat.le_trans _ (1 + nat_size (n / 2)) _).
  - apply le_n_S. apply nat_size_incr. apply Hmn.
  - destruct n; try lia. rewrite <- N.div2_div.
    destruct p; trivial.
Qed.

Lemma div2_contr :
    forall m n, 0 < n -> m <= n / 2 -> m < n.
Proof.
  intros m n Hn Hmn. apply (div2_nat_size m n Hn) in Hmn.
  rewrite N.lt_nge. intro. apply nat_size_incr in H. omega.
Qed.

Lemma nat_size_contract : forall n, (nat_size n <= N.to_nat n)%nat.
Proof. destruct n; trivial. simpl. induction p; simpl; lia. Qed.

Lemma nat_size_log2_up : forall n,
    nat_size n = N.to_nat (N.log2_up (N.succ n)).
Proof.
  destruct n; trivial. unfold N.log2_up.
  assert (1 < N.succ (N.pos p)) by lia.
  rewrite <- N.compare_lt_iff in H. rewrite H, N.pred_succ.
  clear H.
  induction p; trivial; rewrite N2Nat.inj_succ;
  [replace (Npos p~1) with (2 * Npos p + 1) at 2 by lia|
   replace (Npos p~0) with (2 * Npos p ) at 2 by lia];
  [rewrite N.log2_succ_double by lia|rewrite N.log2_double by lia];
  rewrite <- IHp; trivial.
Qed.


(* ****** NAT TO N CONVERSION ************ *)

Definition to_N_func (f : nat -> nat) (n : N) : N
    := N.of_nat (f (N.to_nat n)).

Definition to_nat_func (f : N -> N) (n : nat) : nat
    := N.to_nat (f (N.of_nat n)).

Theorem N_nat_func_id :
    forall (f : N -> N), f = to_N_func (to_nat_func f).
Proof.
  intro f. apply functional_extensionality. intro n.
  unfold to_N_func. unfold to_nat_func.
  repeat rewrite N2Nat.id. trivial.
Qed.

Theorem nat_N_func_id :
    forall (f : nat -> nat), f = to_nat_func (to_N_func f).
Proof.
  intro f. apply functional_extensionality. intro n.
  unfold to_N_func. unfold to_nat_func.
  repeat rewrite Nat2N.id. trivial.
Qed.

Lemma to_N_func_repeat : forall f k,
    repeat f k = to_N_func (prelims.repeat (to_nat_func f) k).
Proof.
  intros f k.
  induction k; apply functional_extensionality;
    intro n; simpl; unfold to_N_func;
      [symmetry; apply N2Nat.id | repeat f_equal].
  rewrite IHk. unfold to_nat_func. rewrite N2Nat.id.
  unfold to_N_func. trivial.
Qed.

Lemma to_nat_func_repeat : forall f k,
    prelims.repeat f k = to_nat_func (repeat (to_N_func f) k).
Proof.
  intros f k.
  induction k; apply functional_extensionality;
    intro n; simpl; unfold to_nat_func;
      [symmetry; apply Nat2N.id | repeat f_equal].
  rewrite IHk. unfold to_N_func. rewrite Nat2N.id.
  unfold to_nat_func. trivial.
Qed.

Lemma to_nat_func_incr : forall f,
    increasing f <-> increasing_expanding.increasing (to_nat_func f).
Proof.
  split; unfold to_nat_func; intros Hf m n.
  - rewrite lt_nat_N. rewrite <- lt_N_nat. apply Hf.
  - repeat rewrite lt_N_nat. intro. apply Hf in H.
    repeat rewrite N2Nat.id in H. apply H.
Qed.