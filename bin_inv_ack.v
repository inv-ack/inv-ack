Require Import BinNat.
Require Import Omega.
Require Import micromega.Lia.
Require Import Logic.FunctionalExtensionality.
Require Import Program.Basics.
Require Import Nnat.
Require Import bin_prelims.
Require Import bin_repeater.
Require Import bin_countdown.
Require Import bin_inverse.
Require inv_ack.

(*
==========================================================================
******* SECTION 13: THE BINARY INVERSE ACKERMANN FUNCTION ****************
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
 * We digress briefly to state and prove the two-argument inverse 
 * Ackermann function, which some authors prefer. Again, inputs are in binary.
 *
 * Finally we state and prove the correctness of the time-bound improvement, 
 * which runs in linear time.
 *)

Lemma to_nat_diag_ack :
  (fun n => repeater.ackermann n n) =
  to_nat_func (fun n : N => bin_ackermann n n).
Proof.
  apply functional_extensionality. unfold to_nat_func. intro n.
  rewrite bin_ackermann_correct. repeat rewrite Nat2N.id. trivial.
Qed.

(* Diagonal Strict Increasing *)
Lemma diag_ack_incr : increasing (fun n => bin_ackermann n n).
Proof.
  rewrite to_nat_func_incr.
  rewrite <- to_nat_diag_ack. apply inv_ack.diag_ack_incr.
Qed.


(* *********** INVERSE ACKERMANN HIERARCHY ******************* *)

(* Definition *)
Fixpoint bin_alpha (m : nat) (x : N) : N :=
  match m with
  | 0%nat => x - 1          | 1%nat => x - 2
  | 2%nat => N.div2 (x - 2) | 3%nat => N.log2 (x + 2) - 2
  | S m'  => bin_countdown_to (bin_alpha m') 1 (bin_alpha m' x)
  end.

(* Crucial Lemma to prove the link from level 2 to level 3 *)
Lemma bin_alpha_2_bin_contract :
    bin_contract_strict_above 1 (bin_alpha 2).
Proof.
  split; intro n; simpl; rewrite N.div2_div;
    [apply N.div_le_upper_bound|intro; apply N.div_le_mono]; lia.
Qed.

(* Recursion *)
Theorem bin_alpha_recursion :
    forall m, (2 <= m)%nat ->
              bin_alpha (S m) =
              compose (bin_countdown_to (bin_alpha m) 1) (bin_alpha m).
Proof.
  destruct m as [|[|[|m]]]; trivial;
    [omega | omega | intro]. clear H.
  apply functional_extensionality; intro n. unfold compose.
  simpl. rewrite N.div2_div.
  replace (n - 2) with (n + 2 - 2*2) by lia.
  rewrite div_sub by lia.
  replace (N.log2 (n + 2) - 2)
    with (N.log2 ((n + 2) / 2) - 1)
    by (rewrite <- N.div2_div, N.div2_spec, N.log2_shiftr; lia).
  remember ((n + 2) / 2) as m. clear n Heqm.
  destruct m as [|p]; trivial.
  induction p; trivial;
    rewrite bin_countdown_recursion by apply bin_alpha_2_bin_contract;
    rewrite N.div2_div;
      [remember (N.pos p~1) as m | remember (N.pos p~0) as m];
        replace (m - 2 - 2) with (m - 2 * 2) by lia;
          rewrite div_sub by lia;
            rewrite <- N.log2_shiftr, <- N.div2_spec, N.div2_div;
              remember (m - 2 <=? 1) as b;
                destruct b; symmetry in Heqb.
  1, 3: rewrite N.leb_le, N.le_sub_le_add_l in Heqb;
    apply (N.div_le_mono _ _ 2) in Heqb.
  2, 4: lia.
  1, 2: unfold N.div at 2 in Heqb; simpl in Heqb;
    rewrite N.log2_null; trivial.
  1, 2: replace (Npos p) with (m / 2) in IHp.
  2: rewrite <- N.div2_succ_double. 
  4: rewrite <- N.div2_double.
  2, 4: rewrite <- N.div2_div; f_equal; trivial.
  1, 2: rewrite N.leb_gt in Heqb; rewrite N.add_comm, <- IHp;
    symmetry; apply N.sub_add;
      rewrite N.le_ngt, N.lt_1_r, N.log2_null, <- N.lt_succ_r;
      simpl; rewrite <- N.le_ngt, le_div_mul_N by lia; lia.
Qed.


(* ******* CORRECTNESS OF INVERSE ACKERMANN HIERARCHY ************** *)

(* Countdown composed with self preserves binary contractiveness *)
Theorem countdown_bin_contract : forall f a b,
    bin_contract_strict_above a f ->
    bin_contract_strict_above b (compose (bin_countdown_to f a) f).
Proof.
  intros f a b Haf0. assert (H:=Haf0). destruct H as [Hf Haf].
  split; intro n; [ |intro Hbn]; unfold compose;
    rewrite bin_countdown_repeat by assumption; rewrite <- repeat_S_comm;
      rewrite N.le_ngt; intro;
        apply (repeat_bin_contract_strict _ _ _ _ Haf0) in H.
  - specialize (nat_size_contract (n - a)).
    rewrite N2Nat.inj_sub. omega.
  - replace (nat_size (n - a)) with
      (S (nat_size ((n - a) / 2))) in H.
    + specialize (nat_size_contract ((n - a) / 2)) as H0.
      simpl in H. rewrite <- Nat.succ_le_mono in H.
      apply (Nat.le_trans _ _ _ H) in H0.
      assert (S (N.to_nat (n/2)) <= N.to_nat (n/2))%nat as contra.
      2: omega.
      apply (Nat.le_trans _ (S (N.to_nat ((n + b) / 2))) _);
        [rewrite <- Nat.succ_le_mono |
         apply (Nat.le_trans _ (N.to_nat ((n - a) / 2)) _)].
      1,3 : rewrite <- le_N_nat; apply N.div_le_mono; lia.
      apply (Nat.le_trans _
            (S (N.to_nat ((n + b) / 2) +
                nat_size (f (f (repeat f (N.to_nat ((n + b) / 2)) n)) - a)))
             _);
        omega. 
    + rewrite <- N.div2_div.
      destruct (n - a); [simpl in H; omega | induction p; trivial].
Qed.

Lemma bin_alpha_2_correct : forall n,
    bin_alpha 2 n = N.of_nat (inv_ack.alpha 2 (N.to_nat n)).
Proof.
  intro n. unfold bin_alpha. unfold to_N_func.
  remember (N.to_nat n) as m.
  replace (n - 2) with (N.of_nat (m - 2)) by lia.
  rewrite <- Nat2N.inj_div2. f_equal. clear Heqm. clear n.
  replace (inv_ack.alpha 2 m) with
    (countdown.countdown_to (inv_ack.alpha 1) 1 (inv_ack.alpha 1 m))
      by trivial.
  rewrite inv_ack.alpha_1.
  generalize (m - 2)%nat. clear m. intro n.
  assert (Nat.div2 n =
          countdown.countdown_to (fun n0 : nat => (n0 - 2)%nat) 1 n
          /\ Nat.div2 (S n) =
             countdown.countdown_to (fun n0 : nat => (n0 - 2)%nat) 1 (S n)).
  { induction n; split; trivial. apply IHn.
    destruct (countdown.countdown_recursion 1
               (fun n0 => (n0-2)%nat) (S(S n))) as [_ H].
    - split; intro m; omega.
    - rewrite H by omega. replace (S(S n) - 2)%nat with n by omega.
      simpl. f_equal. apply IHn. }
  apply H.
Qed.

(* 
 * Every bin_alpha level starting from 2 is strictly binary 
 * contracting above 1, so bin_countdown_to to 1 works 
 * properly for them. 
 *)
Theorem bin_alpha_contract_strict_above_1 : forall m,
    (2 <= m)%nat -> bin_contract_strict_above 1 (bin_alpha m).
Proof.
  destruct m as [|[|m]]; try omega; intro; clear H. induction m.
  - split; intro n; simpl; rewrite N.div2_div;
      [apply N.div_le_upper_bound|intro; apply N.div_le_mono]; lia.
  - rewrite bin_alpha_recursion; [| omega].
    apply (countdown_bin_contract _ _ _ IHm).
Qed.

Theorem bin_alpha_correct :
    forall m, bin_alpha m = to_N_func (inv_ack.alpha m).
Proof.
  induction m as [|[|[|m]]]; apply functional_extensionality;
    intro n; unfold to_N_func. 2: rewrite inv_ack.alpha_1.
  1,2: simpl; lia. 1: apply bin_alpha_2_correct.
  rewrite bin_alpha_recursion by omega. unfold compose.
  rewrite bin_countdown_correct by
      (apply bin_alpha_contract_strict_above_1; omega).
  rewrite IHm. rewrite <- nat_N_func_id.
  replace (N.to_nat 1) with 1%nat by trivial.
  unfold to_N_func. f_equal. rewrite Nat2N.id. trivial.
Qed.

Corollary bin_alpha_ackermann :
    forall m, upp_inv_rel (bin_alpha m) (bin_ackermann (N.of_nat m)).
Proof.
  intros m n p. rewrite <- (N2Nat.id n). rewrite bin_ackermann_correct.
  rewrite bin_alpha_correct. unfold to_N_func. rewrite <- le_nat_N.
  rewrite le_N_nat. repeat rewrite Nat2N.id.
  destruct (inv_ack.alpha_correct m) as [_ H]. apply H.
Qed.


(* ********* TWO PARAMETERS INVERSE ACKERMANN ************* *)

(* Two parameters Binary Inverse Ackerman worker function *)
Fixpoint two_params_bin_inv_ack_wkr (f : N -> N) (n k : N) (b : nat) : N :=
  match b with
  | 0%nat => 0
  | S b'  => if (n <=? k) then 0
              else let g := (bin_countdown_to f 1) in
                   N.succ (two_params_bin_inv_ack_wkr (compose g f) (g n) k b')
  end.

(* Two parameters Binary Inverse Ackermann function *)
Definition two_params_bin_inv_ack (m n : N) : N :=
  let n' := (N.log2_up n) in
    let m' := m / n in
      if (n' - 2 <=? m') then 1
        else if (N.div2 (n' - 2) <=? m') then 2
          else let f := (fun x => N.log2 (x + 2) - 2) in
            3 + two_params_bin_inv_ack_wkr f (f n') m' (nat_size n).

(* Correctness proofs begin here *)

(* Small helper lemma - alpha decreases by level *)
Lemma bin_alpha_decr_by_lvl :
    forall i n, bin_alpha (S i) n <= bin_alpha i n.
Proof.
  intros i n. repeat rewrite bin_alpha_correct.
  unfold to_N_func. rewrite <- le_nat_N.
  apply inv_ack.alpha_decr_by_lvl.
Qed.

(* Lemma about worker function's inner working *)
Lemma two_params_bin_inv_ack_wkr_intermediate :
    forall i n k b, k < bin_alpha (S (S i)) n -> (i <= b)%nat ->
      two_params_bin_inv_ack_wkr (bin_alpha 3) (bin_alpha 3 n) k b =
        N.of_nat i +
          two_params_bin_inv_ack_wkr
            (bin_alpha (S (S (S i)))) (bin_alpha (S (S (S i))) n) k (b - i).
Proof.
  induction i; intros n k b Hin Hib.
  - rewrite N.add_0_l. f_equal. omega.
  - rewrite IHi.
    2: apply (N.lt_le_trans _ (bin_alpha (S (S (S i))) n) _ Hin),
               bin_alpha_decr_by_lvl. 
    2: omega.
    unfold two_params_bin_inv_ack_wkr at 1.
    replace (b - i)%nat with (S (b - (S i)))%nat by omega.
    rewrite <- N.leb_gt in Hin. rewrite Hin.
    fold two_params_bin_inv_ack_wkr.
    rewrite <- N.add_succ_comm. f_equal. lia.
Qed.

(* Correctness theorem for two_params_bin_inv_ack worker *)
Theorem two_params_bin_inv_ack_upp_inv :
    forall m n, two_params_bin_inv_ack m n =
      1 + upp_inv (fun x => bin_ackermann (N.succ x) (m / n)) (N.log2_up n).
Proof.
  intros m n. unfold two_params_bin_inv_ack.
  remember (N.log2_up n) as b. remember (m / n) as a.
  fold (bin_alpha 2 b). fold (bin_alpha 1 b). fold (bin_alpha 3 b).
  assert (increasing (fun x : N => bin_ackermann (N.succ x) a)) as HF.
  { unfold increasing. intros x y.
    repeat rewrite bin_ackermann_correct.
    rewrite <- lt_nat_N. repeat rewrite N2Nat.inj_succ.
    rewrite lt_N_nat, Nat.succ_lt_mono. apply inv_ack.ack_incr_by_lvl.
  }
  assert (N.to_nat b <= nat_size n)%nat as Hb.
  { rewrite Heqb, nat_size_log2_up, <- le_N_nat.
    apply N.log2_up_le_mono. lia. }
  remember (nat_size n) as t. clear Heqb Heqa Heqt m n.
  remember (upp_inv (fun x : N => bin_ackermann (N.succ x) a) b) as q.
  assert (upp_inv_rel (upp_inv (fun x : N => bin_ackermann (N.succ x) a))
          (fun x : N => bin_ackermann (N.succ x) a)) as HfF.
  { apply upp_inv_correct, HF. }
  assert (bin_alpha (S (N.to_nat q)) b <= a) as Hq.
  { apply bin_alpha_ackermann.
    replace (N.of_nat _) with (N.succ q) by lia. apply HfF. lia. }
  remember (N.to_nat q) as p. replace q with (N.of_nat p) in * by lia.
  clear Heqp q. destruct p.
  - rewrite <- N.leb_le in Hq. rewrite Hq. trivial.
  - assert (a < bin_alpha (S p) b) as Hp.
    { rewrite N.lt_nge, (bin_alpha_ackermann (S p) a b), Nat2N.inj_succ.
      rewrite <- (HfF (N.of_nat p) b). lia. }
    destruct p.
    + rewrite <- N.leb_gt in Hp. rewrite Hp.
      rewrite <- N.leb_le in Hq. rewrite Hq. trivial.
    + assert (a < bin_alpha 2 b <= bin_alpha 1 b) as H12.
      { split; [|apply bin_alpha_decr_by_lvl].
        apply (N.lt_le_trans _ (bin_alpha (S (S p)) b) _ Hp).
        clear Hq Hp Heqq. induction p; [lia|].
        apply (N.le_trans _ (bin_alpha (S (S p)) b) _).
        apply bin_alpha_decr_by_lvl. apply IHp. }
      destruct H12 as [H2 H1]. apply (N.lt_le_trans _ _ _ H2) in H1.
      rewrite <- N.leb_gt in H1. rewrite <- N.leb_gt in H2.
      rewrite H1, H2. fold (bin_alpha 3).
      replace (1 + N.of_nat (S (S p))) with (3 + (N.of_nat p)) by lia.
      f_equal.
      rewrite (two_params_bin_inv_ack_wkr_intermediate p _ _ _ Hp).
      * rewrite <- N.add_0_r. f_equal.
        destruct (t - p)%nat; trivial. rewrite <- N.leb_le in Hq.
        unfold two_params_bin_inv_ack_wkr. rewrite Hq. trivial.
      * apply (Nat.le_trans _ (N.to_nat b) _); trivial.
        rewrite N.lt_nge, (bin_alpha_ackermann (S (S p)) a b),
          <- N.lt_nge, lt_N_nat in Hp.
        apply (Nat.le_trans _
                 (N.to_nat (bin_ackermann (N.of_nat (S (S p))) a)) _);
        [|lia]. rewrite bin_ackermann_correct. repeat rewrite Nat2N.id.
        clear Hq Heqq Hp. induction p; [omega|]. rewrite Nat.le_succ_l.
        apply (Nat.le_lt_trans _ _ _ IHp).
        apply inv_ack.ack_incr_by_lvl. omega.
Qed.



(* *********** INVERSE ACKERMANN FUNCTION ******************** *)

Fixpoint bin_inv_ack_wkr (f : N -> N) (n k : N) (b : nat) : N :=
  match b with
  | 0%nat  => k
  | S b' =>
    if n <=? k then k
    else let g := (bin_countdown_to f 1) in
         bin_inv_ack_wkr (compose g f) (g n) (N.succ k) b'
  end.

(* IMPORTANT *)
(* Definition by hard-coding the second bin_alpha level, runtime O(n) *)
Definition bin_inv_ack n :=
  if (n <=? 1) then 0
  else if (n <=? 3) then 1
       else if (n <=? 7) then 2
            else let f := (fun x => N.log2 (x + 2) - 2) in
                 bin_inv_ack_wkr f (f n) 3 (nat_size n).

(* Below we give a correctness proof of the above definition. *)

(* Intermediate lemmas about bin_inv_ack_wkr *)
Lemma bin_alpha_contr : forall i n,
    (S i < N.to_nat (bin_alpha (S i) n))%nat ->
    (i < N.to_nat (bin_alpha i n))%nat.
Proof.
  intros i n. specialize (bin_alpha_ackermann i (N.of_nat i) n).
  specialize (bin_alpha_ackermann (S i) (N.of_nat (S i)) n).
  specialize (diag_ack_incr (N.of_nat i) (N.of_nat (S i))). lia.
Qed.

Lemma bin_inv_ack_wkr_intermediate : forall i n b,
    (S (S i) < N.to_nat (bin_alpha (S (S i)) n))%nat ->
    (S (S i) < b)%nat ->
    bin_inv_ack_wkr (bin_alpha 3) (bin_alpha 3 n) 3 b =
    bin_inv_ack_wkr (bin_alpha (S (S (S i))))
                    (bin_alpha (S (S (S i))) n) (N.of_nat (S (S (S i)))) (b - i).
Proof.
  induction i; intros n b Hn Hib; symmetry;
    [f_equal; omega | rewrite bin_alpha_recursion by omega].
  rewrite IHi; [replace (b - i)%nat with (S (b - S i))%nat by omega
               |apply (bin_alpha_contr _ _ Hn) | omega].
  rewrite lt_nat_N, N2Nat.id in Hn. rewrite <- N.leb_gt in Hn.
  unfold bin_inv_ack_wkr at 2. rewrite Hn. rewrite <- Nat2N.inj_succ. trivial.
Qed.

(* Proof that bin_inv_ack_wkr is correct given sufficient budget *)
Lemma bin_inv_ack_wkr_sufficient :
  forall n b,
    (8 <= n <= bin_ackermann b b) ->
      bin_inv_ack_wkr (bin_alpha 3) (bin_alpha 3 n) 3 (N.to_nat b)
        = upp_inv (fun m => bin_ackermann m m) n.
Proof.
  assert (Hincr := diag_ack_incr).
  assert (Hack := upp_inv_correct _ Hincr).
  unfold upp_inv_rel in Hack. intros n b [Hn Hnb].
  remember (N.to_nat (upp_inv (fun m : N => bin_ackermann m m) n)) as p.
  rewrite <- (Nat2N.id p) in Heqp. apply N2Nat.inj in Heqp.
  assert (n <= bin_ackermann (N.of_nat p) (N.of_nat p)) as Hp0 by
        (apply Hack; lia).
  destruct p as [|[|[|p]]].
  1,2,3 : unfold N.of_nat in Heqp; unfold bin_ackermann in Hp0;
    simpl in Hp0; lia.
  assert (bin_ackermann (N.of_nat (S (S p))) (N.of_nat (S (S p))) < n)
      as Hp1
      by (rewrite N.lt_nge; rewrite <- Hack; lia).
  assert (S (S p) < N.to_nat b)%nat as Hpb.
  { rewrite Nat.lt_nge. intro Hc.
    inversion Hc as [Hc0|Hc1]. rewrite <- Hc0 in Hp1.
    rewrite N2Nat.id in Hp1. lia.
    rewrite prelims.lt_S_le, lt_nat_N, N2Nat.id in H.
    apply Hincr in H. lia. }
  rewrite (bin_inv_ack_wkr_intermediate p).
  - replace (N.to_nat b - p)%nat with
      (S (N.to_nat b - S p))%nat by omega.
    unfold bin_inv_ack_wkr.
    replace (bin_alpha (S (S (S p))) n <=? N.of_nat (S (S (S p))))
      with true;
        trivial.
    symmetry. rewrite N.leb_le.
    rewrite (bin_alpha_ackermann (S (S (S p))) _ _). apply Hp0.
  - rewrite lt_nat_N. rewrite N2Nat.id. rewrite N.lt_nge.
    rewrite (bin_alpha_ackermann (S (S p)) _ _). lia.
  - apply Hpb.
Qed.

(* Helper lemmas regarding ackermann at level 3 *)
Open Scope nat_scope.

Lemma ack_2 : forall n, repeater.ackermann 2 n = 2 * n + 3.
Proof.
  induction n; trivial.
  replace (repeater.ackermann 2 (S n)) with
    (repeater.ackermann 1 (repeater.ackermann 2 n)) by trivial.
  rewrite IHn. rewrite inv_ack.ack_1. omega.
Qed.

Lemma ack_3 : forall n, repeater.ackermann 3 n = 2 ^ (n + 3) - 3.
Proof.
  induction n; trivial.
  replace (repeater.ackermann 3 (S n)) with
    (repeater.ackermann 2 (repeater.ackermann 3 n)) by trivial.
  rewrite IHn. rewrite ack_2.
  replace (S n + 3) with (S (n + 3)) by trivial.
  replace (2 ^ (S (n+3))) with (2 * 2 ^ (n+3)) by trivial.
  assert (3 <= 2 ^ (n+3)).
  { apply (Nat.le_trans _ (2^3) _); [simpl; omega|].
    apply Nat.pow_le_mono_r; omega. } omega.
Qed.

Close Scope nat_scope.

(* Proof that bin_inv_ack is correct *)
Theorem bin_inv_ack_correct : bin_inv_ack = to_N_func (inv_ack.inv_ack).
Proof.
  apply functional_extensionality. intro n.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/
          n = 5 \/ n = 6 \/ n = 7 \/ 8 <= n) as Hn by lia.
  repeat destruct Hn as [Hn|Hn]; try rewrite Hn; trivial.
  unfold bin_inv_ack.
  replace (n <=? 1) with false by (symmetry; rewrite N.leb_gt; lia).
  replace (n <=? 3) with false by (symmetry; rewrite N.leb_gt; lia).
  replace (n <=? 7) with false by (symmetry; rewrite N.leb_gt; lia).
  rewrite <- (Nat2N.id (nat_size n)). fold (bin_alpha 3).
  fold (bin_alpha 3 n). rewrite bin_inv_ack_wkr_sufficient.
  - unfold upp_inv. f_equal. rewrite <- to_nat_diag_ack. symmetry.
    apply inverse.upp_inv_unique. apply inv_ack.diag_ack_incr.
    apply inv_ack.inv_ack_correct.
  - split; [lia|]. rewrite bin_ackermann_correct. rewrite Nat2N.id.
    apply (N.le_trans _ (N.of_nat (repeater.ackermann 3 (nat_size n))) _).
    + clear Hn. rewrite le_N_nat. rewrite Nat2N.id.
      rewrite ack_3. destruct n; simpl; [lia|].
      induction p; [| |simpl; lia]; simpl;
        [rewrite Pos2Nat.inj_xI|rewrite Pos2Nat.inj_xO];
        assert (3 <=
          2 ^ ((fix nat_pos_size (x : positive) : nat :=
                 match x with
                 | (y~1)%positive | (y~0)%positive => S (nat_pos_size y)
                 | 1%positive => 1
                 end) p + 3))%nat
          by (apply (Nat.le_trans _ (2^3) _); [simpl; omega|];
              apply Nat.pow_le_mono_r; omega); omega.
    + rewrite <- le_nat_N. rewrite Nat.le_ngt.
      assert (H := inv_ack.ack_incr_by_lvl (nat_size n)).
      apply (increasing_expanding.incr_twoways _ (nat_size n) 3) in H.
      simpl in *. rewrite <- H. apply nat_size_incr in Hn.
      simpl in Hn. omega.
Qed.

(* Please see inv_ack_test.v for a demonstration of the runtime of bin_inv_ack *)