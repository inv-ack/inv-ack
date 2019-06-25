Require Import Omega.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.
Require Import inverse.

(*
==================================================================================
***************************** SECTION 5: COUNTDOWN  *****************************
==================================================================================
 *)

(* 
 * Earlier we explored how to compute inverse of a function's repeater 
 * solely from the function's own inverse, without directly computing the 
 * repeater itself. The first lemma addresses this.
 *
 * We base the definition of "contractions" and "countdown" on this observation.
 * We also give a computation for countdown and prove several useful results 
 * about it. 
 * 
 * The inverse of (repeater_from a F) is the minimum number of applications
 * of (inverse F) to the input to get a result less than or equal to a.
 *  This serves as motivation to contractions and countdown 
 *)
Lemma upp_inv_repeater :
  forall a f F f',
    upp_inv_rel f F ->
    upp_inv_rel f' (repeater_from F a) ->
    (forall n m, f' n <= m <-> repeat f m n <= a).
Proof.
  intros a f F f' HfF Hf'F n m.
  rewrite (Hf'F m n). rewrite repeater_from_repeat.
  symmetry. apply (upp_inv_repeat m f F HfF a n).
Qed.


(* ****** CONTRACTIONS ****** *)

(* Definition of non-strict contractions *)
Definition contracting (f : nat -> nat) : Prop :=
  forall n, f n <= n.

(* Definition of strict expansion *)
Definition contract_strict_above (a : nat) (f : nat -> nat) : Prop :=
  contracting f /\ (forall n, a < n -> f n < n).

(* Upper inverses of expansions are contractions *)
Theorem upp_inv_expand_contract :
    forall f F, expanding F -> upp_inv_rel f F -> contracting f.
Proof.
  intros f F HF HfF n. rewrite (HfF n n). apply HF.
Qed.

(* Upper inverses of "strict-from-a expansions" themselves contract above a *)
Theorem upp_inv_expand_contract_strict :
  forall a f F,
    expand_strict_from a F ->
      upp_inv_rel f F -> contract_strict_above a f.
Proof.
  intros a f F HF HfF. destruct HF as [HF HaF].
  split.
  1: apply (upp_inv_expand_contract _ F HF HfF). 
  intro n. destruct n; [omega|]. repeat rewrite <- lt_S_le.
  rewrite (HfF n _). apply HaF.
Qed.


(* ****** PROPERTIES OF CONTRACTIONS *******)

(* Repeat of contractions make the result smaller *)
Lemma repeat_contract :
  forall f n k l,
    contracting f -> k <= l -> repeat f l n <= repeat f k n.
Proof.
  intros f n k l Hf Hkl. induction l; inversion Hkl; trivial.
  apply IHl in H0.
  apply (Nat.le_trans _ (repeat f l n) _); [apply Hf | apply H0].
Qed.

(* Stricter version of the above *)
Lemma repeat_contract_strict :
  forall a f n k,
    contract_strict_above a f ->
    S a <= repeat f k n -> (S k) + repeat f (S k) n <= n.
Proof.
  intros a f n k Hf Han. destruct Hf as [Hf Haf]. induction k.
  1: simpl in Han; simpl; apply Haf in Han; omega. 
  apply (Nat.le_trans _ (S k + repeat f (S k) n) _).
  - apply Haf in Han. simpl in Han; simpl. omega.
  - assert (S a <= repeat f k n) as Han0.
    { apply (Nat.le_trans _ (repeat f (S k) n) _); [apply Han|].
      apply Haf in Han. simpl. apply Hf. }
    apply IHk in Han0. omega.
Qed.



(* ****** COUNTDOWN ****** *)

(* Repeats "f" "k" times over, or until we go below "a".
   Outputs "min(k, min{l : repeat f l n <= a})" *)
Fixpoint cdn_wkr (f : nat -> nat) (a : nat)  (n k : nat) : nat :=
  match k with
  | 0    => 0
  | S k' => if (n <=? a) then 0 else
             S (cdn_wkr f a (f n) k')
  end.

(* Actual defintion. We give the worker a budget of "n" steps, which
   guarantees that it reaches below "a" before terminating *)
Definition countdown_to f a n := cdn_wkr f a n n.



(* ****** COUNTDOWN CORRECTNESS THEOREMS ****** *)

(* INITIAL VALUE THEOREM
   Basically countdown returns 0 if "n" is already below "a" *)
Theorem countdown_init :
  forall a f n k, n <= a -> cdn_wkr f a n k = 0.
Proof.
  intros a f n k Hna.
  destruct k; trivial.
  rewrite <- Nat.leb_le in Hna.
  unfold cdn_wkr. rewrite Hna; trivial.
Qed.

(* EXISTENCE OF COUNTDOWN VALUE LEMMA *)
(* Basically the existence of the countdown value for strict contractions
   It asserts there is a minimum "l" for which repeating "f" "l" times from "n"
   will give a result less than or equal to "a" *)
Lemma repeat_contract_strict_threshold :
  forall a f n,
    contract_strict_above a f -> a < n ->
    exists l, (S l) <= n /\ repeat f (S l) n <= a < repeat f l n.
Proof.
  intros a f n Hf Han. destruct Hf as [Hf Haf].
  remember (n - a) as m.
  destruct m; [omega|].
  assert (forall b, (a <= b) -> f (S b) <= b) as Ha
      by (intros b Hab; rewrite le_S_n_m; apply Haf; omega).
  generalize dependent a.
  induction m.
  - intros. exists 0.
    simpl. split; [|split];
    [|replace n with (S a) by omega; apply Ha|]; omega.
  - intros. destruct (IHm (S a)); try omega.
    + intros p Hp. apply Haf. omega.
    + intros b Hab. apply Ha. omega.
    + destruct H as [H0 H1]. destruct H1 as [Hl Hr]. inversion Hl.
      2: exists x; split; [apply H0 | omega].
      exists (S x). simpl. rewrite H1. split.
      2: split; [apply Ha|]; omega.
      apply (Nat.le_trans _ (S x + (repeat f (S x) n)) _);
                  [simpl; rewrite H1; omega|].
      apply (repeat_contract_strict a f n x);
      [split; assumption | omega].
Qed.


(* INTERMEDIATE STATE LEMMA
   Similar to the general recursion formula for "countdown_recurse_rel" *)
Theorem countdown_intermediate :
  forall a f n k i,
    contracting f ->
    S i <= k ->
    a < repeat f i n ->
    cdn_wkr f a n k =
    (S i) + cdn_wkr f a (repeat f (S i) n) (k - (S i)).
Proof.
  assert (forall a f n k,
             contracting f -> 1 <= k -> a < n ->
             cdn_wkr f a n k =
             1 + cdn_wkr f a (f n) (k - 1) ) as case_0.
  { simpl. intros a f n k Hf Hk Ha. destruct k; [omega|].
    replace (S k - 1) with k by omega. unfold cdn_wkr.
    rewrite Nat.lt_nge, <- Nat.leb_nle in Ha. rewrite Ha. trivial.
  }
  intros a f n k i Hf Hik Hai.
  induction i; [simpl; apply case_0; trivial|].
  rewrite IHi; [|omega|].
  2: apply (Nat.le_trans _ (repeat f (S i) n) _);
     [trivial | apply Hf].
  simpl. remember (f (repeat f i n)) as m. remember (k - S i) as l.
  replace (k - S(S i)) with (l - 1) by omega.
  rewrite case_0; [omega | trivial | omega|].
  simpl in Hai. rewrite Heqm. trivial.
Qed.

(* COUNTDOWN VS REPEAT THEOREM
   Correctness theorem for this countdown defintion *)
Theorem countdown_repeat :
  forall a f n k,
    contract_strict_above a f ->
      countdown_to f a n <= k <-> repeat f k n <= a.
Proof.
  intros a f n k Haf. inversion Haf as [Hf _].
  unfold countdown_to; split.
  - intro. rewrite not_lt. intro.
    rewrite (countdown_intermediate a f n n k Hf) in H;
      [omega | trivial..].
    apply (Nat.le_trans _ (S k + (repeat f (S k) n)) _); [omega|].
    apply (repeat_contract_strict a f n k Haf H0). 
  - intro. destruct k.
    1: simpl in H; rewrite (countdown_init a f n); omega; apply H. 
    remember (n - a) as m.
    destruct m; [rewrite countdown_init; omega|]. 
    destruct (repeat_contract_strict_threshold a f n Haf); [omega|].
    destruct H0 as [Hx0 [Hxl Hxr]].
    assert (cdn_wkr f a n n = S x) as Hx.
    { rewrite (countdown_intermediate a f n n x); trivial.
      rewrite countdown_init; [omega | trivial].
    }
    rewrite Hx. apply not_le. intro.
    apply (repeat_contract f n (S k) x) in H0; [omega | apply Hf].
Qed.

(* RECURSION FOR CONTRACTORS THEOREM *)
Theorem countdown_recursion :
  forall a f n,
    contract_strict_above a f ->
    (n <= a -> countdown_to f a n = 0) /\
    (a < n -> countdown_to f a n = S (countdown_to f a (f n))).
Proof.
  intros a f n Hf. split.
  1: intro Han; unfold countdown_to; apply countdown_init; apply Han.
  intro Han.
  assert (countdown_to f a n <= S (countdown_to f a (f n))) as G1.
  { rewrite countdown_repeat by apply Hf.
    rewrite repeat_S_comm.
    rewrite <- countdown_repeat by apply Hf.
    trivial. }
  assert (1 <= countdown_to f a n) as G0.
  { rewrite le_lt_S. rewrite <- not_le.
    rewrite countdown_repeat by apply Hf.
    simpl. omega. }
  assert (countdown_to f a (f n) <= countdown_to f a n - 1).
  { rewrite countdown_repeat by apply Hf.
    rewrite <- repeat_S_comm.
    replace (S (countdown_to f a n - 1)) with
              (countdown_to f a n) by omega.
    rewrite <- countdown_repeat by apply Hf. trivial. }
  omega.
Qed.

Corollary countdown_antirecursion :
  forall a f n,
    contract_strict_above a f ->
      countdown_to f a (f n) = countdown_to f a n - 1.
Proof.
  intros a f n Haf.
  assert (H := Haf).
  destruct (Nat.lt_ge_cases a n) as [Han | Han];
    apply (countdown_recursion a f n) in H.
  1: apply H in Han; omega.
  assert (f n <= a) as Hafn
      by (apply (Nat.le_trans _ n _); [apply Haf | apply Han]).
  apply (countdown_recursion a f (f n)) in Haf.
  apply Haf in Hafn. apply H in Han. omega.
Qed.


(* STRICT CONTRACTIVENESS PRESERVATION THEOREM *)
Theorem countdown_contract_strict :
  forall a f t,
    1 <= a ->
    contract_strict_above a f ->
    contract_strict_above t (countdown_to f a).
Proof.
  intros a f t Ha Haf. split.
  - intro n. rewrite countdown_repeat by apply Haf.
    rewrite not_lt. intro.
    apply repeat_contract_strict in H; [omega | apply Haf..].
  - intros n Hn. destruct n; [omega|]. rewrite <- lt_S_le.
    rewrite countdown_repeat by apply Haf. destruct n;  trivial.
    remember (repeat f n (S (S n)) - a) as m. destruct m.
    1: apply (Nat.le_trans _ (repeat f n (S (S n))) _);
       [apply Haf | omega]. 
    assert (S n + repeat f (S n) (S (S n)) <= (S n) + a)
      by (apply (Nat.le_trans _ (S (S n)) _);
          [apply (repeat_contract_strict a _ _ _ Haf)|]; omega).
    omega.
Qed.

(* ****** COUNTDOWN - REPEATER - INVERSE PRESERVATION **************** *)

(* 
 * This theorem is important. 
 * It says that countdown and repeater will preserve the 
 * upper inverse relation on their respective results.
 * We need this to prove the correctness of inverse hyperoperations and
 *  inverse Ackermann towers built with countdown later on 
 *)
Theorem countdown_repeater_upp_inverse :
  forall a f F,
    expand_strict_from a F ->
    upp_inv_rel f F ->
    upp_inv_rel (countdown_to f a) (repeater_from F a).
Proof.
  intros a f F HaF HfF n N.
  apply (upp_inv_expand_contract_strict a f F) in HaF; [|trivial].
  rewrite repeater_from_repeat. apply (upp_inv_repeat n _ _) in HfF.
  rewrite <- (HfF a N). apply countdown_repeat. trivial.
Qed.