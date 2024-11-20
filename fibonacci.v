(*
  Sanjay Adhith
  <sanjay.adhith@u.nus.edu.sg>
  November 2024
  Singapore
 *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Nat Arith Bool Lia.
    
(* *** *)

(* The Fibonacci implementation we want to work with *)

Fixpoint fib (n : nat) : nat :=
  match n with
    0 =>
    0
  | S n' =>
    match n' with
      0 =>
      1
    | S n'' =>
      fib n' + fib n''
    end
  end.

Lemma fold_unfold_fib_O :
  fib O =
    0.
Proof.
  fold_unfold_tactic fib.
Qed.

Lemma fold_unfold_fib_S :
  forall n' : nat,
    fib (S n') =
    match n' with
      0 =>
      1
    | S n'' =>
      fib n' + fib n''
    end.
Proof.
  fold_unfold_tactic fib.
Qed.

(* Okay, so I want to find out when F_n is even, and
   when F_n is odd. *)

Compute fib 1.
(* 1 - odd*)
Compute fib 2.
(* 1 - odd*)
Compute fib 3.
(* 2 - even*)
Compute fib 4.
(* 3 - odd*)
Compute fib 5.
(* 5 - odd*)
Compute fib 6.
(* 8 - even*)
Compute fib 7.
(* 13 - odd*)
Compute fib 8.
(* 21 - odd*)
Compute fib 9.
(* 34 - odd*)

(*

   Mabye some tabular visualisation will help. Below,
   'o' refers to an odd number while 'e' refers to an
    even number.

        F_n 1  1  2  3  5  8  13 21 34
          n 1  2  3  4  5  6  7  8  9
     parity o  o  e  o  o  e  o  o  e

   Okay. The pattern that is emerging is that if
   n is a multiple of three, then F_n must be even.

   So I would formally state that F_n is even iff
   n is a multiple of three.

   For the backwards implication, I could try to
   first prove the auxillary lemma that

   F_nk is a multiple of F_n by induction and
   then be done with it.

   The forwards implication is not easy.
   and I don't have a proof sketch yet. 
*)

(* Even numbers from LPP *)

Fixpoint evenp (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    negb (evenp n')
  end.

Lemma fold_unfold_evenp_0:
  evenp 0 = true.
Proof.
  fold_unfold_tactic evenp.
Qed.

Lemma fold_unfold_evenp_S:
  forall n' : nat,
    evenp (S n') =
    negb (evenp n').
Proof.
  fold_unfold_tactic evenp.
Qed.

Corollary fold_unfold_evenp_SS :
  forall n : nat,
    evenp (S (S n)) = evenp n.
Proof.
  intro n.
  rewrite ->2 fold_unfold_evenp_S.
  exact (negb_involutive (evenp n)).
Qed.


Corollary successor_flips_evenness:
  forall n : nat,
    evenp n = negb (evenp (S n)).
Proof.
  intro n.
  rewrite -> (fold_unfold_evenp_S n).
  rewrite -> negb_involutive.
  reflexivity.

  Restart.
  intro n.
  rewrite <- fold_unfold_evenp_S.
  exact (eq_sym (fold_unfold_evenp_SS n)).
Qed.

Lemma SO_is_not_even :
  evenp 1 = false.
Proof.
  rewrite -> fold_unfold_evenp_S.
  rewrite -> fold_unfold_evenp_0.
  Search (negb true).
  unfold negb.
  reflexivity.
Qed.

Lemma twice_S :
  forall n : nat,
    S (S (2 * n)) = 2 * S n.
Proof.
  intro n.
  ring.
Qed.

Lemma thrice_S :
  forall n : nat,
    S (S (S (3 * n))) = 3 * S n.
Proof.
  intro n.
  ring.
Qed.

Lemma twice :
  forall x : nat,
    x + x = 2 * x.
Proof.
  intro x.
  ring.
Qed.

Lemma completeness_of_evenp:
  forall k : nat,
    evenp (2 * k) = true.
Proof.
  intro k.
  induction k as [ | k' IHk'].

  * rewrite -> Nat.mul_0_r.
    exact fold_unfold_evenp_0.

  * rewrite <- twice_S.
    rewrite -> fold_unfold_evenp_SS.
    exact IHk'.
Qed.

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall k : nat, P k -> P (S k) -> P (S (S k))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert (H_both : P n /\ P (S n)).
  { induction n as [ | n' [IHn' IHSn']].
    - Check (conj H_P0 H_P1).
      exact (conj H_P0 H_P1).
    - Check (H_PSS n' IHn' IHSn').
      Check (conj IHSn' (H_PSS n' IHn' IHSn')).
      exact (conj IHSn' (H_PSS n' IHn' IHSn')).
  }
  destruct H_both as [ly _].
  exact ly.
Qed.  

Lemma soundness_of_evenp:
  forall n : nat,
    evenp n = true ->
     exists k : nat, 
         n = 2 * k.
Proof.
  intros n.
  induction n as [ | | n'' IHn'' IHSn''] using nat_ind2.

  * intros _.
    exists 0.
    ring.

  * rewrite -> SO_is_not_even.
    intro H_absurd.
    discriminate.

  * rewrite -> fold_unfold_evenp_SS.
    intros H_n''.
    Check (IHn'' H_n'').
    destruct (IHn'' H_n'') as [k' H_k'].
    rewrite -> H_k'.
    rewrite -> twice_S.
    exists (S k').
    reflexivity.
Qed.      

Lemma nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    (forall n : nat, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n)))) ->
    forall n : nat, P n.
Proof.
  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (H3 : P n /\ P (S n) /\ P (S (S n))).
  { induction n as [ | n' [IHn' [IHSn' IHSSn']]].
    - exact (conj H_P0 (conj H_P1 H_P2)).
    - Check (H_PSSS n' IHn' IHSn' IHSSn').
      exact (conj IHSn' (conj IHSSn' (H_PSSS n' IHn' IHSn' IHSSn'))).
  }
  destruct H3 as [ly _].
  exact ly.
Qed.

Lemma periodicity_of_even:
    forall n k2 : nat,
          fib (3*n) = 2 * k2 ->
      (exists k3 : nat,
          fib (S (S (S (3*n)))) = 2 * k3).
Proof.
  intros n k2 H_k2.
  rewrite -> fold_unfold_fib_S.
  rewrite -> fold_unfold_fib_S.
  rewrite -> H_k2.
  Search (_ + _ + _ = _ + _ + _).
  rewrite -> Nat.add_shuffle0.
  rewrite -> twice.
  rewrite <- Nat.mul_add_distr_l.
  exists (fib (S (3 * n)) + k2).
  reflexivity.
Qed.

(*
  Let me proving something easier,
  if I start with something even, then
  moving three steps down the line
  brings me somewhere even.
*)
     
Lemma shifting_by_threes:
  forall n k2: nat,
    S (S (S n)) = 3 * k2 ->
    (exists k3 : nat,
        n = 3 * k3).

Proof.
  intros n [ | k2'] H_k2.

  - rewrite -> Nat.mul_0_r in H_k2.
    discriminate.

  - rewrite <- thrice_S in H_k2.
    injection H_k2 as H_k2'.
    exists k2'.
    rewrite -> H_k2'.
    ring.
Qed.    
    
  
Lemma about_the_backwards_implication:
  forall n k3: nat,
      n = 3 * k3 ->
  exists k2 : nat,
      fib n = 2 * k2.
Proof.
  intros n.
  induction n as [ | | | n'' IHn' IHSn'' IHSSm''] using nat_ind3.
  intros k3 H_k3.
  
  * rewrite -> fold_unfold_fib_O.
    exists 0.
    ring.

  * case k3 as [ | k3'].

    - intros H_absurd.
      rewrite -> Nat.mul_0_r in H_absurd.
      discriminate.

    - intros H_absurd.
      rewrite <- thrice_S in H_absurd.
      discriminate.
      
  * case k3 as [ | k3'].

    - intros H_absurd.
      rewrite -> Nat.mul_0_r in H_absurd.
      discriminate.

    - intros H_absurd.
      rewrite <- thrice_S in H_absurd.
      discriminate.

  * rewrite ->2 fold_unfold_fib_S.
    rewrite -> Nat.add_shuffle0.
    rewrite -> twice.
    intros k3 H_up_three.
    pose (shifting_by_threes n'' k3 H_up_three) as H_down_three.
    destruct H_down_three as [k3' H_down_three].
    pose (IHn' k3' H_down_three) as IHn'_down.
    destruct IHn'_down as [k2' IHn'_down].
    rewrite -> IHn'_down.
    exists (fib (S n'') + k2').
    rewrite -> Nat.mul_add_distr_l.
    reflexivity.
Qed.    
    
Lemma about_sum_of_even_numbers:
  forall a b c : nat,
    2*a + b = 2*c ->
      exists k : nat,
          b = 2 * k.

Proof.
  intros a b c.
  revert b.

  induction b as [ | b'].

  * intros H_sum.
    exists 0.
    ring.

  * intros H_IHb'.
    exists (c - a).
    Search (_ * (_ - _)).
    rewrite -> Nat.mul_sub_distr_l.
    rewrite <- H_IHb'.
    rewrite -> Nat.add_comm.
    rewrite -> Nat.add_sub.
    reflexivity.
Qed.
    
Lemma about_the_forwards_implication:
  forall n k2 : nat,
      fib n = 2 * k2 ->
    exists k3 : nat,
      n = 3 * k3.
Proof.
  intros n.
  
  induction n as [ | | | n'' IHn' IHSn'' IHSSm''] using nat_ind3;   intros k2 H_k2.

  * exists 0.
    ring.

  * rewrite -> fold_unfold_fib_S in H_k2.
    case k2 as [ | k2'].

   - rewrite -> Nat.mul_0_r in H_k2.
     discriminate.

   - rewrite <- twice_S in H_k2.
     discriminate.

  * rewrite ->2 fold_unfold_fib_S in H_k2.
    rewrite -> fold_unfold_fib_O in H_k2.
    rewrite -> Nat.add_0_r in H_k2.
    case k2 as [ | k2'].

   - rewrite -> Nat.mul_0_r in H_k2.
     discriminate.

   - rewrite <- twice_S in H_k2.
     discriminate.

  * rewrite ->2 fold_unfold_fib_S in H_k2.
    rewrite -> Nat.add_shuffle0 in H_k2.
    rewrite -> twice in H_k2.
    pose (about_sum_of_even_numbers
             (fib (S n''))
             (fib n'')
             k2
             H_k2
          ) as H_n''.

    destruct H_n'' as [k1 H_n''].
    pose (IHn' k1 H_n'') as H_n''_is_multiple_of_3.
    destruct H_n''_is_multiple_of_3 as [k3' H_n''_is_multiple_of_3].

   - exists (S (k3')).
     rewrite -> H_n''_is_multiple_of_3.
     rewrite -> thrice_S.
     reflexivity.
Qed.      
