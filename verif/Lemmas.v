Require Import ZArith.
Require Import Reals.
Require Import BuiltIn.
Require Import int.Int.
Require Import int.Abs.
Require Import int.ComputerDivision.
Require Import real.Real.
Require Import real.RealInfix.
Require Import real.FromInt.
Require Import map.Map.
Require Import Qedlib.
Require Import Qed.
Require Import Cint.
Require Import Bits.
Require Import Zbits.
Require Import Cbits.

Open Local Scope Z_scope.

Lemma mult_simplification:
  forall (i_1 i : Z),
  ((0 < i)%Z) ->
  ((0 <= i_1)%Z) ->
  ((((Cdiv (i * i_1) i)) = i_1)%Z).
Proof.
  intros. destruct(Cdiv_cases (i*i_1) i) as [HH _].
  now rewrite HH, Z.mul_comm, Z_div_mult 
    by (try apply Z.le_ge; auto with zarith).
Qed.

(* lemmas used to prove gcr *)
Lemma lsl_to_pow2:
  forall (a b : Z),
  (0 <= b)%Z -> lsl a b = (a * 2 ^ b)%Z.
Proof.
  intros.
  rewrite lsl_pos.
  unfold lsl_def.
  rewrite Zabs2Nat.abs_nat_nonneg.
  rewrite lsl_arithmetic_shift.
  unfold lsl_arithmetic_def.
  rewrite two_power_nat_equiv.
  rewrite Z2Nat.id.
  trivial.
  assumption.
  assumption.
  assumption.
Qed.

Lemma lsl_left_bound:
  forall (a b c : Z),
  (a <= c)%Z -> (0 <= b)%Z -> (lsl a b <= lsl c b)%Z.
Proof.
  intros.
  rewrite lsl_to_pow2.
  rewrite lsl_to_pow2.
  apply Zmult_le_compat_r.
  assumption.
  apply Z.pow_nonneg.
  auto with zarith.
  assumption.
  assumption.
Qed.

Lemma lsl_right_bound:
  forall (a b c : Z),
  (0 <= a)%Z -> (0 <= b <= c)%Z -> (lsl a b <= lsl a c)%Z.
Proof.
  intros.
  rewrite lsl_to_pow2.
  rewrite lsl_to_pow2.
  apply Zmult_le_compat_l.
  apply Z.pow_le_mono_r.
  auto with zarith.
  apply H0.
  apply H.
  auto with zarith.
  apply H0.
Qed.

