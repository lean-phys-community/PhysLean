/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

import QuantumInfo.Finite.ProductPower
public import QuantumInfo.ClassicalInfo.Hellinger
public import QuantumInfo.Finite.AxiomatizedEntropy.Bounds
public import QuantumInfo.Finite.POVM

@[expose] public section

/-! # Faithfulness of nontrivial axiomatized relative entropies

This file contains the Tomamichel-style proof that a nontrivial axiomatized relative entropy is
faithful, together with the binary-channel and finite classical testing lemmas used by the proof.
-/

noncomputable section
universe u

open ComplexOrder
open scoped NNReal
open scoped ENNReal
open scoped Kronecker
open scoped HermitianMat
open ProbDistribution

variable (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → HermitianMat d ℂ → ℝ≥0∞)

namespace RelEntropy

variable {d : Type u} [Fintype d] [DecidableEq d]

/-- The output of Tomamichel's preparation channel on the first binary point. -/
private def binaryPrepOne (γ ω : MState d) (s t : ℝ) (hden : 0 < 1 - s - t)
    (h : t • γ.M ≤ (1 - s) • ω.M) : MState d where
  M := (1 - s - t)⁻¹ • ((1 - s) • ω.M - t • γ.M)
  nonneg := smul_nonneg (inv_nonneg.mpr hden.le) (sub_nonneg.mpr h)
  tr := by
    simpa [HermitianMat.trace_smul, HermitianMat.trace_sub, γ.tr, ω.tr] using
      inv_mul_cancel₀ hden.ne'

/-- The output of Tomamichel's preparation channel on the second binary point. -/
private def binaryPrepZero (γ ω : MState d) (s t : ℝ) (hden : 0 < 1 - s - t)
    (h : s • ω.M ≤ (1 - t) • γ.M) : MState d where
  M := (1 - s - t)⁻¹ • ((1 - t) • γ.M - s • ω.M)
  nonneg := smul_nonneg (inv_nonneg.mpr hden.le) (sub_nonneg.mpr h)
  tr := by
    simp [HermitianMat.trace_smul, HermitianMat.trace_sub, γ.tr, ω.tr]
    field_simp [hden.ne']
    ring_nf

/-- A binary coin lifted to the working universe. -/
private def uliftCoin (p : Prob) : ProbDistribution (ULift.{u} (Fin 2)) :=
  (ProbDistribution.congr Equiv.ulift.symm) (.coin p)

private theorem cqPrepare_apply_uliftCoin (τ : ULift (Fin 2) → MState d) (p : Prob) :
    (CPTPMap.cqPrepare (d := d) τ (MState.ofClassical (uliftCoin p))).m =
      (p : ℝ) • (τ (ULift.up (0 : Fin 2))).m +
        ((1 - p : Prob) : ℝ) • (τ (ULift.up (1 : Fin 2))).m := by
  rw [CPTPMap.cqPrepare_apply_ofClassical (d := d) τ (uliftCoin p)]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  have hsum :
      (∑ x : ULift (Fin 2), ↑↑((uliftCoin p) x) * (τ x).m i j) =
        ∑ y : Fin 2, ↑↑((ProbDistribution.coin p) y) * (τ (ULift.up y)).m i j := by
    simpa [uliftCoin, ProbDistribution.congr_apply] using
      (Equiv.sum_comp (Equiv.ulift : ULift (Fin 2) ≃ Fin 2)
        (fun y : Fin 2 => ↑↑((ProbDistribution.coin p) y) * (τ (ULift.up y)).m i j))
  rw [hsum]
  simp [Fin.sum_univ_two]

private def binaryClassicalPostprocess (a b : Prob) :
    CPTPMap (ULift (Fin 2)) (ULift (Fin 2)) :=
  let τ : ULift (Fin 2) → MState (ULift (Fin 2)) := fun i =>
    if i = ULift.up (0 : Fin 2) then MState.ofClassical (uliftCoin a)
    else MState.ofClassical (uliftCoin b)
  CPTPMap.cqPrepare (d := ULift (Fin 2)) τ

private theorem binaryClassicalPostprocess_apply (a b p : Prob) :
    binaryClassicalPostprocess a b (MState.ofClassical (uliftCoin p)) =
      MState.ofClassical (uliftCoin (Prob.mix p a b)) := by
  apply MState.ext_m
  change (CPTPMap.cqPrepare (d := ULift (Fin 2))
      (fun i : ULift (Fin 2) =>
        if i = ULift.up (0 : Fin 2) then MState.ofClassical (uliftCoin a)
        else MState.ofClassical (uliftCoin b))
      (MState.ofClassical (uliftCoin p))).m =
    (MState.ofClassical (uliftCoin (Prob.mix p a b))).m
  rw [cqPrepare_apply_uliftCoin]
  ext i j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  all_goals
    simp [MState.m, MState.ofClassical, Matrix.add_apply, Prob.coe_one_minus, uliftCoin,
      ProbDistribution.congr_apply]
    rw [← HermitianMat.mat_apply, HermitianMat.diagonal_mat]
    simp [Matrix.diagonal, Prob.mix, Mixable.mix, Mixable.mix_ab, Prob.coe_one_minus]
  all_goals ring_nf

private theorem uliftCoin_support_top (p : Prob) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (MState.ofClassical (uliftCoin p)).M.support = ⊤ := by
  rw [← HermitianMat.nonSingular_iff_support_top]
  apply HermitianMat.nonSingular_of_posDef
  rw [MState.coe_ofClassical]
  apply Matrix.PosDef.diagonal
  intro i
  rcases i with ⟨i⟩
  fin_cases i
  · simpa [Complex.real_lt_real, uliftCoin, ProbDistribution.congr_apply] using hp0
  · simp [uliftCoin, ProbDistribution.congr_apply, Prob.coe_one_minus]
    exact_mod_cast hp1

private def classicalIndicatorEffect {κ : Type u} [DecidableEq κ] (A : Set κ) :
    HermitianMat κ ℂ := by classical exact HermitianMat.diagonal ℂ fun x => if x ∈ A then 1 else 0

private theorem ofClassical_exp_val_indicator
    {κ : Type u} [Fintype κ] [DecidableEq κ] (dist : ProbDistribution κ) (A : Set κ)
    [DecidablePred (fun x => x ∈ A)] :
    (MState.ofClassical dist).exp_val (classicalIndicatorEffect A) =
      ∑ x, if x ∈ A then (dist x : ℝ) else 0 := by
  rw [classicalIndicatorEffect, MState.exp_val, MState.coe_ofClassical,
    HermitianMat.inner_eq_re_trace]
  simp [Matrix.trace, HermitianMat.diagonal]
  exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp

private theorem exists_effect_exp_val_ne_of_ne (ρ σ : MState d) (hne : ρ ≠ σ) :
    ∃ T : HermitianMat d ℂ, (0 ≤ T ∧ T ≤ 1) ∧ ρ.exp_val T ≠ σ.exp_val T := by
  let A : HermitianMat d ℂ := ρ.M - σ.M
  have hA_not_nonneg : ¬ 0 ≤ A := by
    intro hA_nonneg
    exact hne (MState.ext (eq_of_sub_eq_zero (HermitianMat.ext <|
      (Matrix.PosSemidef.trace_eq_zero_iff (HermitianMat.zero_le_iff.mp hA_nonneg)).1 <|
        (HermitianMat.trace_eq_zero_iff (A := A)).1
          (by simp [A, HermitianMat.trace_sub, ρ.tr, σ.tr]))))
  let B : HermitianMat d ℂ := A⁻
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using HermitianMat.negPart_nonneg A
  have hinner_neg : inner ℝ A B < 0 := by
    simpa [B] using (HermitianMat.inner_negPart_neg_iff (A := A)).2 hA_not_nonneg
  have hB_trace_pos : 0 < B.trace := by
    refine lt_of_le_of_ne (HermitianMat.trace_nonneg hB_nonneg) ?_
    intro htrace
    have hB_zero : B = 0 := HermitianMat.ext <|
      (Matrix.PosSemidef.trace_eq_zero_iff (HermitianMat.zero_le_iff.mp hB_nonneg)).1 <|
        (HermitianMat.trace_eq_zero_iff (A := B)).1 htrace.symm
    rw [hB_zero] at hinner_neg
    simp at hinner_neg
  let T : HermitianMat d ℂ := B.trace⁻¹ • B
  have hT_nonneg : 0 ≤ T := by
    simpa [T] using smul_nonneg (inv_nonneg.mpr hB_trace_pos.le) hB_nonneg
  have hT_le_one : T ≤ 1 := by
    dsimp [T]
    simpa [smul_smul, inv_mul_cancel₀ hB_trace_pos.ne'] using
      smul_le_smul_of_nonneg_left (HermitianMat.le_trace_smul_one hB_nonneg)
        (inv_nonneg.mpr hB_trace_pos.le)
  refine ⟨T, ⟨hT_nonneg, hT_le_one⟩, fun hsame => ?_⟩
  have hzero : inner ℝ A T = 0 := by
    simpa [A, MState.exp_val, inner_sub_left] using sub_eq_zero.mpr hsame
  have hneg : inner ℝ A T < 0 := by
    simpa [T, inner_smul_right] using
      mul_neg_of_pos_of_neg (inv_pos.mpr hB_trace_pos) hinner_neg
  linarith

private theorem hellingerOverlap_uliftCoin (p q : Prob) :
    hellingerOverlap (uliftCoin p) (uliftCoin q) =
      Real.sqrt ((p : ℝ) * (q : ℝ)) +
        Real.sqrt ((1 - (p : ℝ)) * (1 - (q : ℝ))) := by
  change (∑ x : ULift (Fin 2),
      Real.sqrt (((ProbDistribution.coin p) x.down : ℝ) *
        ((ProbDistribution.coin q) x.down : ℝ))) = _
  simpa [Fin.sum_univ_two] using
    (Equiv.sum_comp (Equiv.ulift : ULift (Fin 2) ≃ Fin 2)
      fun y : Fin 2 => Real.sqrt (((ProbDistribution.coin p) y : ℝ) *
        ((ProbDistribution.coin q) y : ℝ)))

private theorem exists_likelihood_indicator_effect
    {κ : Type u} [Fintype κ] [DecidableEq κ] (P Q : ProbDistribution κ) (s r : Prob)
    (hoverlap_s : hellingerOverlap P Q ≤ (s : ℝ))
    (hoverlap_r : hellingerOverlap P Q ≤ 1 - (r : ℝ)) :
    ∃ T : HermitianMat κ ℂ, (0 ≤ T ∧ T ≤ 1) ∧
      ∃ α β : Prob,
        (MState.ofClassical P).exp_val T = α ∧
        (MState.ofClassical Q).exp_val T = β ∧
        (α : ℝ) ≤ s ∧ (r : ℝ) ≤ β := by
  classical
  let A : Set κ := {x | (P x : ℝ) ≤ Q x}
  let T : HermitianMat κ ℂ := classicalIndicatorEffect A
  have hT : 0 ≤ T ∧ T ≤ 1 := by
    refine ⟨?_, ?_⟩
    · rw [HermitianMat.zero_le_iff]
      simp [T, classicalIndicatorEffect, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]
      exact fun i => by by_cases hi : i ∈ A <;> simp [hi]
    · rw [← sub_nonneg]
      rw [show T = HermitianMat.diagonal ℂ fun x => if x ∈ A then (1 : ℝ) else 0 from rfl,
        ← HermitianMat.diagonal_one (𝕜 := ℂ),
        ← HermitianMat.diagonal_sub, HermitianMat.zero_le_iff, HermitianMat.diagonal_mat,
        Matrix.posSemidef_diagonal_iff]
      exact fun i => by by_cases hi : i ∈ A <;> simp [hi]
  refine ⟨T, hT,
    ⟨(MState.ofClassical P).exp_val T, (MState.ofClassical P).exp_val_prob hT⟩,
    ⟨(MState.ofClassical Q).exp_val T, (MState.ofClassical Q).exp_val_prob hT⟩,
    rfl, rfl, ?_, ?_⟩
  · change (MState.ofClassical P).exp_val T ≤ (s : ℝ)
    rw [ofClassical_exp_val_indicator]
    exact (show ∑ x, (if (P x : ℝ) ≤ Q x then (P x : ℝ) else 0) ≤
        hellingerOverlap P Q by
      rw [hellingerOverlap]
      refine Finset.sum_le_sum ?_
      intro x _
      by_cases hx : (P x : ℝ) ≤ Q x
      · simpa [hx] using Real.le_sqrt (P x).2.1 (mul_nonneg (P x).2.1 (Q x).2.1) |>.2
          (by simpa [pow_two] using mul_le_mul_of_nonneg_left hx (P x).2.1)
      · simpa [hx] using Real.sqrt_nonneg ((P x : ℝ) * (Q x : ℝ))).trans hoverlap_s
  · change (r : ℝ) ≤ (MState.ofClassical Q).exp_val T
    rw [ofClassical_exp_val_indicator]
    change (r : ℝ) ≤ ∑ x, (if (P x : ℝ) ≤ Q x then (Q x : ℝ) else 0)
    have hcompl : ∑ x, (if (P x : ℝ) ≤ Q x then 0 else (Q x : ℝ)) ≤
        hellingerOverlap P Q := by
      rw [hellingerOverlap]
      refine Finset.sum_le_sum ?_
      intro x _
      by_cases hx : (P x : ℝ) ≤ Q x
      · simpa [hx] using Real.sqrt_nonneg ((P x : ℝ) * (Q x : ℝ))
      · rw [mul_comm]
        simpa [hx] using Real.le_sqrt (Q x).2.1 (mul_nonneg (Q x).2.1 (P x).2.1) |>.2
          (by simpa [pow_two] using
            mul_le_mul_of_nonneg_left (le_of_not_ge hx) (Q x).2.1)
    have htotal' :
        (∑ x, (if (P x : ℝ) ≤ Q x then 0 else (Q x : ℝ))) +
          (∑ x, (if (P x : ℝ) ≤ Q x then (Q x : ℝ) else 0)) =
        1 := by
      rw [← Finset.sum_add_distrib]
      convert Q.normalized using 1
      exact Finset.sum_congr rfl fun x _ => by by_cases hx : (P x : ℝ) ≤ Q x <;> simp [hx]
    linarith

private theorem exists_npow_binary_effect_le_ge
    (p q s r : Prob) (hpq : (p : ℝ) < q)
    (hs_pos : 0 < (s : ℝ)) (hr_lt_one : (r : ℝ) < 1) :
    ∃ (n : ℕ) (T : HermitianMat (Fin n → ULift.{u} (Fin 2)) ℂ),
      (0 ≤ T ∧ T ≤ 1) ∧ ∃ α β : Prob,
        (MState.npow (MState.ofClassical (uliftCoin p)) n).exp_val T = α ∧
        (MState.npow (MState.ofClassical (uliftCoin q)) n).exp_val T = β ∧
        (α : ℝ) ≤ s ∧ (r : ℝ) ≤ β := by
  let ε : ℝ := (s : ℝ) ⊓ (1 - (r : ℝ))
  have ha1 : hellingerOverlap (uliftCoin p) (uliftCoin q) < 1 := by
    rw [hellingerOverlap_uliftCoin]
    simpa [hellingerOverlap_coin] using hellingerOverlap_coin_lt_one p q hpq
  obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one
    (show 0 < ε by simpa [ε] using lt_inf_iff.mpr ⟨hs_pos, sub_pos.mpr hr_lt_one⟩) ha1
  have hoverlap_lt :
      hellingerOverlap (ProbDistribution.npow (uliftCoin p) n)
        (ProbDistribution.npow (uliftCoin q) n) < ε := by
    rwa [ProbDistribution.hellingerOverlap_npow]
  obtain ⟨T, hT, α, β, hpT, hqT, hαs, hrβ⟩ :=
    exists_likelihood_indicator_effect
      (ProbDistribution.npow (uliftCoin p) n) (ProbDistribution.npow (uliftCoin q) n) s r
      (hoverlap_lt.le.trans inf_le_left) (hoverlap_lt.le.trans inf_le_right)
  exact ⟨n, T, hT, α, β, by simpa [MState.ofClassical_npow] using hpT,
    by simpa [MState.ofClassical_npow] using hqT, hαs, hrβ⟩

/-- Universe-lifted two-outcome POVM associated to an effect `0 ≤ T ≤ 1`. -/
private def binaryPOVMOfEffectULift (T : HermitianMat d ℂ) (hT : 0 ≤ T ∧ T ≤ 1) :
    POVM (ULift (Fin 2)) d where
  mats i := if i = ULift.up (0 : Fin 2) then T else 1 - T
  nonneg i := by
    split
    · exact hT.1
    · exact HermitianMat.zero_le_iff.mpr hT.2
  normalized := by
    have hsum :
        (∑ i : ULift (Fin 2), if i = ULift.up (0 : Fin 2) then T else 1 - T) =
          ∑ i : Fin 2, if ULift.up i = ULift.up (0 : Fin 2) then T else 1 - T := by
      refine Fintype.sum_equiv Equiv.ulift
        (fun i : ULift (Fin 2) => if i = ULift.up (0 : Fin 2) then T else 1 - T)
        (fun i : Fin 2 => if ULift.up i = ULift.up (0 : Fin 2) then T else 1 - T) ?_
      rintro ⟨x⟩
      rfl
    rw [hsum]
    simp [Fin.sum_univ_two]

/-- Measuring a lifted binary effect and discarding the post-measurement state gives a lifted coin. -/
private theorem binaryPOVMOfEffectULift_measureDiscard_apply
    (T : HermitianMat d ℂ) (hT : 0 ≤ T ∧ T ≤ 1) (ρ : MState d) :
    (binaryPOVMOfEffectULift T hT).measureDiscard ρ =
      MState.ofClassical (uliftCoin ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩) := by
  rw [POVM.measureDiscard_apply]
  congr 1
  let p : Prob := ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩
  ext i
  rcases i with ⟨i⟩
  fin_cases i
  · let z : ULift.{u} (Fin 2) := ULift.up (0 : Fin 2)
    change inner ℝ T ρ.M = ((uliftCoin p) z : ℝ)
    simp [z, p, uliftCoin, ProbDistribution.congr_apply, MState.exp_val, HermitianMat.inner_comm]
  · let o : ULift.{u} (Fin 2) := ULift.up (1 : Fin 2)
    change inner ℝ (1 - T) ρ.M = ((uliftCoin p) o : ℝ)
    simp [o, p, uliftCoin, ProbDistribution.congr_apply, Prob.coe_one_minus,
      MState.exp_val, HermitianMat.inner_comm, inner_sub_right, HermitianMat.inner_one, ρ.tr]

private theorem exists_binary_measurement_of_ne (ρ σ : MState d) (hne : ρ ≠ σ) :
    ∃ p q : Prob, (p : ℝ) < (q : ℝ) ∧
      ∃ Λ : CPTPMap d (ULift.{u} (Fin 2)),
        Λ ρ = MState.ofClassical (uliftCoin p) ∧
        Λ σ = MState.ofClassical (uliftCoin q) := by
  obtain ⟨T, hT, hT_ne⟩ := exists_effect_exp_val_ne_of_ne ρ σ hne
  let p : Prob := ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩
  let q : Prob := ⟨σ.exp_val T, σ.exp_val_prob hT⟩
  by_cases hpq : (p : ℝ) < q
  · exact ⟨p, q, hpq, (binaryPOVMOfEffectULift T hT).measureDiscard,
      by rw [binaryPOVMOfEffectULift_measureDiscard_apply],
      by rw [binaryPOVMOfEffectULift_measureDiscard_apply]⟩
  · let T' : HermitianMat d ℂ := 1 - T
    have hT' : 0 ≤ T' ∧ T' ≤ 1 := by
      refine ⟨by dsimp [T']; exact HermitianMat.zero_le_iff.mpr hT.2, ?_⟩
      dsimp [T']
      rw [sub_le_iff_le_add]
      simpa using hT.1
    have hpq' : ((1 - p : Prob) : ℝ) < (1 - q : Prob) := by
      rw [Prob.coe_one_minus, Prob.coe_one_minus]
      linarith [lt_of_le_of_ne (le_of_not_gt hpq) (fun heq => hT_ne heq.symm)]
    refine ⟨1 - p, 1 - q, hpq', (binaryPOVMOfEffectULift T' hT').measureDiscard, ?_, ?_⟩ <;>
      rw [binaryPOVMOfEffectULift_measureDiscard_apply] <;>
      congr 2 <;>
      apply Subtype.ext <;>
      simp [T', p, q, MState.exp_val_sub, MState.exp_val_one, Prob.coe_one_minus]

private theorem exists_binary_postprocess {α β s r : Prob}
    (hαs : (α : ℝ) ≤ s) (hsr : (s : ℝ) < r) (hrβ : (r : ℝ) ≤ β) :
    ∃ a b : Prob, Prob.mix α a b = s ∧ Prob.mix β a b = r := by
  let A : ℝ := α
  let B : ℝ := β
  let S : ℝ := s
  let R : ℝ := r
  have hAB : A < B := by dsimp [A, B, S, R] at *; linarith
  let k : ℝ := (R - S) / (B - A)
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (sub_nonneg.mpr (by dsimp [S, R]; exact hsr.le))
      (sub_nonneg.mpr hAB.le)
  have hk_le_one : k ≤ 1 := by
    dsimp [k]
    rw [div_le_one (sub_pos.mpr hAB)]
    dsimp [A, B, S, R] at *
    linarith
  let bR : ℝ := S - A * k
  let aR : ℝ := bR + k
  have hbR_nonneg : 0 ≤ bR := by
    dsimp [bR, A, S] at *
    linarith [mul_le_mul_of_nonneg_left hk_le_one α.2.1]
  have hbR_le_one : bR ≤ 1 := by
    dsimp [bR, S]
    nlinarith [s.2.2, α.2.1, hk_nonneg]
  have haR_nonneg : 0 ≤ aR := by dsimp [aR]; positivity
  have haR_le_one : aR ≤ 1 := by
    have hden_pos : 0 < B - A := sub_pos.mpr hAB
    have hmain :
        S * (B - A) + (1 - A) * (R - S) ≤ 1 * (B - A) := by
      nlinarith [
        mul_le_mul_of_nonneg_right (show R ≤ B by dsimp [R, B] at hrβ ⊢; exact hrβ)
          (show 0 ≤ 1 - A by dsimp [A]; linarith [α.2.2]),
        mul_le_mul_of_nonpos_right (show A ≤ S by dsimp [A, S] at hαs ⊢; exact hαs)
          (show B - 1 ≤ 0 by dsimp [B]; linarith [β.2.2])]
    rw [show aR = (S * (B - A) + (1 - A) * (R - S)) / (B - A) by
      dsimp [aR, bR, k]
      field_simp [hden_pos.ne']
      ring, div_le_one hden_pos]
    simpa using hmain
  let a : Prob := ⟨aR, haR_nonneg, haR_le_one⟩
  let b : Prob := ⟨bR, hbR_nonneg, hbR_le_one⟩
  refine ⟨a, b, ?_, ?_⟩
  all_goals
    ext
    simp [Prob.mix, Mixable.mix, Mixable.mix_ab, Prob.coe_one_minus, a, b, aR, bR, k, A, B, S, R]
  ·
    ring
  ·
    field_simp [show (↑β : ℝ) - ↑α ≠ 0 by dsimp [A, B] at hAB; linarith]
    ring

/-- A full-support state dominates every other state up to an integer scalar. -/
private theorem exists_le_nat_smul_of_fullSupport (ρ σ : MState d)
    (hσ : σ.M.support = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ρ.M ≤ ((N + 1 : ℝ) • σ.M) := by
  letI : σ.M.NonSingular := HermitianMat.nonSingular_iff_support_top.mpr hσ
  have hexp : ∃ x : ℝ, ρ.M ≤ Real.exp x • σ.M := by
    by_contra h
    exact (RelEntropy.max_not_top ρ σ.M σ.nonneg).mpr
      (by simp [HermitianMat.nonSingular_ker_bot]) (by simp [max, h])
  obtain ⟨x, hx⟩ := hexp
  refine ⟨Nat.ceil (Real.exp x), Nat.ceil_pos.mpr (Real.exp_pos x), ?_⟩
  exact hx.trans <| smul_le_smul_of_nonneg_right ((Nat.le_ceil _).trans (by norm_num)) σ.nonneg

section nontrivial
variable [RelEntropy f] [RelEntropy.Nontrivial f]

/-- From Tomamichel nontriviality, extract a strictly positive binary classical pair with
full-support states. This is the finite binary witness used in the proof of `faithful`. -/
private theorem exists_positive_binary_pair :
    ∃ p q : Prob, 0 < (p : ℝ) ∧ (p : ℝ) < q ∧ (q : ℝ) < 1 ∧
      (MState.ofClassical (uliftCoin.{u} p)).M.support = ⊤ ∧
      (MState.ofClassical (uliftCoin.{u} q)).M.support = ⊤ ∧
      0 < f (MState.ofClassical (uliftCoin.{u} p))
        (MState.ofClassical (uliftCoin.{u} q)).M := by
  obtain ⟨s, t, hs0, -, ht0, -, hs_order, hsSupport, htSupport, hpos⟩ :
      ∃ s t : Prob,
        0 < (s : ℝ) ∧ (s : ℝ) < 1 / 2 ∧
        0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 ∧
        (s : ℝ) < ((1 - t : Prob) : ℝ) ∧
        (MState.ofClassical (uliftCoin s)).M.support = ⊤ ∧
        (MState.ofClassical (uliftCoin (1 - t))).M.support = ⊤ ∧
        0 < f (MState.ofClassical (uliftCoin s))
          (MState.ofClassical (uliftCoin (1 - t))).M := by
    obtain ⟨γ, ω, hγ, hω, hpos⟩ :=
      RelEntropy.Nontrivial.nontrivial (f := f) (ULift.{u} (Fin 2))
    obtain ⟨s, t, hs0, hslt, ht0, htlt, hleft, hright⟩ :
        ∃ s t : Prob, 0 < (s : ℝ) ∧ (s : ℝ) < 1 / 2 ∧
          0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 ∧
          (t : ℝ) • γ.M ≤ (1 - (s : ℝ)) • ω.M ∧
          (s : ℝ) • ω.M ≤ (1 - (t : ℝ)) • γ.M := by
      obtain ⟨Nγω, hNγω_pos, hγω⟩ := exists_le_nat_smul_of_fullSupport γ ω hω
      obtain ⟨Nωγ, _, hωγ⟩ := exists_le_nat_smul_of_fullSupport ω γ hγ
      let K : ℕ := Nat.max Nγω Nωγ
      let a : ℝ := 1 / (K + 2 : ℝ)
      have hden_pos : (0 : ℝ) < K + 2 := by positivity
      have ha_pos : 0 < a := by dsimp [a]; positivity
      have ha_lt_half : a < 1 / 2 := by
        dsimp [a]
        rw [div_lt_iff₀ hden_pos]
        nlinarith [show (1 : ℝ) ≤ K by
          exact_mod_cast le_trans hNγω_pos (le_max_left Nγω Nωγ)]
      have hscale {N : ℕ} (hNK : N ≤ K) : a * (N + 1 : ℝ) ≤ 1 - a := by
        dsimp [a]
        rw [div_mul_eq_mul_div, one_sub_div hden_pos.ne',
          div_le_div_iff_of_pos_right hden_pos]
        nlinarith [show (N + 1 : ℝ) ≤ K + 1 by exact_mod_cast Nat.succ_le_succ hNK]
      let p : Prob := ⟨a, ha_pos.le, by linarith [ha_lt_half]⟩
      refine ⟨p, p, by simpa [p] using ha_pos, by simpa [p] using ha_lt_half,
        by simpa [p] using ha_pos, by simpa [p] using ha_lt_half, ?_, ?_⟩
      · simpa [p] using calc
          a • γ.M ≤ a • ((Nγω + 1 : ℝ) • ω.M) :=
            smul_le_smul_of_nonneg_left hγω ha_pos.le
          _ = (a * (Nγω + 1 : ℝ)) • ω.M := by rw [smul_smul]
          _ ≤ (1 - a) • ω.M := smul_le_smul_of_nonneg_right
            (hscale (le_max_left Nγω Nωγ)) ω.nonneg
      · simpa [p] using calc
          a • ω.M ≤ a • ((Nωγ + 1 : ℝ) • γ.M) :=
            smul_le_smul_of_nonneg_left hωγ ha_pos.le
          _ = (a * (Nωγ + 1 : ℝ)) • γ.M := by rw [smul_smul]
          _ ≤ (1 - a) • γ.M := smul_le_smul_of_nonneg_right
            (hscale (le_max_right Nγω Nωγ)) γ.nonneg
    have hden : 0 < 1 - (s : ℝ) - (t : ℝ) := by linarith
    let τ := fun i =>
      if i = ULift.up (0 : Fin 2) then
        binaryPrepOne γ ω (s : ℝ) (t : ℝ) hden hleft
      else
        binaryPrepZero γ ω (s : ℝ) (t : ℝ) hden hright
    let Λ := CPTPMap.cqPrepare τ
    have hdenC : (1 - ((s : ℝ) : ℂ) - ((t : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hden.ne'
    have hγprep : Λ (MState.ofClassical (uliftCoin s)) = γ := by
      apply MState.ext_m
      change (CPTPMap.cqPrepare τ (MState.ofClassical (uliftCoin s))).m = γ.m
      rw [cqPrepare_apply_uliftCoin, Prob.coe_one_minus]
      ext i j
      simp [τ, binaryPrepOne, binaryPrepZero, MState.m, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, -MState.mat_M]
      field_simp [hdenC]
      ring
    have hωprep : Λ (MState.ofClassical (uliftCoin (1 - t))) = ω := by
      apply MState.ext_m
      change (CPTPMap.cqPrepare τ (MState.ofClassical (uliftCoin (1 - t)))).m = ω.m
      rw [cqPrepare_apply_uliftCoin, Prob.coe_one_minus, Prob.coe_one_minus]
      ext i j
      simp [τ, binaryPrepOne, binaryPrepZero, MState.m, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, -MState.mat_M]
      field_simp [hdenC]
      ring
    refine ⟨s, t, hs0, hslt, ht0, htlt, by rw [Prob.coe_one_minus]; linarith,
      uliftCoin_support_top s hs0 (by linarith),
      uliftCoin_support_top (1 - t) (by rw [Prob.coe_one_minus]; linarith)
        (by rw [Prob.coe_one_minus]; linarith), ?_⟩
    exact lt_of_lt_of_le hpos <| by
      simpa [hγprep, hωprep] using DPI (f := f) (MState.ofClassical (uliftCoin s))
        (MState.ofClassical (uliftCoin (1 - t))) Λ
  exact ⟨s, 1 - t, hs0, hs_order, by rw [Prob.coe_one_minus]; linarith,
    hsSupport, htSupport, hpos⟩

/-- A nontrivial relative entropy is **faithful**: it can distinguish when two states are equal.

The proof (Tomamichel §5) goes by building a binary measurement that separates `ρ` from `σ`,
using DPI to reduce to a classical `Fin 2` distribution, then amplifying with `of_kron` until the
`Nontrivial` axiom forces a strictly positive value. The tensor-power separation step is formalized
via the finite classical likelihood test in `exists_npow_binary_effect_le_ge`. -/
theorem faithful (ρ σ : MState d) : f ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro hzero
    by_contra hne
    obtain ⟨p, q, hpq, Λ, hρ, hσ⟩ := exists_binary_measurement_of_ne ρ σ hne
    let ρp := MState.ofClassical (uliftCoin p)
    let σq := MState.ofClassical (uliftCoin q)
    have hzero_one : f ρp σq.M = 0 :=
      le_antisymm (by simpa [ρp, σq, hρ, hσ, hzero] using DPI (f := f) ρ σ Λ) bot_le
    obtain ⟨s, r, hs_pos, hsr, hr_lt_one, _, _, hpos⟩ :=
      exists_positive_binary_pair (f := f)
    obtain ⟨n, T, hT, α, β, hpT, hqT, hαs, hrβ⟩ :=
      exists_npow_binary_effect_le_ge p q s r hpq hs_pos hr_lt_one
    suffices 0 < f (MState.npow ρp n) (MState.npow σq n).M by
      rw [RelEntropy.of_npow (f := f), hzero_one, mul_zero] at this
      simp at this
    obtain ⟨a, b, hsmix, hrmix⟩ := exists_binary_postprocess hαs hsr hrβ
    let Μ := (binaryPOVMOfEffectULift T hT).measureDiscard
    let Λ' := (binaryClassicalPostprocess a b) ∘ₘ Μ
    have hOut (x z y : Prob)
        (hz : (MState.npow (MState.ofClassical (uliftCoin x)) n).exp_val T = z)
        (hy : Prob.mix z a b = y) :
        Λ' (MState.npow (MState.ofClassical (uliftCoin x)) n) =
          MState.ofClassical (uliftCoin y) := by
      simpa [Λ', Μ, CPTPMap.compose_eq, binaryPOVMOfEffectULift_measureDiscard_apply,
        binaryClassicalPostprocess_apply] using
        (congrArg (fun z => MState.ofClassical (uliftCoin (Prob.mix z a b)))
          (Subtype.ext hz)).trans (congrArg (fun x => MState.ofClassical (uliftCoin x)) hy)
    exact lt_of_lt_of_le hpos <| by
      simpa [ρp, σq, hOut p α s hpT hsmix, hOut q β r hqT hrmix] using
        DPI (f := f) (MState.npow ρp n) (MState.npow σq n) Λ'
  · rintro rfl
    simp

/-- In every system with at least two classical points, a nontrivial relative entropy has a
strictly positive value on some pair of full-support states. -/
theorem exists_fullSupport_positive_of_two_le_card
    (d : Type u) [Fintype d] [DecidableEq d] (hd : 2 ≤ Fintype.card d) :
    ∃ (ρ σ : MState d), ρ.M.support = ⊤ ∧ σ.M.support = ⊤ ∧ 0 < f ρ σ := by
  haveI : Nonempty d := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num) hd)
  let i : d := Classical.arbitrary d
  let p : Prob := ⟨1 / 2, by norm_num⟩
  let ρ : MState d := p [MState.ofClassical (.constant i) ↔ MState.uniform]
  refine ⟨ρ, MState.uniform, ?_, ?_, ?_⟩
  · haveI : ρ.M.NonSingular := HermitianMat.nonSingular_of_posDef <| by
      dsimp [ρ]
      exact MState.PosDef_mix_of_ne_one (hσ₂ := MState.uniform_posDef) p
        (by dsimp [p]; norm_num [Prob.ext_iff])
    exact HermitianMat.nonSingular_support_top
  · haveI : (MState.uniform : MState d).M.NonSingular :=
      HermitianMat.nonSingular_of_posDef MState.uniform_posDef
    exact HermitianMat.nonSingular_support_top
  · refine bot_lt_iff_ne_bot.mpr ((faithful (f := f) ρ MState.uniform).not.mpr ?_)
    intro hρσ
    have hmat := congrArg (fun τ : MState d => τ.M.mat) hρσ
    simp [ρ, p, Mixable.mix, Mixable.mix_ab, MState.instMixable,
      MState.uniform, MState.ofClassical, ProbDistribution.constant_eq,
      ProbDistribution.uniform_def, HermitianMat.diagonal, Mixable.to_U] at hmat
    have hdiag_re := congrArg Complex.re (congrFun (congrFun hmat i) i)
    simp [Matrix.add_apply] at hdiag_re
    norm_num at hdiag_re
    nlinarith [inv_lt_one_of_one_lt₀
      (by exact_mod_cast (lt_of_lt_of_le one_lt_two hd) : (1 : ℝ) < Fintype.card d)]

end nontrivial

end RelEntropy
