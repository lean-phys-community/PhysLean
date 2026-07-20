/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ClassicalInfo.Distribution
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import QuantumInfo.ClassicalInfo.ForMathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # Shannon entropy

Definitions and facts about the Shannon entropy function -x*ln(x), both on a single
variable and on a distribution.

There is significant overlap with `Real.negMulLog` and `Real.binEntropy` in Mathlib,
and probably these files could be combined in some form. -/

@[expose] public section

noncomputable section
open NNReal

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The one-event entropy function, H₁(p) = -p*ln(p). Uses nits. -/
def H₁ : Prob → ℝ :=
  fun x ↦ Real.negMulLog x

/-- H₁ of 0 is zero.-/
@[simp]
def H₁_zero_eq_zero : H₁ 0 = 0 := by
  simp [H₁]

/-- H₁ of 1 is zero.-/
@[simp]
def H₁_one_eq_zero : H₁ 1 = 0 := by
  simp [H₁]

/-- Entropy is nonnegative. -/
theorem H₁_nonneg (p : Prob) : 0 ≤ H₁ p :=
  Real.negMulLog_nonneg p.zero_le_coe p.coe_le_one

/-- Entropy is less than 1. -/
theorem H₁_le_1 (p : Prob) : H₁ p < 1 := by
  rw [H₁]
  rcases eq_or_ne (p : ℝ) 1 with h | h
  · simp [h]
  · linarith [Real.negMulLog_lt_one_sub_self p.zero_le_coe h, p.zero_le_coe]

/-- Entropy is at most 1/e. -/
theorem H₁_le_exp_m1 (p : Prob) : H₁ p ≤ Real.exp (-1) :=
  Real.negMulLog_le_rexp_neg_one p.zero_le_coe

theorem H₁_concave : ∀ (x y : Prob), ∀ (p : Prob), p[H₁ x ↔ H₁ y] ≤ H₁ (p[x ↔ y]) := by
  intros x y p
  have h := Real.concaveOn_negMulLog.2 (Set.mem_Ici.2 x.zero_le_coe)
    (Set.mem_Ici.2 y.zero_le_coe) p.zero_le_coe
    (show (0 : ℝ) ≤ 1 - ↑p by linarith [p.coe_le_one]) (by ring)
  simpa only [H₁, smul_eq_mul, Prob.coe_one_minus, Mixable.mix, Mixable.mix_ab,
    Mixable.mkT_instUniv, Prob.mkT_mixable, Prob.to_U_mixable, Mixable.to_U_instUniv] using h

/-- The Shannon entropy of a discrete distribution, H(X) = ∑ H₁(p_x). -/
def Hₛ (d : ProbDistribution α) : ℝ :=
  Finset.sum Finset.univ (fun x ↦ H₁ (d.prob x))

/-- Shannon entropy of a distribution is nonnegative. -/
theorem Hₛ_nonneg (d : ProbDistribution α) : 0 ≤ Hₛ d :=
  Finset.sum_nonneg' fun _ ↦ H₁_nonneg _

/-- Shannon entropy of a distribution is at most ln d. -/
theorem Hₛ_le_log_d (d : ProbDistribution α) : Hₛ d ≤ Real.log (Fintype.card α) := by
  cases isEmpty_or_nonempty α
  · simp [Hₛ]
  have hcard : (0 : ℝ) < Fintype.card α := by positivity
  have key : (Fintype.card α : ℝ)⁻¹ * Hₛ d ≤
      (Fintype.card α : ℝ)⁻¹ * Real.log (Fintype.card α) := by
    have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun _ : α ↦ (Fintype.card α : ℝ)⁻¹) (p := fun i ↦ (d.prob i : ℝ))
      (fun _ _ ↦ by positivity) (by simp [hcard.ne']) fun i _ ↦ Prob.zero_le_coe
    simpa [← Finset.mul_sum, d.2, ProbDistribution.prob, Hₛ, H₁, Real.negMulLog, neg_mul,
      Real.log_inv] using h
  exact le_of_mul_le_mul_left key (by positivity)

/-- The shannon entropy of a constant variable is zero. -/
@[simp]
theorem Hₛ_constant_eq_zero {i : α} : Hₛ (ProbDistribution.constant i) = 0 := by
  simp [Hₛ, apply_ite]

/-- Shannon entropy of a uniform distribution is ln d. -/
theorem Hₛ_uniform [Nonempty α] :
    Hₛ (ProbDistribution.uniform (α := α)) = Real.log (Finset.univ.card (α := α)) := by
  simp [Hₛ, ProbDistribution.prob, H₁, Real.negMulLog]

/-- Shannon entropy of two-event distribution. -/
theorem Hₛ_coin (p : Prob) : Hₛ (ProbDistribution.coin p) = Real.binEntropy p := by
  simp [Hₛ, H₁, ProbDistribution.coin, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

lemma Hₛ_eq_of_multiset_map_eq (d₁ : ProbDistribution α) (d₂ : ProbDistribution β)
    (h : Multiset.map d₁.prob Finset.univ.val = Multiset.map d₂.prob Finset.univ.val) :
    Hₛ d₁ = Hₛ d₂ := by
  convert congr_arg (fun m ↦ m.map (fun x ↦ -Real.log x.1 * x.1 ) |> Multiset.sum ) h using 1
  <;> simp [Hₛ, H₁, mul_comm, Real.negMulLog]

--TODO:
-- * Shannon entropy is concave under mixing distributions.
-- * Shannon entropy as an expectation value
