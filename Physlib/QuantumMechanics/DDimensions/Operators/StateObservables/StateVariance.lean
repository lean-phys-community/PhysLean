/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Krystian Nowakowski
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.ExpectedValue
public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.IsEigenvector
public import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!
# State variance and standard deviation

The state variance is the first-order quantity `\|Tψ - ⟨T⟩_ψ ψ\|^2`. It only requires
`ψ ∈ T.domain`.

## Main definitions

- `LinearPMap.stateVariance` and `LinearPMap.stateStdDev`: state variance and standard deviation.

## Main statements

- `LinearPMap.stateVariance_eq_norm_sq_sub_stateExpectedValue_sq`: for a unit vector, the variance
  is `‖Tψ‖ ^ 2 - ⟨T⟩_ψ ^ 2`.
- `LinearPMap.stateVariance_eq_zero_iff_isEigenvector` and
  `LinearPMap.stateStdDev_eq_zero_iff_isEigenvector`: for a unit vector, zero variance or standard
  deviation is equivalent to the eigenvector condition.

## References

- [B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 12][hall2013quantum].

-/

@[expose] public section

namespace LinearPMap

open InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- State variance `‖Tψ - ⟨T⟩_ψ ψ‖ ^ 2`; only `ψ ∈ T.domain` is required. -/
def stateVariance (T : H →ₗ.[ℂ] H) (ψ : T.domain) : ℝ :=
  ‖centered T ψ‖ ^ 2

/-- The state variance is the squared norm of the centered vector. -/
lemma stateVariance_eq_centered_norm_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    stateVariance T ψ = ‖centered T ψ‖ ^ 2 :=
  rfl

/-- `stateVariance` with `centered` unfolded to `Tψ - ⟨T⟩_ψ • ψ`. -/
lemma stateVariance_eq_norm_sub_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    stateVariance T ψ =
      ‖T ψ - (stateExpectedValue T ψ : ℂ) • (ψ : H)‖ ^ 2 :=
  rfl

/-- For symmetric `T` and `‖ψ‖ = 1`, state variance equals `‖Tψ‖ ^ 2 - ⟨T⟩_ψ ^ 2`. -/
lemma stateVariance_eq_norm_sq_sub_stateExpectedValue_sq (T : H →ₗ.[ℂ] H)
    (hT : T.IsSymmetric) (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    stateVariance T ψ = ‖T ψ‖ ^ 2 - stateExpectedValue T ψ ^ 2 := by
  let μ := stateExpectedValue T ψ
  let a : H := T ψ
  have hμ_right : ⟪(ψ : H), a⟫_ℂ = (μ : ℂ) := by
    simpa [a, μ] using stateExpectedValue_eq_inner T hT ψ
  have hμ_left : ⟪a, (ψ : H)⟫_ℂ = (μ : ℂ) := by
    simpa [inner_conj_symm] using congrArg star hμ_right
  have h_re_inner_centered : (⟪a, (μ : ℂ) • (ψ : H)⟫_ℂ).re = μ ^ 2 := by
    rw [inner_smul_right, hμ_left]
    simp [μ]
    ring
  have h_norm_centered_smul : ‖(μ : ℂ) • (ψ : H)‖ ^ 2 = μ ^ 2 := by
    rw [norm_smul, hψ_norm]
    simp [μ]
  have h_norm_sub_sq :
      ‖a - (μ : ℂ) • (ψ : H)‖ ^ 2 =
        ‖a‖ ^ 2 - 2 * (⟪a, (μ : ℂ) • (ψ : H)⟫_ℂ).re + ‖(μ : ℂ) • (ψ : H)‖ ^ 2 := by
    simpa using (norm_sub_sq (𝕜 := ℂ) a ((μ : ℂ) • (ψ : H)))
  rw [stateVariance_eq_norm_sub_sq, h_norm_sub_sq, h_re_inner_centered,
    h_norm_centered_smul]
  ring

/-- State variance is nonnegative. -/
lemma stateVariance_nonneg (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    0 ≤ stateVariance T ψ := by
  rw [stateVariance_eq_centered_norm_sq]
  exact sq_nonneg _

/-- Zero variance is the same as a zero centered vector. -/
lemma stateVariance_eq_zero_iff_centered_eq_zero (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    stateVariance T ψ = 0 ↔ centered T ψ = 0 := by
  rw [stateVariance_eq_centered_norm_sq]
  exact sq_eq_zero_iff.trans norm_eq_zero

/-- Zero variance is the same as `Tψ = ⟨T⟩_ψ ψ`. -/
lemma stateVariance_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    stateVariance T ψ = 0 ↔ T ψ = (stateExpectedValue T ψ : ℂ) • (ψ : H) := by
  rw [stateVariance_eq_zero_iff_centered_eq_zero, centered_eq_zero_iff]

/-- For `‖ψ‖ = 1`, zero variance iff `ψ` is an eigenvector with eigenvalue `⟨T⟩_ψ`. -/
lemma stateVariance_eq_zero_iff_isEigenvector (T : H →ₗ.[ℂ] H)
    (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    stateVariance T ψ = 0 ↔
      T.IsEigenvector ψ (stateExpectedValue T ψ : ℂ) := by
  rw [stateVariance_eq_zero_iff]
  constructor
  · intro h_centered
    refine ⟨h_centered, ?_⟩
    intro h_zero
    have h_zero' : (ψ : H) = 0 := by simpa using h_zero
    have h_norm_zero : ‖(ψ : H)‖ = 0 := by simp [h_zero']
    have : (0 : ℝ) = 1 := h_norm_zero.symm.trans hψ_norm
    norm_num at this
  · intro h_eigen
    exact h_eigen.1

/-- Standard deviation `√(state variance)` for `ψ ∈ T.domain`. -/
def stateStdDev (T : H →ₗ.[ℂ] H) (ψ : T.domain) : ℝ :=
  Real.sqrt (stateVariance T ψ)

/-- The state standard deviation, unfolded to the square root of the variance. -/
lemma stateStdDev_eq_sqrt_stateVariance (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    stateStdDev T ψ = Real.sqrt (stateVariance T ψ) :=
  rfl

/-- State standard deviation is nonnegative. -/
lemma stateStdDev_nonneg (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    0 ≤ stateStdDev T ψ := by
  rw [stateStdDev_eq_sqrt_stateVariance]
  exact Real.sqrt_nonneg _

@[simp]
lemma stateStdDev_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    stateStdDev T ψ ^ 2 = stateVariance T ψ := by
  rw [stateStdDev_eq_sqrt_stateVariance, Real.sq_sqrt]
  exact stateVariance_nonneg T ψ

/-- Zero standard deviation is the same as a zero centered vector. -/
lemma stateStdDev_eq_zero_iff_centered_eq_zero (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    stateStdDev T ψ = 0 ↔ centered T ψ = 0 := by
  rw [stateStdDev_eq_sqrt_stateVariance, Real.sqrt_eq_zero]
  · exact stateVariance_eq_zero_iff_centered_eq_zero T ψ
  · exact stateVariance_nonneg T ψ

/-- Zero standard deviation is the same as `Tψ = ⟨T⟩_ψ ψ`. -/
lemma stateStdDev_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    stateStdDev T ψ = 0 ↔ T ψ = (stateExpectedValue T ψ : ℂ) • (ψ : H) := by
  rw [stateStdDev_eq_zero_iff_centered_eq_zero, centered_eq_zero_iff]

/-- For `‖ψ‖ = 1`, zero standard deviation iff the eigenvector condition holds. -/
lemma stateStdDev_eq_zero_iff_isEigenvector (T : H →ₗ.[ℂ] H)
    (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    stateStdDev T ψ = 0 ↔
      T.IsEigenvector ψ (stateExpectedValue T ψ : ℂ) := by
  rw [stateStdDev_eq_zero_iff]
  constructor
  · intro h_centered
    refine ⟨h_centered, ?_⟩
    intro h_zero
    have h_zero' : (ψ : H) = 0 := by simpa using h_zero
    have h_norm_zero : ‖(ψ : H)‖ = 0 := by simp [h_zero']
    have : (0 : ℝ) = 1 := h_norm_zero.symm.trans hψ_norm
    norm_num at this
  · intro h_eigen
    exact h_eigen.1

end
end LinearPMap
