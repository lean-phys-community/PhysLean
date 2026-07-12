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
# Variance and standard deviation

The variance of a partial linear map `T` in a state `ψ` is `‖Tψ - ⟨T⟩_ψ ψ‖ ^ 2`. It only
requires `ψ ∈ T.domain`.

When `T` is symmetric, `‖ψ‖ = 1`, and `Tψ ∈ T.domain`, it also equals `⟨T^2⟩_ψ - ⟨T⟩_ψ ^ 2`.

## Main definitions

- `LinearPMap.variance` and `LinearPMap.standardDeviation`.

## Main statements

- `LinearPMap.variance_eq_norm_sq_sub_expectedValue_sq`: for a unit vector and symmetric `T`,
  the variance is `‖Tψ‖ ^ 2 - ⟨T⟩_ψ ^ 2`.
- `LinearPMap.variance_eq_re_inner_sub_expectedValue_sq`: the second-order formula when
`Tψ ∈ T.domain`.
- `LinearPMap.variance_eq_zero_iff_isEigenvector` and
  `LinearPMap.standardDeviation_eq_zero_iff_isEigenvector`: for a unit vector, zero variance or
  standard deviation is equivalent to the eigenvector condition.

## References

- [B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 12][hall2013quantum].

-/

@[expose] public section

namespace LinearPMap

open InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Variance `‖Tψ - ⟨T⟩_ψ ψ‖ ^ 2`; only `ψ ∈ T.domain` is required. -/
def variance (T : H →ₗ.[ℂ] H) (ψ : T.domain) : ℝ :=
  ‖centered T ψ‖ ^ 2

/-- The variance is the squared norm of the centered vector. -/
lemma variance_eq_centered_norm_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    variance T ψ = ‖centered T ψ‖ ^ 2 :=
  rfl

/-- `variance` with `centered` unfolded to `Tψ - ⟨T⟩_ψ • ψ`. -/
lemma variance_eq_norm_sub_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    variance T ψ =
      ‖T ψ - (expectedValue T ψ : ℂ) • (ψ : H)‖ ^ 2 :=
  rfl

/-- For symmetric `T` and `‖ψ‖ = 1`, variance equals `‖Tψ‖ ^ 2 - ⟨T⟩_ψ ^ 2`. -/
lemma variance_eq_norm_sq_sub_expectedValue_sq (T : H →ₗ.[ℂ] H)
    (hT : T.IsSymmetric) (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    variance T ψ = ‖T ψ‖ ^ 2 - expectedValue T ψ ^ 2 := by
  let μ := expectedValue T ψ
  let a : H := T ψ
  have hμ_right : ⟪(ψ : H), a⟫_ℂ = (μ : ℂ) := by
    simpa [a, μ] using expectedValue_eq_inner T hT ψ
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
  rw [variance_eq_norm_sub_sq, h_norm_sub_sq, h_re_inner_centered,
    h_norm_centered_smul]
  ring

/-- Variance is nonnegative. -/
lemma variance_nonneg (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    0 ≤ variance T ψ := by
  rw [variance_eq_centered_norm_sq]
  exact sq_nonneg _

/-- Zero variance is the same as a zero centered vector. -/
lemma variance_eq_zero_iff_centered_eq_zero (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    variance T ψ = 0 ↔ centered T ψ = 0 := by
  rw [variance_eq_centered_norm_sq]
  exact sq_eq_zero_iff.trans norm_eq_zero

/-- Zero variance is the same as `Tψ = ⟨T⟩_ψ ψ`. -/
lemma variance_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    variance T ψ = 0 ↔ T ψ = (expectedValue T ψ : ℂ) • (ψ : H) := by
  rw [variance_eq_zero_iff_centered_eq_zero, centered_eq_zero_iff]

/-- For `‖ψ‖ = 1`, zero variance iff `ψ` is an eigenvector with eigenvalue `⟨T⟩_ψ`. -/
lemma variance_eq_zero_iff_isEigenvector (T : H →ₗ.[ℂ] H)
    (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    variance T ψ = 0 ↔
      T.IsEigenvector ψ (expectedValue T ψ : ℂ) := by
  rw [variance_eq_zero_iff]
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

/-- Standard deviation `√(variance)` for `ψ ∈ T.domain`. -/
def standardDeviation (T : H →ₗ.[ℂ] H) (ψ : T.domain) : ℝ :=
  Real.sqrt (variance T ψ)

/-- The standard deviation, unfolded to the square root of the variance. -/
lemma standardDeviation_eq_sqrt_variance (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    standardDeviation T ψ = Real.sqrt (variance T ψ) :=
  rfl

/-- Standard deviation is nonnegative. -/
lemma standardDeviation_nonneg (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    0 ≤ standardDeviation T ψ := by
  rw [standardDeviation_eq_sqrt_variance]
  exact Real.sqrt_nonneg _

@[simp]
lemma standardDeviation_sq (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    standardDeviation T ψ ^ 2 = variance T ψ := by
  rw [standardDeviation_eq_sqrt_variance, Real.sq_sqrt]
  exact variance_nonneg T ψ

/-- Zero standard deviation is the same as a zero centered vector. -/
lemma standardDeviation_eq_zero_iff_centered_eq_zero (T : H →ₗ.[ℂ] H)
    (ψ : T.domain) :
    standardDeviation T ψ = 0 ↔ centered T ψ = 0 := by
  rw [standardDeviation_eq_sqrt_variance, Real.sqrt_eq_zero]
  · exact variance_eq_zero_iff_centered_eq_zero T ψ
  · exact variance_nonneg T ψ

/-- Zero standard deviation is the same as `Tψ = ⟨T⟩_ψ ψ`. -/
lemma standardDeviation_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : T.domain) :
    standardDeviation T ψ = 0 ↔ T ψ = (expectedValue T ψ : ℂ) • (ψ : H) := by
  rw [standardDeviation_eq_zero_iff_centered_eq_zero, centered_eq_zero_iff]

/-- For `‖ψ‖ = 1`, zero standard deviation iff the eigenvector condition holds. -/
lemma standardDeviation_eq_zero_iff_isEigenvector (T : H →ₗ.[ℂ] H)
    (ψ : T.domain) (hψ_norm : ‖(ψ : H)‖ = 1) :
    standardDeviation T ψ = 0 ↔
      T.IsEigenvector ψ (expectedValue T ψ : ℂ) := by
  rw [standardDeviation_eq_zero_iff]
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

section SecondOrder

variable (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
variable (ψ : T.domain)
variable (hTψ : T ψ ∈ T.domain)
variable (hψ_norm : ‖(ψ : H)‖ = 1)

include hT

/-- For symmetric `T`, `re ⟪ψ, T(Tψ)⟫` is `‖Tψ‖ ^ 2`. -/
lemma re_inner_apply_sq_eq_norm_sq :
    (⟪(ψ : H), T ⟨T ψ, hTψ⟩⟫_ℂ).re = ‖T ψ‖ ^ 2 := by
  rw [← hT ψ ⟨T ψ, hTψ⟩, inner_self_eq_norm_sq_to_K]
  rw [sq, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]

include hψ_norm

/-- When `Tψ ∈ T.domain`, variance equals `⟨T^2⟩_ψ - ⟨T⟩_ψ ^ 2`. -/
lemma variance_eq_re_inner_sub_expectedValue_sq :
    variance T ψ =
      (⟪(ψ : H), T ⟨T ψ, hTψ⟩⟫_ℂ).re - expectedValue T ψ ^ 2 := by
  rw [variance_eq_norm_sq_sub_expectedValue_sq T hT ψ hψ_norm,
    re_inner_apply_sq_eq_norm_sq T hT ψ hTψ]

end SecondOrder

end
end LinearPMap
