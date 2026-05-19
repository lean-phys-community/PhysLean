/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Krystian Nowakowski
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.ExpectedValue
public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.IsEigenvector
public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.StateVariance
public import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!
# Second-order state observables

When `Tψ ∈ T.domain`, the familiar expression `⟨T^2⟩_ψ - ⟨T⟩_ψ^2` is available as
`LinearPMap.variance`. For a unit vector it agrees with the first-order state variance from
`StateVariance`.

## Main definitions

- `LinearPMap.variance` and `LinearPMap.stdDev`: second-order variance and standard deviation
  when `Tψ ∈ T.domain`.

## Main statements

- `LinearPMap.stateVariance_eq_variance_of_mem_domain`: the first-order and second-order variances
  agree when `Tψ ∈ T.domain` and `‖ψ‖ = 1`.

## References

- [B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 12][hall2013quantum].

-/

@[expose] public section

namespace LinearPMap

open InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section SecondOrder

variable (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
variable (ψ : T.domain)
variable (hTψ : T ψ ∈ T.domain)
variable (hψ_norm : ‖(ψ : H)‖ = 1)

/-- Second-order variance `⟨T^2⟩_ψ - ⟨T⟩_ψ ^ 2` when `Tψ ∈ T.domain`.

Agrees with `stateVariance` only when `T` is symmetric, `‖ψ‖ = 1`, and `Tψ ∈ T.domain`;
see `stateVariance_eq_variance_of_mem_domain`. -/
def variance : ℝ :=
  (⟪(ψ : H), T ⟨T ψ, hTψ⟩⟫_ℂ).re - expectedValue T ψ ^ 2

/-- The second-order variance, unfolded. -/
lemma variance_eq_re_inner_sub_expectedValue_sq :
    variance T ψ hTψ =
      (⟪(ψ : H), T ⟨T ψ, hTψ⟩⟫_ℂ).re - expectedValue T ψ ^ 2 :=
  rfl

/-- Square root of the second-order variance. -/
def stdDev : ℝ :=
  Real.sqrt (variance T ψ hTψ)

/-- The second-order standard deviation, unfolded. -/
lemma stdDev_eq_sqrt_variance :
    stdDev T ψ hTψ = Real.sqrt (variance T ψ hTψ) :=
  rfl

/-- Second-order standard deviation is nonnegative. -/
lemma stdDev_nonneg :
    0 ≤ stdDev T ψ hTψ := by
  rw [stdDev_eq_sqrt_variance]
  exact Real.sqrt_nonneg _

include hT

/-- For symmetric `T`, `re ⟪ψ, T(Tψ)⟫` is `‖Tψ‖ ^ 2`. -/
lemma re_inner_apply_sq_eq_norm_sq :
    (⟪(ψ : H), T ⟨T ψ, hTψ⟩⟫_ℂ).re = ‖T ψ‖ ^ 2 := by
  rw [← hT ψ ⟨T ψ, hTψ⟩, inner_self_eq_norm_sq_to_K]
  rw [sq, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]

/-- For symmetric `T`, the second-order variance is `‖Tψ‖ ^ 2 - ⟨T⟩_ψ ^ 2`. -/
lemma variance_eq_norm_sq_sub_expectedValue_sq :
    variance T ψ hTψ = ‖T ψ‖ ^ 2 - expectedValue T ψ ^ 2 := by
  rw [variance, re_inner_apply_sq_eq_norm_sq T hT ψ hTψ]

include hψ_norm

/-- For unit `ψ`, the state variance agrees with the second-order variance. -/
lemma stateVariance_eq_variance_of_mem_domain :
    stateVariance T ψ = variance T ψ hTψ := by
  rw [stateVariance_eq_norm_sq_sub_stateExpectedValue_sq T hT ψ hψ_norm,
    variance_eq_norm_sq_sub_expectedValue_sq T hT ψ hTψ,
    stateExpectedValue_eq_expectedValue]

/-- For unit `ψ`, the second-order variance is nonnegative. -/
lemma variance_nonneg_of_norm_eq_one :
    0 ≤ variance T ψ hTψ := by
  rw [← stateVariance_eq_variance_of_mem_domain T hT ψ hTψ hψ_norm]
  exact stateVariance_nonneg T ψ

/-- For unit `ψ`, zero second-order variance is the same as a zero centered vector. -/
lemma variance_eq_zero_iff_centered_eq_zero_of_norm_eq_one :
    variance T ψ hTψ = 0 ↔ centered T ψ = 0 := by
  rw [← stateVariance_eq_variance_of_mem_domain T hT ψ hTψ hψ_norm,
    stateVariance_eq_zero_iff_centered_eq_zero]

/-- For unit `ψ`, zero second-order variance is equivalent to the eigenvector condition. -/
lemma variance_eq_zero_iff_isEigenvector_of_norm_eq_one :
    variance T ψ hTψ = 0 ↔
      T.IsEigenvector ψ (stateExpectedValue T ψ : ℂ) := by
  rw [← stateVariance_eq_variance_of_mem_domain T hT ψ hTψ hψ_norm,
    stateVariance_eq_zero_iff_isEigenvector T ψ hψ_norm]

/-- The corresponding equality of standard deviations. -/
lemma stateStdDev_eq_stdDev_of_mem_domain :
    stateStdDev T ψ = stdDev T ψ hTψ := by
  rw [stateStdDev, stdDev, stateVariance_eq_variance_of_mem_domain T hT ψ hTψ hψ_norm]

@[simp]
lemma stdDev_sq_of_norm_eq_one :
    stdDev T ψ hTψ ^ 2 = variance T ψ hTψ := by
  rw [← stateStdDev_eq_stdDev_of_mem_domain T hT ψ hTψ hψ_norm, stateStdDev_sq,
    stateVariance_eq_variance_of_mem_domain T hT ψ hTψ hψ_norm]

/-- For unit `ψ`, zero second-order standard deviation is the same as a zero centered vector. -/
lemma stdDev_eq_zero_iff_centered_eq_zero_of_norm_eq_one :
    stdDev T ψ hTψ = 0 ↔ centered T ψ = 0 := by
  rw [← stateStdDev_eq_stdDev_of_mem_domain T hT ψ hTψ hψ_norm,
    stateStdDev_eq_zero_iff_centered_eq_zero]

/-- For unit `ψ`, zero second-order standard deviation is equivalent to the eigenvector
condition. -/
lemma stdDev_eq_zero_iff_isEigenvector_of_norm_eq_one :
    stdDev T ψ hTψ = 0 ↔
      T.IsEigenvector ψ (stateExpectedValue T ψ : ℂ) := by
  rw [← stateStdDev_eq_stdDev_of_mem_domain T hT ψ hTψ hψ_norm,
    stateStdDev_eq_zero_iff_isEigenvector T ψ hψ_norm]

end SecondOrder

end
end LinearPMap
