/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
public import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!
# State observables

For a partial linear map `T` on a complex inner product space and a vector `ψ ∈ T.domain`, this
file defines the expectation value, centered vector, variance, and standard deviation of `T` in
the state `ψ`.

The state variance is the first-order quantity `\|Tψ - ⟨T⟩_ψ ψ\|^2`. It only requires
`ψ ∈ T.domain`. The familiar second-order expression
`⟨T^2⟩_ψ - ⟨T⟩_ψ^2` is related to it later in the file, under the additional assumption
`Tψ ∈ T.domain`.

## Main definitions

- `LinearPMap.expectedValue`: the real part of the quadratic form
  `⟪ψ, Tψ⟫_ℂ`.
- `LinearPMap.stateExpectedValue`: the same quantity, with state-observable naming.
- `LinearPMap.centered`: the centered vector `Tψ - ⟨T⟩ψ`.
- `LinearPMap.stateVariance` and `LinearPMap.stateStdDev`: state variance and standard deviation.
- `LinearPMap.squaredExpectedValue`, `LinearPMap.variance`, and `LinearPMap.stdDev`: the
  second-order versions available when `Tψ ∈ T.domain`.
- `LinearPMap.IsEigenvector`: the eigenvector predicate for a partial linear map.

## Main statements

- `LinearPMap.expectedValue_eq_inner`: for symmetric `T`, the complex inner product is real and
  equals the real expectation value coerced to `ℂ`.
- `LinearPMap.stateVariance_eq_norm_sq_sub_stateExpectedValue_sq`: for a unit vector, the variance
  is `‖Tψ‖ ^ 2 - ⟨T⟩_ψ ^ 2`.
- `LinearPMap.stateVariance_eq_variance_of_mem_domain`: the first-order and second-order variances
  agree when `Tψ ∈ T.domain`.
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

/-- A nonzero vector in the domain of `T` satisfying `T ψ = μ • ψ`. -/
def IsEigenvector (T : H →ₗ.[ℂ] H) (ψ : T.domain) (μ : ℂ) : Prop :=
  T ψ = μ • (ψ : H) ∧ (ψ : H) ≠ 0

/-- The eigenvalue equation for a partial-map eigenvector. -/
lemma IsEigenvector.apply_eq {T : H →ₗ.[ℂ] H} {ψ : T.domain} {μ : ℂ}
    (hψ : T.IsEigenvector ψ μ) :
    T ψ = μ • (ψ : H) :=
  hψ.1

/-- A partial-map eigenvector is nonzero. -/
lemma IsEigenvector.ne_zero {T : H →ₗ.[ℂ] H} {ψ : T.domain} {μ : ℂ}
    (hψ : T.IsEigenvector ψ μ) :
    (ψ : H) ≠ 0 :=
  hψ.2

private lemma conj_inner_apply_self_eq_of_isSymmetric (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : H) (hψ : ψ ∈ T.domain) :
    (starRingEnd ℂ) ⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ =
      ⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ := by
  simpa [inner_conj_symm] using hT ⟨ψ, hψ⟩ ⟨ψ, hψ⟩

/-- Expectation value `re ⟪ψ, Tψ⟫_ℂ` for `ψ ∈ T.domain`.

For symmetric `T`, this agrees with `⟪ψ, Tψ⟫_ℂ` after coercion from `ℝ`;
see `expectedValue_eq_inner`. -/
def expectedValue (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) : ℝ :=
  (⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ).re

/-- The expectation value, unfolded as a real part. -/
lemma expectedValue_eq_re_inner (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) :
    expectedValue T ψ hψ = (⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ).re :=
  rfl

/-- If `T` is symmetric, `⟪ψ, Tψ⟫_ℂ` is the expectation value, coerced to `ℂ`. -/
lemma expectedValue_eq_inner (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : H) (hψ : ψ ∈ T.domain) :
    ⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ = (expectedValue T ψ hψ : ℂ) := by
  have h_re : ((⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ).re : ℂ) =
      ⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ :=
    Complex.conj_eq_iff_re.mp
      (by simpa using conj_inner_apply_self_eq_of_isSymmetric T hT ψ hψ)
  simpa [expectedValue] using h_re.symm

/-- Reverse orientation of `LinearPMap.expectedValue_eq_inner`. -/
lemma inner_eq_expectedValue (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : H) (hψ : ψ ∈ T.domain) :
    (expectedValue T ψ hψ : ℂ) = ⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ :=
  (expectedValue_eq_inner T hT ψ hψ).symm

/-- State-observable notation for the expectation value. -/
def stateExpectedValue (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) : ℝ :=
  expectedValue T ψ hψ

/-- State-level expectation values reduce to quadratic-form expectation values. -/
lemma stateExpectedValue_eq_expectedValue (T : H →ₗ.[ℂ] H) (ψ : H)
    (hψ : ψ ∈ T.domain) :
    stateExpectedValue T ψ hψ = expectedValue T ψ hψ :=
  rfl

/-- For symmetric partial linear maps, the complex inner product is the state expectation value. -/
lemma stateExpectedValue_eq_inner (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : H) (hψ : ψ ∈ T.domain) :
    ⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ = (stateExpectedValue T ψ hψ : ℂ) := by
  simpa [stateExpectedValue] using expectedValue_eq_inner T hT ψ hψ

/-- Reverse orientation of `LinearPMap.stateExpectedValue_eq_inner`. -/
lemma inner_eq_stateExpectedValue (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : H) (hψ : ψ ∈ T.domain) :
    (stateExpectedValue T ψ hψ : ℂ) = ⟪ψ, (T ⟨ψ, hψ⟩ : H)⟫_ℂ :=
  (stateExpectedValue_eq_inner T hT ψ hψ).symm

/-- The centered vector `Tψ - ⟨T⟩_ψ ψ`. -/
def centered (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) : H :=
  T ⟨ψ, hψ⟩ - (stateExpectedValue T ψ hψ : ℂ) • ψ

/-- The centered vector, unfolded to its raw expression. -/
lemma centered_eq (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) :
    centered T ψ hψ = (T ⟨ψ, hψ⟩ : H) - (stateExpectedValue T ψ hψ : ℂ) • ψ :=
  rfl

/-- A centered vector vanishes exactly when `Tψ = ⟨T⟩_ψ ψ`. -/
lemma centered_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) :
    centered T ψ hψ = 0 ↔
      (T ⟨ψ, hψ⟩ : H) = (stateExpectedValue T ψ hψ : ℂ) • ψ := by
  rw [centered_eq, sub_eq_zero]

/-- For a unit vector and symmetric `T`, the centered vector is orthogonal to the state. -/
lemma inner_state_centered_eq_zero (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : H) (hψ : ψ ∈ T.domain) (hψ_norm : ‖ψ‖ = 1) :
    ⟪ψ, centered T ψ hψ⟫_ℂ = 0 := by
  rw [centered_eq, inner_sub_right, inner_smul_right, stateExpectedValue_eq_inner T hT ψ hψ]
  simp [hψ_norm, inner_self_eq_norm_sq_to_K]

/-- The conjugate orientation of `LinearPMap.inner_state_centered_eq_zero`. -/
lemma inner_centered_state_eq_zero (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
    (ψ : H) (hψ : ψ ∈ T.domain) (hψ_norm : ‖ψ‖ = 1) :
    ⟪centered T ψ hψ, ψ⟫_ℂ = 0 := by
  rw [centered_eq, inner_sub_left, inner_smul_left]
  have hμ := stateExpectedValue_eq_inner T hT ψ hψ
  have hμ' : ⟪(T ⟨ψ, hψ⟩ : H), ψ⟫_ℂ = (stateExpectedValue T ψ hψ : ℂ) := by
    simpa [inner_conj_symm] using congrArg star hμ
  rw [hμ']
  simp [hψ_norm, inner_self_eq_norm_sq_to_K]

/-- State variance `‖Tψ - ⟨T⟩_ψ ψ‖ ^ 2`; only `ψ ∈ T.domain` is required. -/
def stateVariance (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) : ℝ :=
  ‖centered T ψ hψ‖ ^ 2

/-- The state variance is the squared norm of the centered vector. -/
lemma stateVariance_eq_centered_norm_sq (T : H →ₗ.[ℂ] H) (ψ : H)
    (hψ : ψ ∈ T.domain) :
    stateVariance T ψ hψ = ‖centered T ψ hψ‖ ^ 2 :=
  rfl

/-- `stateVariance` with `centered` unfolded to `Tψ - ⟨T⟩_ψ • ψ`. -/
lemma stateVariance_eq_norm_sub_sq (T : H →ₗ.[ℂ] H) (ψ : H)
    (hψ : ψ ∈ T.domain) :
    stateVariance T ψ hψ =
      ‖(T ⟨ψ, hψ⟩ : H) - (stateExpectedValue T ψ hψ : ℂ) • ψ‖ ^ 2 :=
  rfl

/-- For symmetric `T` and `‖ψ‖ = 1`, state variance equals `‖Tψ‖ ^ 2 - ⟨T⟩_ψ ^ 2`. -/
lemma stateVariance_eq_norm_sq_sub_stateExpectedValue_sq (T : H →ₗ.[ℂ] H)
    (hT : T.IsSymmetric) (ψ : H) (hψ : ψ ∈ T.domain) (hψ_norm : ‖ψ‖ = 1) :
    stateVariance T ψ hψ = ‖(T ⟨ψ, hψ⟩ : H)‖ ^ 2 - stateExpectedValue T ψ hψ ^ 2 := by
  let μ := stateExpectedValue T ψ hψ
  let a : H := T ⟨ψ, hψ⟩
  have hμ_right : ⟪ψ, a⟫_ℂ = (μ : ℂ) := by
    simpa [a, μ] using stateExpectedValue_eq_inner T hT ψ hψ
  have hμ_left : ⟪a, ψ⟫_ℂ = (μ : ℂ) := by
    simpa [inner_conj_symm] using congrArg star hμ_right
  have h_re_inner_centered : (⟪a, (μ : ℂ) • ψ⟫_ℂ).re = μ ^ 2 := by
    rw [inner_smul_right, hμ_left]
    simp [μ]
    ring
  have h_norm_centered_smul : ‖(μ : ℂ) • ψ‖ ^ 2 = μ ^ 2 := by
    rw [norm_smul, hψ_norm]
    simp [μ]
  have h_norm_sub_sq :
      ‖a - (μ : ℂ) • ψ‖ ^ 2 =
        ‖a‖ ^ 2 - 2 * (⟪a, (μ : ℂ) • ψ⟫_ℂ).re + ‖(μ : ℂ) • ψ‖ ^ 2 := by
    simpa using (norm_sub_sq (𝕜 := ℂ) a ((μ : ℂ) • ψ))
  rw [stateVariance_eq_norm_sub_sq, h_norm_sub_sq, h_re_inner_centered,
    h_norm_centered_smul]
  ring

/-- State variance is nonnegative. -/
lemma stateVariance_nonneg (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) :
    0 ≤ stateVariance T ψ hψ := by
  rw [stateVariance_eq_centered_norm_sq]
  exact sq_nonneg _

/-- Zero variance is the same as a zero centered vector. -/
lemma stateVariance_eq_zero_iff_centered_eq_zero (T : H →ₗ.[ℂ] H)
    (ψ : H) (hψ : ψ ∈ T.domain) :
    stateVariance T ψ hψ = 0 ↔ centered T ψ hψ = 0 := by
  rw [stateVariance_eq_centered_norm_sq]
  exact sq_eq_zero_iff.trans norm_eq_zero

/-- Zero variance is the same as `Tψ = ⟨T⟩_ψ ψ`. -/
lemma stateVariance_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) :
    stateVariance T ψ hψ = 0 ↔
      (T ⟨ψ, hψ⟩ : H) = (stateExpectedValue T ψ hψ : ℂ) • ψ := by
  rw [stateVariance_eq_zero_iff_centered_eq_zero, centered_eq_zero_iff]

/-- For `‖ψ‖ = 1`, zero variance iff `ψ` is an eigenvector with eigenvalue `⟨T⟩_ψ`. -/
lemma stateVariance_eq_zero_iff_isEigenvector (T : H →ₗ.[ℂ] H)
    (ψ : H) (hψ : ψ ∈ T.domain) (hψ_norm : ‖ψ‖ = 1) :
    stateVariance T ψ hψ = 0 ↔
      T.IsEigenvector ⟨ψ, hψ⟩ (stateExpectedValue T ψ hψ : ℂ) := by
  rw [stateVariance_eq_zero_iff]
  constructor
  · intro h_centered
    refine ⟨h_centered, ?_⟩
    intro h_zero
    have h_zero' : ψ = 0 := by simpa using h_zero
    have h_norm_zero : ‖ψ‖ = 0 := by simp [h_zero']
    have : (0 : ℝ) = 1 := h_norm_zero.symm.trans hψ_norm
    norm_num at this
  · intro h_eigen
    exact h_eigen.1

/-- Standard deviation `√(state variance)` for `ψ ∈ T.domain`. -/
def stateStdDev (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) : ℝ :=
  Real.sqrt (stateVariance T ψ hψ)

/-- The state standard deviation, unfolded to the square root of the variance. -/
lemma stateStdDev_eq_sqrt_stateVariance (T : H →ₗ.[ℂ] H) (ψ : H)
    (hψ : ψ ∈ T.domain) :
    stateStdDev T ψ hψ = Real.sqrt (stateVariance T ψ hψ) :=
  rfl

/-- State standard deviation is nonnegative. -/
lemma stateStdDev_nonneg (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) :
    0 ≤ stateStdDev T ψ hψ := by
  rw [stateStdDev_eq_sqrt_stateVariance]
  exact Real.sqrt_nonneg _

@[simp]
lemma stateStdDev_sq (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) :
    stateStdDev T ψ hψ ^ 2 = stateVariance T ψ hψ := by
  rw [stateStdDev_eq_sqrt_stateVariance, Real.sq_sqrt]
  exact stateVariance_nonneg T ψ hψ

/-- Zero standard deviation is the same as a zero centered vector. -/
lemma stateStdDev_eq_zero_iff_centered_eq_zero (T : H →ₗ.[ℂ] H)
    (ψ : H) (hψ : ψ ∈ T.domain) :
    stateStdDev T ψ hψ = 0 ↔ centered T ψ hψ = 0 := by
  rw [stateStdDev_eq_sqrt_stateVariance, Real.sqrt_eq_zero]
  · exact stateVariance_eq_zero_iff_centered_eq_zero T ψ hψ
  · exact stateVariance_nonneg T ψ hψ

/-- Zero standard deviation is the same as `Tψ = ⟨T⟩_ψ ψ`. -/
lemma stateStdDev_eq_zero_iff (T : H →ₗ.[ℂ] H) (ψ : H) (hψ : ψ ∈ T.domain) :
    stateStdDev T ψ hψ = 0 ↔
      (T ⟨ψ, hψ⟩ : H) = (stateExpectedValue T ψ hψ : ℂ) • ψ := by
  rw [stateStdDev_eq_zero_iff_centered_eq_zero, centered_eq, sub_eq_zero]

/-- For `‖ψ‖ = 1`, zero standard deviation iff the eigenvector condition holds. -/
lemma stateStdDev_eq_zero_iff_isEigenvector (T : H →ₗ.[ℂ] H)
    (ψ : H) (hψ : ψ ∈ T.domain) (hψ_norm : ‖ψ‖ = 1) :
    stateStdDev T ψ hψ = 0 ↔
      T.IsEigenvector ⟨ψ, hψ⟩ (stateExpectedValue T ψ hψ : ℂ) := by
  rw [stateStdDev_eq_zero_iff]
  constructor
  · intro h_centered
    refine ⟨h_centered, ?_⟩
    intro h_zero
    have h_zero' : ψ = 0 := by simpa using h_zero
    have h_norm_zero : ‖ψ‖ = 0 := by simp [h_zero']
    have : (0 : ℝ) = 1 := h_norm_zero.symm.trans hψ_norm
    norm_num at this
  · intro h_eigen
    exact h_eigen.1

section SecondOrder

variable (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric)
variable (ψ : H) (hψ : ψ ∈ T.domain)
variable (hTψ : (T ⟨ψ, hψ⟩ : H) ∈ T.domain)
variable (hψ_norm : ‖ψ‖ = 1)

/-- Second moment `re ⟪ψ, T(Tψ)⟫` when `Tψ ∈ T.domain`. -/
def squaredExpectedValue : ℝ :=
  (⟪ψ, (T ⟨(T ⟨ψ, hψ⟩ : H), hTψ⟩ : H)⟫_ℂ).re

/-- The second moment, unfolded as a real part. -/
lemma squaredExpectedValue_eq_re_inner :
    squaredExpectedValue T ψ hψ hTψ =
      (⟪ψ, (T ⟨(T ⟨ψ, hψ⟩ : H), hTψ⟩ : H)⟫_ℂ).re :=
  rfl

/-- Second-order variance `squaredExpectedValue - ⟨T⟩_ψ ^ 2` when `Tψ ∈ T.domain`. -/
def variance : ℝ :=
  squaredExpectedValue T ψ hψ hTψ - expectedValue T ψ hψ ^ 2

/-- The second-order variance, unfolded. -/
lemma variance_eq_squaredExpectedValue_sub_expectedValue_sq :
    variance T ψ hψ hTψ = squaredExpectedValue T ψ hψ hTψ - expectedValue T ψ hψ ^ 2 :=
  rfl

/-- Square root of the second-order variance. -/
def stdDev : ℝ :=
  Real.sqrt (variance T ψ hψ hTψ)

/-- The second-order standard deviation, unfolded. -/
lemma stdDev_eq_sqrt_variance :
    stdDev T ψ hψ hTψ = Real.sqrt (variance T ψ hψ hTψ) :=
  rfl

/-- Second-order standard deviation is nonnegative. -/
lemma stdDev_nonneg :
    0 ≤ stdDev T ψ hψ hTψ := by
  rw [stdDev_eq_sqrt_variance]
  exact Real.sqrt_nonneg _

include hT

/-- For symmetric `T`, the second moment is `‖Tψ‖ ^ 2`. -/
lemma squaredExpectedValue_eq_norm_sq :
    squaredExpectedValue T ψ hψ hTψ = ‖(T ⟨ψ, hψ⟩ : H)‖ ^ 2 := by
  unfold squaredExpectedValue
  rw [← hT ⟨ψ, hψ⟩ ⟨(T ⟨ψ, hψ⟩ : H), hTψ⟩, inner_self_eq_norm_sq_to_K]
  rw [sq, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]

/-- For symmetric `T`, the second-order variance is `‖Tψ‖ ^ 2 - ⟨T⟩_ψ ^ 2`. -/
lemma variance_eq_norm_sq_sub_expectedValue_sq :
    variance T ψ hψ hTψ = ‖(T ⟨ψ, hψ⟩ : H)‖ ^ 2 - expectedValue T ψ hψ ^ 2 := by
  rw [variance, squaredExpectedValue_eq_norm_sq T hT ψ hψ hTψ]

include hψ_norm

/-- For unit `ψ`, the state variance agrees with the second-order variance. -/
lemma stateVariance_eq_variance_of_mem_domain :
    stateVariance T ψ hψ = variance T ψ hψ hTψ := by
  rw [stateVariance_eq_norm_sq_sub_stateExpectedValue_sq T hT ψ hψ hψ_norm,
    variance_eq_norm_sq_sub_expectedValue_sq T hT ψ hψ hTψ,
    stateExpectedValue_eq_expectedValue]

/-- For unit `ψ`, the second-order variance is nonnegative. -/
lemma variance_nonneg_of_norm_eq_one :
    0 ≤ variance T ψ hψ hTψ := by
  rw [← stateVariance_eq_variance_of_mem_domain T hT ψ hψ hTψ hψ_norm]
  exact stateVariance_nonneg T ψ hψ

/-- For unit `ψ`, zero second-order variance is the same as a zero centered vector. -/
lemma variance_eq_zero_iff_centered_eq_zero_of_norm_eq_one :
    variance T ψ hψ hTψ = 0 ↔ centered T ψ hψ = 0 := by
  rw [← stateVariance_eq_variance_of_mem_domain T hT ψ hψ hTψ hψ_norm,
    stateVariance_eq_zero_iff_centered_eq_zero]

/-- For unit `ψ`, zero second-order variance is equivalent to the eigenvector condition. -/
lemma variance_eq_zero_iff_isEigenvector_of_norm_eq_one :
    variance T ψ hψ hTψ = 0 ↔
      T.IsEigenvector ⟨ψ, hψ⟩ (stateExpectedValue T ψ hψ : ℂ) := by
  rw [← stateVariance_eq_variance_of_mem_domain T hT ψ hψ hTψ hψ_norm,
    stateVariance_eq_zero_iff_isEigenvector T ψ hψ hψ_norm]

/-- The corresponding equality of standard deviations. -/
lemma stateStdDev_eq_stdDev_of_mem_domain :
    stateStdDev T ψ hψ = stdDev T ψ hψ hTψ := by
  rw [stateStdDev, stdDev, stateVariance_eq_variance_of_mem_domain T hT ψ hψ hTψ hψ_norm]

@[simp]
lemma stdDev_sq_of_norm_eq_one :
    stdDev T ψ hψ hTψ ^ 2 = variance T ψ hψ hTψ := by
  rw [← stateStdDev_eq_stdDev_of_mem_domain T hT ψ hψ hTψ hψ_norm, stateStdDev_sq,
    stateVariance_eq_variance_of_mem_domain T hT ψ hψ hTψ hψ_norm]

/-- For unit `ψ`, zero second-order standard deviation is the same as a zero centered vector. -/
lemma stdDev_eq_zero_iff_centered_eq_zero_of_norm_eq_one :
    stdDev T ψ hψ hTψ = 0 ↔ centered T ψ hψ = 0 := by
  rw [← stateStdDev_eq_stdDev_of_mem_domain T hT ψ hψ hTψ hψ_norm,
    stateStdDev_eq_zero_iff_centered_eq_zero]

/-- For unit `ψ`, zero second-order standard deviation is equivalent to the eigenvector
condition. -/
lemma stdDev_eq_zero_iff_isEigenvector_of_norm_eq_one :
    stdDev T ψ hψ hTψ = 0 ↔
      T.IsEigenvector ⟨ψ, hψ⟩ (stateExpectedValue T ψ hψ : ℂ) := by
  rw [← stateStdDev_eq_stdDev_of_mem_domain T hT ψ hψ hTψ hψ_norm,
    stateStdDev_eq_zero_iff_isEigenvector T ψ hψ hψ_norm]

end SecondOrder

end
end LinearPMap
