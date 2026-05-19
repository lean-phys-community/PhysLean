/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Krystian Nowakowski
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
/-!
# Expectation values and centered vectors

For a partial linear map `T` on a complex inner product space and `ψ ∈ T.domain`, this file
defines the expectation value and the centered vector `Tψ - ⟨T⟩_ψ ψ`.

## Main definitions

- `LinearPMap.expectedValue`: the real part of `⟪ψ, Tψ⟫_ℂ`.
- `LinearPMap.stateExpectedValue`: the same quantity, with state-observable naming.
- `LinearPMap.centered`: the centered vector `Tψ - ⟨T⟩ψ`.

## Main statements

- `LinearPMap.expectedValue_eq_inner`: for symmetric `T`, the complex inner product is real and
  equals the real expectation value coerced to `ℂ`.

## References

- [B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 12][hall2013quantum].

-/

@[expose] public section

namespace LinearPMap

open InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

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

/-- Same as `expectedValue`; kept for state-observable naming. -/
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

end
end LinearPMap
