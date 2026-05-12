/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables
/-!
# Uncertainty bounds for partial linear maps

This file proves abstract uncertainty bounds for symmetric partial linear maps on complex inner
product spaces. The statements are independent of any concrete position or momentum operator.

The state-level results use only the domain assumptions needed to form the centered vectors. The
raw-commutator results add the second-order domain hypotheses required to apply `A` to `Bψ` and
`B` to `Aψ`.

## Main definitions

- `LinearPMap.stateCovariance`: the real part of the inner product of two centered vectors.

## Main statements

- `LinearPMap.inner_centered_commutator_of_raw_commutator`: a raw commutator expectation gives the
  corresponding centered commutator expectation.
- `LinearPMap.state_uncertainty_squared_of_centered_commutator`: the Robertson squared bound from a
  centered commutator identity.
- `LinearPMap.state_uncertainty_squared_with_covariance_of_centered_commutator`: the strengthened
  Robertson-Schrodinger bound.
- `LinearPMap.state_uncertainty_of_centered_commutator`: the standard-deviation form of the bound.
- `LinearPMap.state_uncertainty_squared_of_raw_commutator`,
  `LinearPMap.state_uncertainty_squared_with_covariance_of_raw_commutator`, and
  `LinearPMap.state_uncertainty_of_raw_commutator`: variants using a raw commutator expectation.

## References

- [H. P. Robertson, *The Uncertainty Principle* (1929)][robertson1929uncertainty].
- [E. Schrodinger, *Zum Heisenbergschen Unscharfeprinzip* (1930)][schrodinger1930heisenberg].
- [B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 12][hall2013quantum].
-/

@[expose] public section

namespace LinearPMap

open InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Covariance

variable (A B : H →ₗ.[ℂ] H)
variable (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain)

/-- State covariance, defined as the real part of the centered inner product. -/
def stateCovariance : ℝ :=
  (⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ).re

/-- State covariance, unfolded to the real part of the centered inner product. -/
lemma stateCovariance_eq_re_inner_centered :
    stateCovariance A B ψ hψA hψB =
      (⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ).re :=
  rfl

/-- Swapping the two observables does not change the state covariance. -/
lemma stateCovariance_comm :
    stateCovariance A B ψ hψA hψB = stateCovariance B A ψ hψB hψA := by
  rw [stateCovariance_eq_re_inner_centered, stateCovariance_eq_re_inner_centered]
  calc
    (⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ).re =
        (((starRingEnd ℂ) ⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ)).re := by
      rw [inner_conj_symm]
    _ = (⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ).re := by
      change (star ⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ).re =
        (⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ).re
      rw [Complex.star_def, Complex.conj_re]

/-- State covariance as the real part of the symmetrized centered inner product. -/
lemma stateCovariance_eq_re_symm_centered :
    stateCovariance A B ψ hψA hψB =
      ((⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ +
        ⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ).re) / 2 := by
  let z : ℂ := ⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ
  have hz : ⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ = star z := by
    simp [z, inner_conj_symm]
  rw [stateCovariance_eq_re_inner_centered, hz]
  change z.re = ((z + star z).re) / 2
  simp

@[simp]
lemma stateCovariance_self_eq_stateVariance (A : H →ₗ.[ℂ] H)
    (ψ : H) (hψ : ψ ∈ A.domain) :
    stateCovariance A A ψ hψ hψ = stateVariance A ψ hψ := by
  rw [stateCovariance_eq_re_inner_centered, stateVariance_eq_centered_norm_sq,
    inner_self_eq_norm_sq_to_K]
  rw [sq, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]

end Covariance

private lemma inner_im_of_commutator_eq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    (⟪u, v⟫_ℂ).im = c / 2 := by
  have h_conj_im : (⟪v, u⟫_ℂ).im = -(⟪u, v⟫_ℂ).im := by
    rw [(inner_conj_symm (𝕜 := ℂ) v u).symm, Complex.conj_im]
  have h_im := congrArg Complex.im h_comm
  rw [Complex.sub_im] at h_im
  simp at h_im
  rw [h_conj_im] at h_im
  linarith

private lemma inner_norm_sq_eq_re_sq_add_commutator_half_sq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    ‖⟪u, v⟫_ℂ‖ ^ 2 = (⟪u, v⟫_ℂ).re ^ 2 + (c / 2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, inner_im_of_commutator_eq h_comm]
  ring

private lemma sub_expectation_commutator_eq_raw
    (ψ a b : H) (μa μb : ℝ)
    (hμa_right : ⟪ψ, a⟫_ℂ = (μa : ℂ))
    (hμa_left : ⟪a, ψ⟫_ℂ = (μa : ℂ))
    (hμb_right : ⟪ψ, b⟫_ℂ = (μb : ℂ))
    (hμb_left : ⟪b, ψ⟫_ℂ = (μb : ℂ))
    (hψ_norm : ‖ψ‖ = 1) :
    ⟪a - (μa : ℂ) • ψ, b - (μb : ℂ) • ψ⟫_ℂ -
        ⟪b - (μb : ℂ) • ψ, a - (μa : ℂ) • ψ⟫_ℂ =
      ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ := by
  calc
    ⟪a - (μa : ℂ) • ψ, b - (μb : ℂ) • ψ⟫_ℂ -
        ⟪b - (μb : ℂ) • ψ, a - (μa : ℂ) • ψ⟫_ℂ =
          (⟪a, b⟫_ℂ - (μb : ℂ) * ⟪a, ψ⟫_ℂ - star (μa : ℂ) * ⟪ψ, b⟫_ℂ +
            star (μa : ℂ) * (μb : ℂ) * ⟪ψ, ψ⟫_ℂ) -
          (⟪b, a⟫_ℂ - (μa : ℂ) * ⟪b, ψ⟫_ℂ - star (μb : ℂ) * ⟪ψ, a⟫_ℂ +
            star (μb : ℂ) * (μa : ℂ) * ⟪ψ, ψ⟫_ℂ) := by
              simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
              simp [mul_comm, mul_assoc]
              ring_nf
    _ = ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ := by
          rw [hμa_right, hμa_left, hμb_right, hμb_left, inner_self_eq_norm_sq_to_K,
            hψ_norm]
          simp
          ring

private lemma raw_commutator_eq_of_symmetric
    (A B : H →ₗ.[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : H) {a b : H} (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain)
    (hBA : a ∈ B.domain) (hAB : b ∈ A.domain)
    (ha : a = A ⟨ψ, hψA⟩) (hb : b = B ⟨ψ, hψB⟩)
    {c : ℝ}
    (h_raw : ⟪ψ, A ⟨b, hAB⟩ - B ⟨a, hBA⟩⟫_ℂ = Complex.I * c) :
    ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ = Complex.I * c := by
  subst a
  subst b
  have ha_pairing :
      ⟪A ⟨ψ, hψA⟩, B ⟨ψ, hψB⟩⟫_ℂ =
        ⟪ψ, A ⟨B ⟨ψ, hψB⟩, hAB⟩⟫_ℂ := by
    simpa using hA ⟨ψ, hψA⟩ ⟨B ⟨ψ, hψB⟩, hAB⟩
  have hb_pairing :
      ⟪B ⟨ψ, hψB⟩, A ⟨ψ, hψA⟩⟫_ℂ =
        ⟪ψ, B ⟨A ⟨ψ, hψA⟩, hBA⟩⟫_ℂ := by
    simpa using hB ⟨ψ, hψB⟩ ⟨A ⟨ψ, hψA⟩, hBA⟩
  calc
    ⟪A ⟨ψ, hψA⟩, B ⟨ψ, hψB⟩⟫_ℂ -
        ⟪B ⟨ψ, hψB⟩, A ⟨ψ, hψA⟩⟫_ℂ =
      ⟪ψ, A ⟨B ⟨ψ, hψB⟩, hAB⟩⟫_ℂ -
        ⟪ψ, B ⟨A ⟨ψ, hψA⟩, hBA⟩⟫_ℂ := by
          rw [ha_pairing, hb_pairing]
    _ = ⟪ψ, A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ⟨ψ, hψA⟩, hBA⟩⟫_ℂ := by
          rw [inner_sub_right]
    _ = Complex.I * c := h_raw

section RawCommutator

variable (A B : H →ₗ.[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
variable (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain)
variable (hψ_norm : ‖ψ‖ = 1)
variable (hBA : A ⟨ψ, hψA⟩ ∈ B.domain)
variable (hAB : B ⟨ψ, hψB⟩ ∈ A.domain)
variable {c : ℝ}
variable (h_raw :
  ⟪ψ, A ⟨(B ⟨ψ, hψB⟩ : H), hAB⟩ -
      B ⟨(A ⟨ψ, hψA⟩ : H), hBA⟩⟫_ℂ = Complex.I * c)

include hA hB hψ_norm hBA hAB h_raw

/-- A raw commutator expectation determines the centered commutator expectation. -/
lemma inner_centered_commutator_of_raw_commutator :
    ⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ -
        ⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ =
      Complex.I * c := by
  let a : H := A ⟨ψ, hψA⟩
  let b : H := B ⟨ψ, hψB⟩
  let μa : ℝ := stateExpectedValue A ψ hψA
  let μb : ℝ := stateExpectedValue B ψ hψB
  have hμa_right : ⟪ψ, a⟫_ℂ = (μa : ℂ) := by
    simpa [a, μa] using stateExpectedValue_eq_inner A hA ψ hψA
  have hμa_left : ⟪a, ψ⟫_ℂ = (μa : ℂ) := by
    have h_symm : ⟪a, ψ⟫_ℂ = ⟪ψ, a⟫_ℂ := by
      simpa [a] using hA ⟨ψ, hψA⟩ ⟨ψ, hψA⟩
    simpa [h_symm] using hμa_right
  have hμb_right : ⟪ψ, b⟫_ℂ = (μb : ℂ) := by
    simpa [b, μb] using stateExpectedValue_eq_inner B hB ψ hψB
  have hμb_left : ⟪b, ψ⟫_ℂ = (μb : ℂ) := by
    have h_symm : ⟪b, ψ⟫_ℂ = ⟪ψ, b⟫_ℂ := by
      simpa [b] using hB ⟨ψ, hψB⟩ ⟨ψ, hψB⟩
    simpa [h_symm] using hμb_right
  calc
    ⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ -
        ⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ =
      ⟪a - (μa : ℂ) • ψ, b - (μb : ℂ) • ψ⟫_ℂ -
        ⟪b - (μb : ℂ) • ψ, a - (μa : ℂ) • ψ⟫_ℂ := by
          rfl
    _ = ⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ :=
      sub_expectation_commutator_eq_raw ψ a b μa μb
        hμa_right hμa_left hμb_right hμb_left hψ_norm
    _ = Complex.I * c :=
      raw_commutator_eq_of_symmetric A B hA hB ψ hψA hψB hBA hAB rfl rfl h_raw

omit hA hB hψ_norm hBA hAB h_raw

end RawCommutator

private lemma commutator_half_sq_le_mul_norm_sq {u v : H} {c : ℝ}
    (h_comm : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * c) :
    (|c| / 2) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
  have h_sq : |c / 2| ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    have h_bound : |c / 2| ≤ ‖u‖ * ‖v‖ := by
      have h_im : |(⟪u, v⟫_ℂ).im| ≤ ‖u‖ * ‖v‖ :=
        le_trans (Complex.abs_im_le_norm ⟪u, v⟫_ℂ) (norm_inner_le_norm u v)
      rwa [inner_im_of_commutator_eq h_comm] at h_im
    have h_nonneg : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg u) (norm_nonneg v)
    nlinarith [abs_nonneg (c / 2), h_bound, h_nonneg]
  simpa [abs_div] using h_sq

private lemma sqrt_mul_ge_of_sq_ge {x y z : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hxy : z ^ 2 ≤ x * y) :
    z ≤ Real.sqrt x * Real.sqrt y := by
  have hs : Real.sqrt (z ^ 2) ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt hxy
  rw [Real.sqrt_sq hz, Real.sqrt_mul hx] at hs
  simpa [mul_comm] using hs

section CenteredBounds

variable (A B : H →ₗ.[ℂ] H)
variable (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain)
variable {c : ℝ}
variable (h_centered :
  ⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ -
    ⟪centered B ψ hψB, centered A ψ hψA⟫_ℂ =
      Complex.I * c)

include h_centered

/-- A centered commutator identity implies the squared Robertson uncertainty bound. -/
lemma state_uncertainty_squared_of_centered_commutator :
    stateVariance A ψ hψA * stateVariance B ψ hψB ≥ (|c| / 2) ^ 2 := by
  rw [stateVariance_eq_centered_norm_sq, stateVariance_eq_centered_norm_sq]
  have h_mul_sq :
      ‖centered A ψ hψA‖ ^ 2 * ‖centered B ψ hψB‖ ^ 2 =
        (‖centered A ψ hψA‖ * ‖centered B ψ hψB‖) ^ 2 := by
    ring
  rw [h_mul_sq]
  exact commutator_half_sq_le_mul_norm_sq h_centered

/-- A centered commutator identity implies the Robertson-Schrodinger uncertainty bound. -/
lemma state_uncertainty_squared_with_covariance_of_centered_commutator :
    stateVariance A ψ hψA * stateVariance B ψ hψB ≥
      (stateCovariance A B ψ hψA hψB) ^ 2 + (c / 2) ^ 2 := by
  rw [stateVariance_eq_centered_norm_sq, stateVariance_eq_centered_norm_sq]
  have h_mul_sq :
      ‖centered A ψ hψA‖ ^ 2 * ‖centered B ψ hψB‖ ^ 2 =
        (‖centered A ψ hψA‖ * ‖centered B ψ hψB‖) ^ 2 := by
    ring
  rw [h_mul_sq]
  calc
    (stateCovariance A B ψ hψA hψB) ^ 2 + (c / 2) ^ 2 =
        ‖⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ‖ ^ 2 := by
          rw [inner_norm_sq_eq_re_sq_add_commutator_half_sq h_centered]
          rfl
    _ ≤ (‖centered A ψ hψA‖ * ‖centered B ψ hψB‖) ^ 2 := by
        have h_bound :=
          norm_inner_le_norm (𝕜 := ℂ) (centered A ψ hψA) (centered B ψ hψB)
        have h_inner_nonneg : 0 ≤ ‖⟪centered A ψ hψA, centered B ψ hψB⟫_ℂ‖ :=
          norm_nonneg _
        have h_mul_nonneg : 0 ≤ ‖centered A ψ hψA‖ * ‖centered B ψ hψB‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        nlinarith

/-- A centered commutator identity implies the standard uncertainty bound. -/
lemma state_uncertainty_of_centered_commutator :
    stateStdDev A ψ hψA * stateStdDev B ψ hψB ≥ |c| / 2 := by
  refine sqrt_mul_ge_of_sq_ge (stateVariance_nonneg A ψ hψA) (by positivity) ?_
  simpa [stateStdDev] using
    state_uncertainty_squared_of_centered_commutator A B ψ hψA hψB h_centered

end CenteredBounds

section RawBounds

variable (A B : H →ₗ.[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
variable (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain)
variable (hψ_norm : ‖ψ‖ = 1)
variable (hBA : A ⟨ψ, hψA⟩ ∈ B.domain)
variable (hAB : B ⟨ψ, hψB⟩ ∈ A.domain)
variable {c : ℝ}
variable (h_raw :
  ⟪ψ, A ⟨(B ⟨ψ, hψB⟩ : H), hAB⟩ -
      B ⟨(A ⟨ψ, hψA⟩ : H), hBA⟩⟫_ℂ = Complex.I * c)

include hA hB hψ_norm hBA hAB h_raw

/-- A raw commutator expectation implies the squared Robertson uncertainty bound. -/
lemma state_uncertainty_squared_of_raw_commutator :
    stateVariance A ψ hψA * stateVariance B ψ hψB ≥ (|c| / 2) ^ 2 :=
  state_uncertainty_squared_of_centered_commutator A B ψ hψA hψB
    (inner_centered_commutator_of_raw_commutator
      A B hA hB ψ hψA hψB hψ_norm hBA hAB h_raw)

/-- A raw commutator expectation implies the squared uncertainty bound with covariance term. -/
lemma state_uncertainty_squared_with_covariance_of_raw_commutator :
    stateVariance A ψ hψA * stateVariance B ψ hψB ≥
      (stateCovariance A B ψ hψA hψB) ^ 2 + (c / 2) ^ 2 :=
  state_uncertainty_squared_with_covariance_of_centered_commutator A B ψ hψA hψB
    (inner_centered_commutator_of_raw_commutator
      A B hA hB ψ hψA hψB hψ_norm hBA hAB h_raw)

/-- A raw commutator expectation implies the standard uncertainty bound. -/
lemma state_uncertainty_of_raw_commutator :
    stateStdDev A ψ hψA * stateStdDev B ψ hψB ≥ |c| / 2 :=
  state_uncertainty_of_centered_commutator A B ψ hψA hψB
    (inner_centered_commutator_of_raw_commutator
      A B hA hB ψ hψA hψB hψ_norm hBA hAB h_raw)

end RawBounds

end
end LinearPMap
