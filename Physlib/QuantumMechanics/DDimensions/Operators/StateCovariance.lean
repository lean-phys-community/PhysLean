/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.ExpectedValue
public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.StateVariance
/-!
# State covariance

For symmetric partial linear maps `A` and `B` on a common state `ψ`, this file defines the
covariance `re ⟪(Aψ)ᶜ, (Bψ)ᶜ⟫` of the centered vectors.

## Main definitions

- `LinearPMap.stateCovariance`: the real part of the inner product of two centered vectors.

-/

@[expose] public section

namespace LinearPMap

open InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Covariance

variable (A B : H →ₗ.[ℂ] H)
variable (ψ : A.domain)
variable (hψB : (ψ : H) ∈ B.domain)

/-- State covariance, defined as the real part of the centered inner product. -/
def stateCovariance : ℝ :=
  (⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ).re

/-- State covariance, unfolded to the real part of the centered inner product. -/
lemma stateCovariance_eq_re_inner_centered :
    stateCovariance A B ψ hψB =
      (⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ).re :=
  rfl

/-- Swapping the two observables does not change the state covariance. -/
lemma stateCovariance_comm :
    stateCovariance A B ψ hψB = stateCovariance B A ⟨ψ, hψB⟩ ψ.2 := by
  rw [stateCovariance_eq_re_inner_centered, stateCovariance_eq_re_inner_centered]
  calc
    (⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ).re =
        (((starRingEnd ℂ) ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ)).re := by
      rw [inner_conj_symm]
    _ = (⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re := by
      change (star ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re =
        (⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re
      rw [Complex.star_def, Complex.conj_re]

/-- State covariance as the real part of the symmetrized centered inner product. -/
lemma stateCovariance_eq_re_symm_centered :
    stateCovariance A B ψ hψB =
      ((⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ +
        ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re) / 2 := by
  let z : ℂ := ⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ
  have hz : ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ = star z := by
    simp [z, inner_conj_symm]
  rw [stateCovariance_eq_re_inner_centered, hz]
  change z.re = ((z + star z).re) / 2
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, add_self_div_two]

@[simp]
lemma stateCovariance_self_eq_stateVariance (A : H →ₗ.[ℂ] H) (ψ : A.domain) :
    stateCovariance A A ψ (by exact ψ.2) = stateVariance A ψ := by
  rw [stateCovariance_eq_re_inner_centered, stateVariance_eq_centered_norm_sq,
    inner_self_eq_norm_sq_to_K]
  rw [sq, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]

end Covariance

end
end LinearPMap
