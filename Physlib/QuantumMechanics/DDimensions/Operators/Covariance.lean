/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.Variance
/-!

# Covariance

## i. Overview

In this module we define the covariance of two partial linear maps `A` and `B` in a common state
`ψ` as the real part of the inner product of their centered vectors.

## ii. Key results

- `covariance` : the real part of the centered inner product.
- `covariance_comm` : covariance is symmetric in the two observables.
- `covariance_eq_re_symm_centered` : covariance as the real part of the symmetrized centered
  inner product.
- `covariance_self_eq_variance` : the covariance of an observable with itself is its variance.

## iii. Table of contents

- A. Covariance

## iv. References

- [B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 12][hall2013quantum].

-/

@[expose] public section

namespace LinearPMap

open InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-!

## A. Covariance

-/

section Covariance

variable (A B : H →ₗ.[ℂ] H)
variable (ψ : A.domain)
variable (hψB : (ψ : H) ∈ B.domain)

/-- Covariance, defined as the real part of the centered inner product. -/
def covariance : ℝ :=
  (⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ).re

/-- Covariance, unfolded to the real part of the centered inner product. -/
lemma covariance_eq_re_inner_centered :
    covariance A B ψ hψB =
      (⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ).re :=
  rfl

/-- Swapping the two observables does not change the covariance. -/
lemma covariance_comm :
    covariance A B ψ hψB = covariance B A ⟨ψ, hψB⟩ ψ.2 := by
  rw [covariance_eq_re_inner_centered, covariance_eq_re_inner_centered]
  calc
    (⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ).re =
        (((starRingEnd ℂ) ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ)).re := by
      rw [inner_conj_symm]
    _ = (⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re := by
      change (star ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re =
        (⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re
      rw [Complex.star_def, Complex.conj_re]

/-- Covariance as the real part of the symmetrized centered inner product. -/
lemma covariance_eq_re_symm_centered :
    covariance A B ψ hψB =
      ((⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ +
        ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ).re) / 2 := by
  let z : ℂ := ⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ
  have hz : ⟪centered B ⟨ψ, hψB⟩, centered A ψ⟫_ℂ = star z := by
    simp [z, inner_conj_symm]
  rw [covariance_eq_re_inner_centered, hz]
  change z.re = ((z + star z).re) / 2
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, add_self_div_two]

@[simp]
lemma covariance_self_eq_variance (A : H →ₗ.[ℂ] H) (ψ : A.domain) :
    covariance A A ψ (by exact ψ.2) = variance A ψ := by
  rw [covariance_eq_re_inner_centered, variance_eq_centered_norm_sq, inner_self_eq_norm_sq_to_K]
  rw [sq, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]

end Covariance

end
end LinearPMap
