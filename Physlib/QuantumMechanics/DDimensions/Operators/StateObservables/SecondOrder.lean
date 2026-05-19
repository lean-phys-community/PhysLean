/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Krystian Nowakowski
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.ExpectedValue
public import Physlib.QuantumMechanics.DDimensions.Operators.StateObservables.StateVariance
/-!
# Second-order formulas for variance

The primary definition of `LinearPMap.variance` is `‖Tψ - ⟨T⟩_ψ ψ‖ ^ 2` in `StateVariance`.
When `T` is symmetric, `‖ψ‖ = 1`, and `Tψ ∈ T.domain`, it agrees with the familiar expression
`⟨T^2⟩_ψ - ⟨T⟩_ψ ^ 2`.

## Main statements

- `LinearPMap.variance_eq_re_inner_sub_expectedValue_sq`: the second-order formula for variance.

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
