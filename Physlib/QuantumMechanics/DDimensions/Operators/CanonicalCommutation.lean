/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Austin Letson
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Commutation
public import Physlib.QuantumMechanics.DDimensions.Operators.Momentum
public import Physlib.QuantumMechanics.DDimensions.Operators.Position
public import Physlib.QuantumMechanics.DDimensions.Operators.Uncertainty
/-!

# Canonical commutation on the Schwartz submodule

## i. Overview

In this module we transport the Schwartz canonical commutation relation to
`schwartzPositionOperator` and `momentumOperator` (`𝓟`) on `schwartzSubmodule d`, and derive the
same-coordinate Heisenberg uncertainty lower bounds for normalized states.

The operators are defined in `Position` and `Momentum`. The abstract inequalities are proved in
`Uncertainty` and applied here via `LinearPMap.state_uncertainty_*_of_raw_commutator`.

## ii. Key results

- `schwartzCoord_position_momentum_commutator` : the CCR for `schwartzEquiv.symm ψ` in
  `𝓢(Space d, ℂ)`.
- `schwartzPositionOperator_commutator_momentumOperator` : the transported CCR on
  `SpaceDHilbertSpace d`.
- `inner_schwartzPositionOperator_commutator_momentumOperator_same` : the same-coordinate
  commutator expectation for `‖ψ‖ = 1`.
- `position_momentum_same_coordinate_uncertainty_squared` : the squared Robertson bound.
- `position_momentum_same_coordinate_uncertainty_squared_with_covariance` : the
  Robertson–Schrödinger bound.
- `position_momentum_same_coordinate_uncertainty` : the standard-deviation form.

## iii. Table of contents

- A. Schwartz canonical commutation
- B. Same-coordinate uncertainty bounds

## iv. References

- [B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 12][hall2013quantum].

-/

@[expose] public section

namespace QuantumMechanics

open Bracket Complex Constants
open KroneckerDelta
open SpaceDHilbertSpace
open SchwartzSubmodule
open SchwartzMap
open InnerProductSpace
open LinearPMap
open ContinuousLinearMap

noncomputable section

variable {d : ℕ}

/-!

## A. Schwartz canonical commutation

-/

/-- Schwartz maps satisfy the coordinate canonical commutation relation. -/
lemma schwartzCoord_position_momentum_commutator (i j : Fin d) (ψ : schwartzSubmodule d) :
    𝐱 i (𝐩 j (schwartzEquiv.symm ψ)) - 𝐩 j (𝐱 i (schwartzEquiv.symm ψ)) =
      (I * ℏ) • δ[i,j] • schwartzEquiv.symm ψ := by
  suffices (⁅𝐱 i, 𝐩 j⁆) (schwartzEquiv.symm ψ) = (I * ℏ) • δ[i,j] • schwartzEquiv.symm ψ by
    simpa [Bracket.bracket]
  simpa using congrArg (fun F : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) => F (schwartzEquiv.symm ψ))
    (position_commutation_momentum i j)

/-- The canonical commutation relation for `schwartzPositionOperator` and `momentumOperator` on the
Schwartz domain. -/
lemma schwartzPositionOperator_commutator_momentumOperator (i j : Fin d)
    (ψ : schwartzSubmodule d) :
    schwartzPositionOperator i
        ⟨(momentumOperator j ψ : SpaceDHilbertSpace d), momentumOperator_range j ψ⟩ -
      momentumOperator j
        ⟨(schwartzPositionOperator i ψ : SpaceDHilbertSpace d),
          schwartzPositionOperator_range i ψ⟩ =
      (I * ℏ) • δ[i,j] • (ψ : SpaceDHilbertSpace d) := by
  simpa [schwartzPositionOperator_apply, momentumOperator_apply, schwartzEquiv.apply_symm_apply,
    Submodule.coe_smul, Submodule.coe_sub] using
    congrArg Subtype.val (congrArg schwartzEquiv (schwartzCoord_position_momentum_commutator i j ψ))

/-- Expectation-level form of the same-coordinate canonical commutation relation. -/
lemma inner_schwartzPositionOperator_commutator_momentumOperator_same
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    ⟪(ψ : SpaceDHilbertSpace d),
      (schwartzPositionOperator i
        ⟨(momentumOperator i ψ : SpaceDHilbertSpace d), momentumOperator_range i ψ⟩ -
      momentumOperator i
        ⟨(schwartzPositionOperator i ψ : SpaceDHilbertSpace d),
          schwartzPositionOperator_range i ψ⟩)⟫_ℂ =
      I * ℏ := by
  rw [schwartzPositionOperator_commutator_momentumOperator i i ψ]
  simp only [KroneckerDelta.eq_one_of_same, one_smul]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hψ_norm, sq]
  simp

/-!

## B. Same-coordinate uncertainty bounds

-/

/-- The same-coordinate position and momentum variances satisfy the squared Heisenberg lower bound
on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty_squared
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    variance (schwartzPositionOperator i) ψ *
      variance (momentumOperator i) ⟨ψ, ψ.2⟩ ≥ (ℏ / 2) ^ 2 := by
  suffices (ℏ / 2) ^ 2 ≤ variance (schwartzPositionOperator i) ψ *
      variance (momentumOperator i) ⟨ψ, ψ.2⟩ by exact this
  have hbound :=
    state_uncertainty_squared_of_raw_commutator (schwartzPositionOperator i) (momentumOperator i)
      (schwartzPositionOperator_isSymmetric i) (momentumOperator_isSymmetric i) ψ ψ.2 hψ_norm
      (schwartzPositionOperator_range i ψ) (momentumOperator_range i ψ) (c := ℏ)
      (inner_schwartzPositionOperator_commutator_momentumOperator_same i ψ hψ_norm)
  simpa only [abs_of_nonneg ℏ_nonneg] using hbound

/-- The same-coordinate Robertson–Schrödinger lower bound on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty_squared_with_covariance
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    variance (schwartzPositionOperator i) ψ *
      variance (momentumOperator i) ⟨ψ, ψ.2⟩ ≥
        (stateCovariance (schwartzPositionOperator i) (momentumOperator i) ψ ψ.2) ^ 2 +
          (ℏ / 2) ^ 2 := by
  suffices (stateCovariance (schwartzPositionOperator i) (momentumOperator i) ψ ψ.2) ^ 2 +
      (ℏ / 2) ^ 2 ≤ variance (schwartzPositionOperator i) ψ *
        variance (momentumOperator i) ⟨ψ, ψ.2⟩ by exact this
  exact state_uncertainty_squared_with_covariance_of_raw_commutator (schwartzPositionOperator i)
    (momentumOperator i) (schwartzPositionOperator_isSymmetric i)
    (momentumOperator_isSymmetric i) ψ ψ.2 hψ_norm (schwartzPositionOperator_range i ψ)
    (momentumOperator_range i ψ) (c := ℏ)
    (inner_schwartzPositionOperator_commutator_momentumOperator_same i ψ hψ_norm)

/-- The same-coordinate position and momentum standard deviations satisfy the Heisenberg lower
bound on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    standardDeviation (schwartzPositionOperator i) ψ *
      standardDeviation (momentumOperator i) ⟨ψ, ψ.2⟩ ≥ ℏ / 2 := by
  suffices ℏ / 2 ≤ standardDeviation (schwartzPositionOperator i) ψ *
      standardDeviation (momentumOperator i) ⟨ψ, ψ.2⟩ by exact this
  have hbound :=
    state_uncertainty_of_raw_commutator (schwartzPositionOperator i) (momentumOperator i)
      (schwartzPositionOperator_isSymmetric i) (momentumOperator_isSymmetric i) ψ ψ.2 hψ_norm
      (schwartzPositionOperator_range i ψ) (momentumOperator_range i ψ) (c := ℏ)
      (inner_schwartzPositionOperator_commutator_momentumOperator_same i ψ hψ_norm)
  simpa only [abs_of_nonneg ℏ_nonneg] using hbound

end
end QuantumMechanics
