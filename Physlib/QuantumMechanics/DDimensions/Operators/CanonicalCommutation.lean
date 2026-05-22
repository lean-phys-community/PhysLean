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
same-coordinate uncertainty lower bounds for normalized states.

The operators are defined in `Position` and `Momentum`. The abstract inequalities are proved in
`Uncertainty` and applied here via `LinearPMap.state_uncertainty_*_of_raw_commutator`.

## ii. Key results

- `schwartzPositionOperator_commutator_momentumOperator` : the transported CCR on
  `SpaceDHilbertSpace d` as an equality of partial linear maps.
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

/-- The momentum operator preserves the domain of the Schwartz-domain position operator. -/
lemma momentumOperator_mem_schwartzPositionOperator_domain
    (i j : Fin d) (ψ : (momentumOperator j).domain) :
    (momentumOperator j ψ : SpaceDHilbertSpace d) ∈ (schwartzPositionOperator i).domain := by
  rw [schwartzPositionOperator_domain]
  exact momentumOperator_range j ψ

/-- The Schwartz-domain position operator preserves the domain of the momentum operator. -/
lemma schwartzPositionOperator_mem_momentumOperator_domain
    (i j : Fin d) (ψ : (schwartzPositionOperator i).domain) :
    (schwartzPositionOperator i ψ : SpaceDHilbertSpace d) ∈ (momentumOperator j).domain := by
  change (schwartzPositionOperator i ψ : SpaceDHilbertSpace d) ∈ schwartzSubmodule d
  have hψ : (ψ : SpaceDHilbertSpace d) ∈ schwartzSubmodule d := by
    rw [← schwartzPositionOperator_domain]
    exact ψ.2
  exact schwartzPositionOperator_range i ⟨ψ, hψ⟩

/-- Pointwise form of the canonical commutation relation on the Schwartz domain. -/
lemma schwartzPositionOperator_commutator_momentumOperator_apply (i j : Fin d)
    (ψ : schwartzSubmodule d) :
    schwartzPositionOperator i (⟨(momentumOperator j ψ : SpaceDHilbertSpace d),
          momentumOperator_range j ψ⟩ : schwartzSubmodule d) -
      momentumOperator j
        ⟨(schwartzPositionOperator i ψ : SpaceDHilbertSpace d),
          schwartzPositionOperator_range i ψ⟩ =
      (I * ℏ) • δ[i,j] • (ψ : SpaceDHilbertSpace d) := by
  have hψ := congrArg
    (fun F : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) => F (schwartzEquiv.symm ψ))
    (position_commutation_momentum i j)
  simpa [schwartzPositionOperator_apply, momentumOperator_apply, schwartzEquiv.apply_symm_apply,
    Bracket.bracket, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Submodule.coe_smul, Submodule.coe_sub] using
    congrArg Subtype.val (congrArg schwartzEquiv hψ)

/-- The canonical commutation relation for `schwartzPositionOperator` and `momentumOperator` as an
equality of partial linear maps on the Schwartz domain. -/
lemma schwartzPositionOperator_commutator_momentumOperator (i j : Fin d) :
    (schwartzPositionOperator i).comp (momentumOperator j)
        (momentumOperator_mem_schwartzPositionOperator_domain i j) -
      (momentumOperator j).comp (schwartzPositionOperator i)
        (schwartzPositionOperator_mem_momentumOperator_domain i j) =
      (I * ℏ * (δ[i,j] : ℂ)) •
        (LinearMap.id.toPMap (schwartzSubmodule d) :
          SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d) := by
  apply LinearPMap.ext
  · rw [LinearPMap.sub_domain, LinearPMap.smul_domain]
    simp [momentumOperator, schwartzPositionOperator_domain]
  · intro x hx hy
    rw [LinearPMap.sub_domain] at hx
    have hxS : x ∈ schwartzSubmodule d := by
      simpa [momentumOperator] using hx.1
    let ψ : schwartzSubmodule d := ⟨x, hxS⟩
    have hpoint := schwartzPositionOperator_commutator_momentumOperator_apply i j ψ
    simp [ψ, LinearPMap.sub_apply] at hpoint ⊢
    rw [← Nat.cast_smul_eq_nsmul ℂ δ[i,j] (x : SpaceDHilbertSpace d), smul_smul] at hpoint
    simpa [mul_assoc] using hpoint

/-- Expectation-level form of the same-coordinate canonical commutation relation. -/
lemma inner_schwartzPositionOperator_commutator_momentumOperator_same
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    ⟪(ψ : SpaceDHilbertSpace d), (schwartzPositionOperator i
        (⟨(momentumOperator i ψ : SpaceDHilbertSpace d),
          momentumOperator_range i ψ⟩ : schwartzSubmodule d) -
      momentumOperator i
        ⟨(schwartzPositionOperator i ψ : SpaceDHilbertSpace d),
          schwartzPositionOperator_range i ψ⟩)⟫_ℂ =
      I * ℏ := by
  rw [schwartzPositionOperator_commutator_momentumOperator_apply i i ψ]
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
    (ℏ / 2) ^ 2 ≤ variance (schwartzPositionOperator i) ψ *
      variance (momentumOperator i) ⟨ψ, ψ.2⟩ := by
  have hbound :=
    state_uncertainty_squared_of_raw_commutator (schwartzPositionOperator i) (momentumOperator i)
      (schwartzPositionOperator_isSymmetric i) (momentumOperator_isSymmetric i) ψ ψ.2 hψ_norm
      (schwartzPositionOperator_range i ψ)
      (momentumOperator_mem_schwartzPositionOperator_domain i i ψ) (c := ℏ)
      (inner_schwartzPositionOperator_commutator_momentumOperator_same i ψ hψ_norm)
  simpa only [abs_of_nonneg ℏ_nonneg] using hbound

/-- The same-coordinate Robertson–Schrödinger lower bound on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty_squared_with_covariance
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    (stateCovariance (schwartzPositionOperator i) (momentumOperator i) ψ ψ.2) ^ 2 +
        (ℏ / 2) ^ 2 ≤
      variance (schwartzPositionOperator i) ψ *
        variance (momentumOperator i) ⟨ψ, ψ.2⟩ := by
  exact state_uncertainty_squared_with_covariance_of_raw_commutator (schwartzPositionOperator i)
    (momentumOperator i) (schwartzPositionOperator_isSymmetric i)
    (momentumOperator_isSymmetric i) ψ ψ.2 hψ_norm (schwartzPositionOperator_range i ψ)
    (momentumOperator_mem_schwartzPositionOperator_domain i i ψ) (c := ℏ)
    (inner_schwartzPositionOperator_commutator_momentumOperator_same i ψ hψ_norm)

/-- The same-coordinate position and momentum standard deviations satisfy the Heisenberg lower
bound on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    ℏ / 2 ≤ standardDeviation (schwartzPositionOperator i) ψ *
      standardDeviation (momentumOperator i) ⟨ψ, ψ.2⟩ := by
  have hbound :=
    state_uncertainty_of_raw_commutator (schwartzPositionOperator i) (momentumOperator i)
      (schwartzPositionOperator_isSymmetric i) (momentumOperator_isSymmetric i) ψ ψ.2 hψ_norm
      (schwartzPositionOperator_range i ψ)
      (momentumOperator_mem_schwartzPositionOperator_domain i i ψ) (c := ℏ)
      (inner_schwartzPositionOperator_commutator_momentumOperator_same i ψ hψ_norm)
  simpa only [abs_of_nonneg ℏ_nonneg] using hbound

end
end QuantumMechanics
