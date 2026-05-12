/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Commutation
public import Physlib.QuantumMechanics.DDimensions.Operators.Uncertainty
/-!
# Canonical commutation on the Schwartz submodule

This file transports the position and momentum operators on Schwartz maps to partial linear maps on
`SpaceDHilbertSpace d`, with common domain `schwartzSubmodule d`. It then records the
same-coordinate canonical commutation relation and the corresponding uncertainty lower bound.

This file supplies the concrete position/momentum data needed to apply the abstract uncertainty inequality,
which is proved in `LinearPMap` form in `Physlib.QuantumMechanics.DDimensions.Operators.Uncertainty`

## Main declarations

- `QuantumMechanics.positionPMapSchwartz`: position as a partial linear map with Schwartz domain.
- `QuantumMechanics.momentumPMapSchwartz`: momentum as a partial linear map with Schwartz domain.
- `QuantumMechanics.positionPMapSchwartz_commutator_momentumPMapSchwartz`: the transported
  canonical commutation relation.
- `QuantumMechanics.position_momentum_same_coordinate_uncertainty_squared`: the squared
  same-coordinate lower bound.
- `QuantumMechanics.position_momentum_same_coordinate_uncertainty`: the same-coordinate
  uncertainty lower bound on normalized Schwartz-domain states.

## References

- [B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 12][hall2013quantum].
-/

@[expose] public section

namespace QuantumMechanics

open Complex Constants
open KroneckerDelta
open SpaceDHilbertSpace
open SchwartzSubmodule
open SchwartzMap
open InnerProductSpace
open LinearPMap

noncomputable section

variable {d : ℕ} (i j : Fin d)

/-- Position as a partial linear map on `SpaceDHilbertSpace d`, with Schwartz domain. -/
def positionPMapSchwartz : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  LinearPMap.mk (schwartzSubmodule d)
    ((schwartzSubmodule d).subtype ∘ₗ positionOperatorSchwartz i)

/-- Momentum as a partial linear map on `SpaceDHilbertSpace d`, with Schwartz domain. -/
def momentumPMapSchwartz : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  LinearPMap.mk (schwartzSubmodule d)
    ((schwartzSubmodule d).subtype ∘ₗ momentumOperatorSchwartz i)

@[simp]
lemma positionPMapSchwartz_domain :
    (positionPMapSchwartz (d := d) i).domain = schwartzSubmodule d :=
  rfl

@[simp]
lemma momentumPMapSchwartz_domain :
    (momentumPMapSchwartz (d := d) i).domain = schwartzSubmodule d :=
  rfl

@[simp]
lemma positionPMapSchwartz_apply (ψ : schwartzSubmodule d) :
    positionPMapSchwartz i ψ = (positionOperatorSchwartz i ψ : SpaceDHilbertSpace d) :=
  rfl

@[simp]
lemma momentumPMapSchwartz_apply (ψ : schwartzSubmodule d) :
    momentumPMapSchwartz i ψ = (momentumOperatorSchwartz i ψ : SpaceDHilbertSpace d) :=
  rfl

/-- The position partial map is symmetric on the Schwartz domain. -/
lemma positionPMapSchwartz_isSymmetric :
    (positionPMapSchwartz (d := d) i).IsSymmetric :=
  fun ψ φ ↦ positionOperatorSchwartz_isSymmetric i ψ φ

/-- The momentum partial map is symmetric on the Schwartz domain. -/
lemma momentumPMapSchwartz_isSymmetric :
    (momentumPMapSchwartz (d := d) i).IsSymmetric :=
  fun ψ φ ↦ momentumOperatorSchwartz_isSymmetric i ψ φ

/-- The Schwartz position partial map is densely defined and closable. -/
lemma positionPMapSchwartz_isUnbounded :
    (positionPMapSchwartz (d := d) i).IsUnbounded :=
  LinearPMap.isUnbounded_of_dense_of_isSymmetric'
    (SchwartzSubmodule.dense d) (positionOperatorSchwartz_isSymmetric i)

/-- The Schwartz momentum partial map is densely defined and closable. -/
lemma momentumPMapSchwartz_isUnbounded :
    (momentumPMapSchwartz (d := d) i).IsUnbounded :=
  LinearPMap.isUnbounded_of_dense_of_isSymmetric'
    (SchwartzSubmodule.dense d) (momentumOperatorSchwartz_isSymmetric i)

/-- The continuous Schwartz operators satisfy `[xᵢ, pⱼ] = iℏ δᵢⱼ`. -/
lemma positionOperatorSchwartz_commutator_momentumOperatorSchwartz
    (ψ : schwartzSubmodule d) :
    positionOperatorSchwartz i (momentumOperatorSchwartz j ψ) -
        momentumOperatorSchwartz j (positionOperatorSchwartz i ψ) =
      (I * ℏ) • δ[i,j] • ψ := by
  apply schwartzEquiv.symm.injective
  simpa [Bracket.bracket, ContinuousLinearMap.mul_def, positionOperatorSchwartz,
    momentumOperatorSchwartz, sub_eq_add_neg, smul_smul] using
    congrArg (· (schwartzEquiv.symm ψ)) (position_commutation_momentum i j)

/-- The canonical commutation relation for the position and momentum partial maps on the Schwartz
domain. -/
lemma positionPMapSchwartz_commutator_momentumPMapSchwartz
    (ψ : schwartzSubmodule d) :
    positionPMapSchwartz i
        ⟨(momentumPMapSchwartz j ψ : SpaceDHilbertSpace d),
          (momentumOperatorSchwartz j ψ).property⟩ -
      momentumPMapSchwartz j
        ⟨(positionPMapSchwartz i ψ : SpaceDHilbertSpace d),
          (positionOperatorSchwartz i ψ).property⟩ =
      (I * ℏ) • δ[i,j] • (ψ : SpaceDHilbertSpace d) := by
  simpa only using
    congrArg ((↑) : schwartzSubmodule d → SpaceDHilbertSpace d)
      (positionOperatorSchwartz_commutator_momentumOperatorSchwartz i j ψ)

/-- Expectation-level form of the same-coordinate canonical commutation relation. -/
lemma inner_positionPMapSchwartz_commutator_momentumPMapSchwartz_same
    (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    ⟪(ψ : SpaceDHilbertSpace d),
      (positionPMapSchwartz i
        ⟨(momentumPMapSchwartz i ψ : SpaceDHilbertSpace d),
          (momentumOperatorSchwartz i ψ).property⟩ -
      momentumPMapSchwartz i
        ⟨(positionPMapSchwartz i ψ : SpaceDHilbertSpace d),
          (positionOperatorSchwartz i ψ).property⟩)⟫_ℂ =
      I * ℏ := by
  rw [positionPMapSchwartz_commutator_momentumPMapSchwartz (i := i) (j := i) ψ]
  simp only [KroneckerDelta.eq_one_of_same, one_smul]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hψ_norm, sq]
  simp

/-- The same-coordinate position and momentum variances satisfy the squared Heisenberg lower bound
on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty_squared
    (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    LinearPMap.stateVariance (positionPMapSchwartz i) (ψ : SpaceDHilbertSpace d) ψ.property *
      LinearPMap.stateVariance (momentumPMapSchwartz i) (ψ : SpaceDHilbertSpace d) ψ.property ≥
        (ℏ / 2) ^ 2 := by
  let A := positionPMapSchwartz i
  let B := momentumPMapSchwartz i
  have hraw := inner_positionPMapSchwartz_commutator_momentumPMapSchwartz_same i ψ hψ_norm
  simpa only [abs_of_nonneg ℏ_nonneg] using
    state_uncertainty_squared_of_raw_commutator A B (positionPMapSchwartz_isSymmetric i)
      (momentumPMapSchwartz_isSymmetric i) (ψ : SpaceDHilbertSpace d) ψ.property ψ.property
      hψ_norm (positionOperatorSchwartz i ψ).property (momentumOperatorSchwartz i ψ).property
      (c := ℏ) hraw

/-- The same-coordinate Robertson-Schrodinger lower bound on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty_squared_with_covariance
    (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    LinearPMap.stateVariance (positionPMapSchwartz i) (ψ : SpaceDHilbertSpace d) ψ.property *
      LinearPMap.stateVariance (momentumPMapSchwartz i) (ψ : SpaceDHilbertSpace d) ψ.property ≥
        (LinearPMap.stateCovariance (positionPMapSchwartz i) (momentumPMapSchwartz i)
          (ψ : SpaceDHilbertSpace d) ψ.property ψ.property) ^ 2 + (ℏ / 2) ^ 2 := by
  let A := positionPMapSchwartz i
  let B := momentumPMapSchwartz i
  have hraw := inner_positionPMapSchwartz_commutator_momentumPMapSchwartz_same i ψ hψ_norm
  simpa only using
    state_uncertainty_squared_with_covariance_of_raw_commutator A B
      (positionPMapSchwartz_isSymmetric i) (momentumPMapSchwartz_isSymmetric i)
      (ψ : SpaceDHilbertSpace d) ψ.property ψ.property hψ_norm
      (positionOperatorSchwartz i ψ).property (momentumOperatorSchwartz i ψ).property
      (c := ℏ) hraw

/-- The same-coordinate position and momentum standard deviations satisfy the Heisenberg lower
bound on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty
    (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    LinearPMap.stateStdDev (positionPMapSchwartz i) (ψ : SpaceDHilbertSpace d) ψ.property *
      LinearPMap.stateStdDev (momentumPMapSchwartz i) (ψ : SpaceDHilbertSpace d) ψ.property ≥
        ℏ / 2 := by
  let A := positionPMapSchwartz i
  let B := momentumPMapSchwartz i
  have hraw := inner_positionPMapSchwartz_commutator_momentumPMapSchwartz_same i ψ hψ_norm
  simpa only [abs_of_nonneg ℏ_nonneg] using
    state_uncertainty_of_raw_commutator A B (positionPMapSchwartz_isSymmetric i)
      (momentumPMapSchwartz_isSymmetric i) (ψ : SpaceDHilbertSpace d) ψ.property ψ.property
      hψ_norm (positionOperatorSchwartz i ψ).property (momentumOperatorSchwartz i ψ).property
      (c := ℏ) hraw

end
end QuantumMechanics
