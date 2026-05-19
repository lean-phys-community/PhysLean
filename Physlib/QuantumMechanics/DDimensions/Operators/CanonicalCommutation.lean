/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Austin Letson
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Commutation
public import Physlib.QuantumMechanics.DDimensions.Operators.Uncertainty
/-!
# Canonical commutation on the Schwartz submodule

This file transports the position and momentum operators on Schwartz maps to partial linear maps on
`SpaceDHilbertSpace d`, with common domain `schwartzSubmodule d`. It then records the
same-coordinate canonical commutation relation and the corresponding uncertainty lower bound.

This file supplies the concrete position/momentum data needed to apply the abstract uncertainty
inequality, which is proved in `LinearPMap` form in
`Physlib.QuantumMechanics.DDimensions.Operators.Uncertainty`.

## Main declarations

- `QuantumMechanics.positionPMapSchwartz`: position as a partial linear map with Schwartz domain.
- `QuantumMechanics.momentumPMapSchwartz`: momentum as a partial linear map with Schwartz domain.
- `QuantumMechanics.schwartzCoord_position_momentum_commutator`: the CCR on pullback
  `schwartzEquiv.symm ψ` in `𝓢(Space d, ℂ)`.
- `QuantumMechanics.positionPMapSchwartz_commutator_momentumPMapSchwartz`: the transported
  canonical commutation relation for the partial maps.
- `QuantumMechanics.position_momentum_same_coordinate_uncertainty_squared`: the squared
  same-coordinate lower bound.
- `QuantumMechanics.position_momentum_same_coordinate_uncertainty`: the same-coordinate
  uncertainty lower bound on normalized Schwartz-domain states.

## References

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

/-- Position as a partial linear map on `SpaceDHilbertSpace d`, with Schwartz domain. -/
def positionPMapSchwartz (i : Fin d) : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d where
  domain := schwartzSubmodule d
  toFun := schwartzIncl.toLinearMap ∘ₗ (𝐱 i).toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

/-- Momentum as a partial linear map on `SpaceDHilbertSpace d`, with Schwartz domain. -/
abbrev momentumPMapSchwartz (i : Fin d) : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  momentumOperator (d := d) (i := i)

@[simp]
lemma positionPMapSchwartz_domain (i : Fin d) :
    (positionPMapSchwartz i).domain = schwartzSubmodule d :=
  rfl

@[simp]
lemma momentumPMapSchwartz_domain (i : Fin d) :
    (momentumPMapSchwartz i).domain = schwartzSubmodule d :=
  rfl

@[simp]
lemma positionPMapSchwartz_apply (i : Fin d) (ψ : schwartzSubmodule d) :
    positionPMapSchwartz i ψ = schwartzEquiv (𝐱 i (schwartzEquiv.symm ψ)) :=
  rfl

lemma momentumPMapSchwartz_apply (i : Fin d) (ψ : schwartzSubmodule d) :
    momentumPMapSchwartz i ψ = schwartzEquiv (𝐩 i (schwartzEquiv.symm ψ)) :=
  momentumOperator_apply i ψ

lemma positionPMapSchwartz_range (i : Fin d) (ψ : schwartzSubmodule d) :
    positionPMapSchwartz i ψ ∈ schwartzSubmodule d := by
  simp [positionPMapSchwartz_apply]

/-- The position partial map is symmetric on the Schwartz domain. -/
lemma positionPMapSchwartz_isSymmetric (i : Fin d) :
    (positionPMapSchwartz i).IsSymmetric := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨g, rfl⟩ := schwartzEquiv.surjective φ
  simp only [positionPMapSchwartz_apply, ← Submodule.coe_inner, schwartzEquiv_inner,
    schwartzEquiv.symm_apply_apply, positionCLM_apply]
  open MeasureTheory in
  refine integral_congr_ae ?_
  filter_upwards with x
  have hi : starRingEnd ℂ ((↑(x i) : ℂ) * f x) = (↑(x i) : ℂ) * starRingEnd ℂ (f x) := by
    rw [map_mul, Complex.conj_ofReal]
  rw [hi]
  ring

/-- The momentum partial map is symmetric on the Schwartz domain. -/
lemma momentumPMapSchwartz_isSymmetric (i : Fin d) :
    (momentumPMapSchwartz i).IsSymmetric :=
  momentumOperator_isSymmetric i

/-- The Schwartz position partial map is densely defined and closable. -/
lemma positionPMapSchwartz_isUnbounded (i : Fin d) :
    (positionPMapSchwartz i).IsUnbounded := by
  refine (LinearPMap.IsSymmetric.isUnbounded_iff_hasDenseDomain
    (positionPMapSchwartz_isSymmetric i)).mpr ?_
  exact SchwartzSubmodule.dense d

/-- The Schwartz momentum partial map is densely defined and closable. -/
lemma momentumPMapSchwartz_isUnbounded (i : Fin d) :
    (momentumPMapSchwartz i).IsUnbounded :=
  momentumOperator_isUnbounded i

/-- Schwartz maps satisfy the coordinate canonical commutation relation. -/
lemma schwartzCoord_position_momentum_commutator (i j : Fin d) (ψ : schwartzSubmodule d) :
    𝐱 i (𝐩 j (schwartzEquiv.symm ψ)) - 𝐩 j (𝐱 i (schwartzEquiv.symm ψ)) =
      (I * ℏ) • δ[i,j] • schwartzEquiv.symm ψ := by
  simpa [Bracket.bracket, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] using
    congrArg (fun F : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) => F (schwartzEquiv.symm ψ))
      (position_commutation_momentum i j)

/-- The canonical commutation relation for the position and momentum partial maps on the Schwartz
domain. -/
lemma positionPMapSchwartz_commutator_momentumPMapSchwartz (i j : Fin d) (ψ : schwartzSubmodule d) :
    positionPMapSchwartz i
        ⟨(momentumPMapSchwartz j ψ : SpaceDHilbertSpace d),
          momentumOperator_range j ψ⟩ -
      momentumPMapSchwartz j
        ⟨(positionPMapSchwartz i ψ : SpaceDHilbertSpace d),
          positionPMapSchwartz_range i ψ⟩ =
      (I * ℏ) • δ[i,j] • (ψ : SpaceDHilbertSpace d) := by
  simpa [positionPMapSchwartz_apply, momentumPMapSchwartz_apply, schwartzEquiv.apply_symm_apply,
    Submodule.coe_smul, Submodule.coe_sub] using
    congrArg ((↑) : schwartzSubmodule d → SpaceDHilbertSpace d)
      (congrArg schwartzEquiv (schwartzCoord_position_momentum_commutator i j ψ))

/-- Expectation-level form of the same-coordinate canonical commutation relation. -/
lemma inner_positionPMapSchwartz_commutator_momentumPMapSchwartz_same
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    ⟪(ψ : SpaceDHilbertSpace d),
      (positionPMapSchwartz i
        ⟨(momentumPMapSchwartz i ψ : SpaceDHilbertSpace d),
          momentumOperator_range i ψ⟩ -
      momentumPMapSchwartz i
        ⟨(positionPMapSchwartz i ψ : SpaceDHilbertSpace d),
          positionPMapSchwartz_range i ψ⟩)⟫_ℂ =
      I * ℏ := by
  rw [positionPMapSchwartz_commutator_momentumPMapSchwartz i i ψ]
  simp only [KroneckerDelta.eq_one_of_same, one_smul]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hψ_norm, sq]
  simp

/-- The same-coordinate position and momentum variances satisfy the squared Heisenberg lower bound
on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty_squared
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    LinearPMap.variance (positionPMapSchwartz i) ψ *
      LinearPMap.variance (momentumPMapSchwartz i) ⟨ψ, ψ.2⟩ ≥
        (ℏ / 2) ^ 2 := by
  let A := positionPMapSchwartz i
  let B := momentumPMapSchwartz i
  have hψB : (ψ : SpaceDHilbertSpace d) ∈ B.domain := ψ.2
  have hraw := inner_positionPMapSchwartz_commutator_momentumPMapSchwartz_same i ψ hψ_norm
  simpa only [abs_of_nonneg ℏ_nonneg] using
    state_uncertainty_squared_of_raw_commutator A B (positionPMapSchwartz_isSymmetric i)
      (momentumPMapSchwartz_isSymmetric i) ψ hψB hψ_norm
      (positionPMapSchwartz_range i ψ) (momentumOperator_range i ψ)
      (c := ℏ) hraw

/-- The same-coordinate Robertson-Schrodinger lower bound on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty_squared_with_covariance
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    LinearPMap.variance (positionPMapSchwartz i) ψ *
      LinearPMap.variance (momentumPMapSchwartz i) ⟨ψ, ψ.2⟩ ≥
        (LinearPMap.stateCovariance (positionPMapSchwartz i) (momentumPMapSchwartz i) ψ
          (by exact ψ.2)) ^ 2 + (ℏ / 2) ^ 2 := by
  let A := positionPMapSchwartz i
  let B := momentumPMapSchwartz i
  have hψB : (ψ : SpaceDHilbertSpace d) ∈ B.domain := ψ.2
  have hraw := inner_positionPMapSchwartz_commutator_momentumPMapSchwartz_same i ψ hψ_norm
  simpa only using
    state_uncertainty_squared_with_covariance_of_raw_commutator A B
      (positionPMapSchwartz_isSymmetric i) (momentumPMapSchwartz_isSymmetric i)
      ψ hψB hψ_norm (positionPMapSchwartz_range i ψ) (momentumOperator_range i ψ)
      (c := ℏ) hraw

/-- The same-coordinate position and momentum standard deviations satisfy the Heisenberg lower
bound on normalized Schwartz-domain states. -/
lemma position_momentum_same_coordinate_uncertainty
    (i : Fin d) (ψ : schwartzSubmodule d) (hψ_norm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    LinearPMap.standardDeviation (positionPMapSchwartz i) ψ *
      LinearPMap.standardDeviation (momentumPMapSchwartz i) ⟨ψ, ψ.2⟩ ≥
        ℏ / 2 := by
  let A := positionPMapSchwartz i
  let B := momentumPMapSchwartz i
  have hψB : (ψ : SpaceDHilbertSpace d) ∈ B.domain := ψ.2
  have hraw := inner_positionPMapSchwartz_commutator_momentumPMapSchwartz_same i ψ hψ_norm
  simpa only [abs_of_nonneg ℏ_nonneg] using
    state_uncertainty_of_raw_commutator A B (positionPMapSchwartz_isSymmetric i)
      (momentumPMapSchwartz_isSymmetric i) ψ hψB hψ_norm
      (positionPMapSchwartz_range i ψ) (momentumOperator_range i ψ)
      (c := ℏ) hraw

end
end QuantumMechanics
