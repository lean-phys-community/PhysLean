/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.MatrixDiv
/-!

# Inviscid stress laws for Cauchy flows

## i. Overview

This module defines the inviscid stress law for `CauchyFlow` and the corresponding
matrix-divergence identity for pressure stress.

## ii. Key results

- `CauchyFlow.IsInviscid` : Predicate saying the Cauchy stress is the inviscid pressure stress.
- `CauchyFlow.matrixDiv_stress_eq_neg_grad_pressure_of_is_inviscid` : The inviscid stress
  contributes the usual pressure-gradient force term.

## iii. Table of contents

- A. Inviscid stress law

## iv. References

-/

@[expose] public section

open Space

namespace FluidDynamics

namespace CauchyFlow

/-!

## A. Inviscid stress law

-/

/-- A Cauchy flow is inviscid with pressure `p` when its stress is the isotropic pressure stress
`-p I`.

In this formulation, inviscid means that the Cauchy stress has no viscous or shear contribution.
It does not rule out body forces; those are carried separately by `CauchyFlow.specificBodyForce`.
-/
def IsInviscid (d : ℕ) (flow : CauchyFlow d) (pressure : ScalarField d) : Prop :=
  ∀ t x, flow.stress t x = (-(pressure t x)) • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The matrix divergence of the inviscid pressure stress `-p I` is `-grad p`. -/
lemma matrixDiv_inviscid_pressure_stress (d : ℕ) (pressureAtTime : Space d → ℝ) :
    matrixDiv d (fun x => (-(pressureAtTime x)) • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      -∇ pressureAtTime := by
  ext x i
  rw [matrixDiv_apply]
  rw [Finset.sum_eq_single i]
  · simp [grad, Space.deriv_eq]
  · intro j _ hji
    have hij : i ≠ j := fun h => hji h.symm
    simp [hij]
  · intro hi
    simp at hi

/-- In an inviscid Cauchy flow, the stress-divergence force is the usual
negative pressure-gradient term. -/
theorem matrixDiv_stress_eq_neg_grad_pressure_of_is_inviscid
    (d : ℕ) (flow : CauchyFlow d) (pressure : ScalarField d)
    (hInviscid : IsInviscid d flow pressure) :
    ∀ t, matrixDiv d (flow.stress t) = -∇ (pressure t) := by
  intro t
  rw [show flow.stress t =
      fun x => (-(pressure t x)) • (1 : Matrix (Fin d) (Fin d) ℝ) by
    funext x
    exact hInviscid t x]
  exact matrixDiv_inviscid_pressure_stress d (pressure t)

end CauchyFlow

end FluidDynamics
