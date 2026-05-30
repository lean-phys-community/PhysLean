/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.CauchyMomentum
public import Physlib.SpaceAndTime.Space.Derivatives.Grad
/-!

# Euler equation for fluid flows

## i. Overview

This module defines the Euler equations for inviscid fluid flow as continuity, Cauchy momentum,
and an inviscid stress law. The pressure field appears through the constitutive relation for
the Cauchy stress tensor rather than as a field of the flow data.

## ii. Key results

- `CauchyFlow.IsInviscid` : Predicate saying the Cauchy stress is the inviscid pressure stress.
- `CauchyFlow.matrixDiv_stress_eq_neg_grad_pressure_of_is_inviscid` : The inviscid stress
  contributes the usual pressure-gradient force term.
- `Euler` : Classical continuity, Cauchy momentum, and inviscid stress together.
- `ConvectiveEuler` : Classical continuity, convective Cauchy momentum, and inviscid stress.
- `euler_iff_convective_euler` : Equivalence of the conservative and convective forms when the
  fields are differentiable.

## iii. Table of contents

- A. Inviscid stress law
- B. Euler equations
- C. Equivalence of conservative and convective Euler forms

## iv. References

-/

@[expose] public section

open Space

namespace FluidDynamics

namespace CauchyFlow

/-!

## A. Inviscid stress law

-/

/-- A Cauchy flow is inviscid with pressure `p` when its stress is `-p I`. -/
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

/-!

## B. Euler equations

-/

/-- The conservative Euler equations: continuity, Cauchy momentum, and inviscid stress. -/
def Euler (d : ℕ) (flow : CauchyFlow d) (pressure : ScalarField d) : Prop :=
  FluidFlow.ClassicalContinuityEquation d flow.toFluidFlow ∧
    CauchyFlow.CauchyMomentumEquation d flow ∧ CauchyFlow.IsInviscid d flow pressure

/-- The convective Euler equations: continuity, convective Cauchy momentum, and inviscid
stress. -/
def ConvectiveEuler (d : ℕ) (flow : CauchyFlow d) (pressure : ScalarField d) : Prop :=
  FluidFlow.ClassicalContinuityEquation d flow.toFluidFlow ∧
    CauchyFlow.ConvectiveCauchyMomentumEquation d flow ∧ CauchyFlow.IsInviscid d flow pressure

/-!

## C. Equivalence of conservative and convective Euler forms

-/

/-- The conservative and convective Euler forms are equivalent when the fields are
differentiable enough for the product rules. -/
theorem euler_iff_convective_euler
    (d : ℕ) (flow : CauchyFlow d) (pressure : ScalarField d)
    (hRhoTime : ∀ t x, DifferentiableAt ℝ (flow.rho · x) t)
    (hVelocityTime : ∀ t x, DifferentiableAt ℝ (flow.velocity · x) t)
    (hMomentumDensity : ∀ t,
      Differentiable ℝ (FluidFlow.momentumDensity d flow.toFluidFlow t))
    (hVelocitySpace : ∀ t, Differentiable ℝ (flow.velocity t)) :
    Euler d flow pressure ↔ ConvectiveEuler d flow pressure := by
  constructor
  · intro hConservative
    refine ⟨hConservative.1, ?_, hConservative.2.2⟩
    exact (CauchyFlow.cauchy_momentum_iff_convective_cauchy_momentum d flow hConservative.1
      hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mp hConservative.2.1
  · intro hConvective
    refine ⟨hConvective.1, ?_, hConvective.2.2⟩
    exact (CauchyFlow.cauchy_momentum_iff_convective_cauchy_momentum d flow hConvective.1
      hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mpr hConvective.2.1

end FluidDynamics
