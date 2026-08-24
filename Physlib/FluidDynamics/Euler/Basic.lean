/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Inviscid
public import Physlib.FluidDynamics.CauchyFlow.Momentum
/-!

# Euler equation for fluid flows

## i. Overview

This module defines the Euler equations for inviscid fluid flow as continuity, Cauchy momentum,
and an inviscid stress law. The pressure field appears through the constitutive relation for
the Cauchy stress tensor rather than as a field of the flow data.

## ii. Key results

- `Euler` : Classical continuity, Cauchy momentum, and inviscid stress together.
- `ConvectiveEuler` : Classical continuity, convective Cauchy momentum, and inviscid stress.
- `euler_iff_convectiveEuler` : Equivalence of the conservative and convective forms when the
  fields are differentiable.

## iii. Table of contents

- A. Euler equations
- B. Equivalence of conservative and convective Euler forms

## iv. References

-/

@[expose] public section

namespace FluidDynamics

/-!

## A. Euler equations

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

## B. Equivalence of conservative and convective Euler forms

-/

/-- The conservative and convective Euler forms are equivalent when the fields are
differentiable enough for the product rules. -/
theorem euler_iff_convectiveEuler
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
    exact
      (CauchyFlow.cauchyMomentumEquation_iff_convectiveCauchyMomentumEquation d flow
        hConservative.1 hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mp
          hConservative.2.1
  · intro hConvective
    refine ⟨hConvective.1, ?_, hConvective.2.2⟩
    exact
      (CauchyFlow.cauchyMomentumEquation_iff_convectiveCauchyMomentumEquation d flow
        hConvective.1 hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mpr
          hConvective.2.1

end FluidDynamics
