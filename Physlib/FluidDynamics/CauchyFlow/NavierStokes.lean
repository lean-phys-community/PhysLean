/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Momentum
public import Physlib.FluidDynamics.CauchyFlow.Newtonian
/-!

# The Navier-Stokes equations

## i. Overview

The Navier-Stokes equations are a set of partial differential equations that describe
the motion of viscous fluid substances. They are fundamental in fluid dynamics and are
used to model the behavior of fluids in various contexts, including gas flow and water flow.

This file defines the Navier-Stokes equations as continuity, Cauchy momentum, and a Newtonian
stress law. The Cauchy momentum equation supplies the balance-law layer, while
`CauchyFlow.IsNewtonian` specializes the stress tensor through pressure and viscosity fields.

## ii. Key results

- `NavierStokes` : Classical continuity, Cauchy momentum, and Newtonian stress together.
- `ConvectiveNavierStokes` : Classical continuity, convective Cauchy momentum, and Newtonian
  stress together.
- `navier_stokes_iff_convective_navier_stokes` : Equivalence of the two forms when the fields
  are differentiable.

## iii. Table of contents

- A. Navier-Stokes equations
- B. Equivalence of conservative and convective Navier-Stokes forms

## iv. References

-/

@[expose] public section

namespace FluidDynamics

/-!

## A. Navier-Stokes equations

-/

/-- The conservative Navier-Stokes equations: continuity, Cauchy momentum, and Newtonian
stress. -/
def NavierStokes
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity secondViscosity : ScalarField d) : Prop :=
  FluidFlow.ClassicalContinuityEquation d flow.toFluidFlow ∧
    CauchyFlow.CauchyMomentumEquation d flow ∧
      CauchyFlow.IsNewtonian d flow pressure shearViscosity secondViscosity

/-- The convective Navier-Stokes equations: continuity, convective Cauchy momentum, and
Newtonian stress. -/
def ConvectiveNavierStokes
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity secondViscosity : ScalarField d) : Prop :=
  FluidFlow.ClassicalContinuityEquation d flow.toFluidFlow ∧
    CauchyFlow.ConvectiveCauchyMomentumEquation d flow ∧
      CauchyFlow.IsNewtonian d flow pressure shearViscosity secondViscosity

/-!

## B. Equivalence of conservative and convective Navier-Stokes forms

-/

/-- The conservative and convective Navier-Stokes forms are equivalent when the fields are
differentiable enough for the product rules. -/
theorem navier_stokes_iff_convective_navier_stokes
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity secondViscosity : ScalarField d)
    (hRhoTime : ∀ t x, DifferentiableAt ℝ (flow.rho · x) t)
    (hVelocityTime : ∀ t x, DifferentiableAt ℝ (flow.velocity · x) t)
    (hMomentumDensity : ∀ t,
      Differentiable ℝ (FluidFlow.momentumDensity d flow.toFluidFlow t))
    (hVelocitySpace : ∀ t, Differentiable ℝ (flow.velocity t)) :
    NavierStokes d flow pressure shearViscosity secondViscosity ↔
      ConvectiveNavierStokes d flow pressure shearViscosity secondViscosity := by
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
