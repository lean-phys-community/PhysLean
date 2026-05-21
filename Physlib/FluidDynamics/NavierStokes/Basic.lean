/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.NavierStokes.Momentum
/-!

# The Navier-Stokes equations

## i. Overview

The Navier-Stokes equations are a set of partial differential equations that describe
the motion of viscous fluid substances. They are fundamental in fluid dynamics and are
used to model the behavior of fluids in various contexts, including gas flow and water flow.

This file combines the continuity equation with the conservative and convective momentum
equations. The stress tensor is left as an input field, so this is the balance-law layer
before specializing to a Newtonian stress law.

## ii. Key results

- `ConservativeForm` : Continuity and conservative momentum equations together.
- `ConvectiveForm` : Continuity and convective momentum equations together.
- `ConservativeForm_iff_ConvectiveForm` : Equivalence of the two forms when the
  fields are differentiable.

## iii. Table of contents

- A. Full Navier-Stokes forms

## iv. References

-/

@[expose] public section

namespace FluidDynamics
namespace NavierStokes

/-!

## A. Full Navier-Stokes forms

-/

/-- The conservative Navier-Stokes balance-law form with an externally supplied stress tensor. -/
def ConservativeForm (d : ℕ) (data : FluidInMomentumBalance d) : Prop :=
  ContinuityEquation d data.toFluidState ∧
    ConservativeMomentumEquation d data

/-- The convective Navier-Stokes form with an externally supplied stress tensor. -/
def ConvectiveForm (d : ℕ) (data : FluidInMomentumBalance d) : Prop :=
  ContinuityEquation d data.toFluidState ∧
    ConvectiveMomentumEquation d data

/-- The conservative and convective Navier-Stokes forms are equivalent when the fields are
differentiable enough for the product rules. -/
theorem ConservativeForm_iff_ConvectiveForm
    (d : ℕ) (data : FluidInMomentumBalance d)
    (hRhoTime : ∀ t x,
      DifferentiableAt ℝ (fun t' => data.rho t' x) t)
    (hVelocityTime : ∀ t x,
      DifferentiableAt ℝ (fun t' => data.velocity t' x) t)
    (hMomentumDensity : ∀ t,
      Differentiable ℝ (momentumDensity d data.toFluidState t))
    (hVelocitySpace : ∀ t, Differentiable ℝ (data.velocity t)) :
    ConservativeForm d data ↔
      ConvectiveForm d data := by
  constructor
  · intro hConservative
    refine ⟨hConservative.1, ?_⟩
    exact (ConservativeMomentumEquation_iff_ConvectiveMomentumEquation d data hConservative.1
      hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mp
      hConservative.2
  · intro hConvective
    refine ⟨hConvective.1, ?_⟩
    exact (ConservativeMomentumEquation_iff_ConvectiveMomentumEquation d data hConvective.1
      hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mpr
      hConvective.2

end NavierStokes
end FluidDynamics
