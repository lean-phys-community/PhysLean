/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.CauchyMomentum
/-!

# The Navier-Stokes equations

## i. Overview

The Navier-Stokes equations are a set of partial differential equations that describe
the motion of viscous fluid substances. They are fundamental in fluid dynamics and are
used to model the behavior of fluids in various contexts, including gas flow and water flow.

This file defines the Navier-Stokes equations as continuity, Cauchy momentum, and a Newtonian
stress law. The Cauchy momentum equation supplies the balance-law layer, while `IsNewtonian`
specializes the stress tensor through pressure and viscosity fields.

## ii. Key results

- `velocityGradient` : The spatial velocity-gradient matrix.
- `newtonianStressTensor` : The Newtonian stress tensor determined by pressure and viscosity.
- `IsNewtonian` : Predicate saying the Cauchy stress has Newtonian constitutive form.
- `NavierStokes` : Classical continuity, Cauchy momentum, and Newtonian stress together.
- `ConvectiveNavierStokes` : Classical continuity, convective Cauchy momentum, and Newtonian
  stress together.
- `navier_stokes_iff_convective_navier_stokes` : Equivalence of the two forms when the fields
  are differentiable.

## iii. Table of contents

- A. Newtonian stress law
- B. Navier-Stokes equations
- C. Equivalence of conservative and convective Navier-Stokes forms

## iv. References

-/

@[expose] public section

open Space

namespace FluidDynamics

/-!

## A. Newtonian stress law

-/

/-- The spatial velocity-gradient matrix, with entries `partial_j u_i`. -/
noncomputable def velocityGradient (d : ℕ) (flow : FluidFlow d) :
    Time → Space d → Matrix (Fin d) (Fin d) ℝ :=
  fun t x i j => ∂[j] (fun x' => flow.velocity t x' i) x

/-- The Newtonian stress tensor
`-p I + mu (grad u + grad u^T) + lambda (div u) I`.

The scalar fields are pressure, shear viscosity, and the coefficient of the isotropic
viscous-divergence term.
-/
noncomputable def newtonianStressTensor (d : ℕ) (flow : FluidFlow d)
    (pressure shearViscosity bulkViscosity : ScalarField d) : StressTensor d :=
  fun t x =>
    (-(pressure t x)) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      shearViscosity t x •
        (velocityGradient d flow t x + Matrix.transpose (velocityGradient d flow t x)) +
        (bulkViscosity t x * (∇ ⬝ flow.velocity t) x) •
          (1 : Matrix (Fin d) (Fin d) ℝ)

/-- A Cauchy flow is Newtonian when its stress tensor has the Newtonian constitutive form. -/
def IsNewtonian
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity bulkViscosity : ScalarField d) : Prop :=
  ∀ t x,
    flow.stress t x =
      newtonianStressTensor d flow.toFluidFlow pressure shearViscosity bulkViscosity t x

/-!

## B. Navier-Stokes equations

-/

/-- The conservative Navier-Stokes equations: continuity, Cauchy momentum, and Newtonian
stress. -/
def NavierStokes
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity bulkViscosity : ScalarField d) : Prop :=
  ClassicalContinuityEquation d flow.toFluidFlow ∧
    CauchyMomentumEquation d flow ∧
      IsNewtonian d flow pressure shearViscosity bulkViscosity

/-- The convective Navier-Stokes equations: continuity, convective Cauchy momentum, and
Newtonian stress. -/
def ConvectiveNavierStokes
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity bulkViscosity : ScalarField d) : Prop :=
  ClassicalContinuityEquation d flow.toFluidFlow ∧
    ConvectiveCauchyMomentumEquation d flow ∧
      IsNewtonian d flow pressure shearViscosity bulkViscosity

/-!

## C. Equivalence of conservative and convective Navier-Stokes forms

-/

/-- The conservative and convective Navier-Stokes forms are equivalent when the fields are
differentiable enough for the product rules. -/
theorem navier_stokes_iff_convective_navier_stokes
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity bulkViscosity : ScalarField d)
    (hRhoTime : ∀ t x, DifferentiableAt ℝ (flow.rho · x) t)
    (hVelocityTime : ∀ t x, DifferentiableAt ℝ (flow.velocity · x) t)
    (hMomentumDensity : ∀ t,
      Differentiable ℝ (momentumDensity d flow.toFluidFlow t))
    (hVelocitySpace : ∀ t, Differentiable ℝ (flow.velocity t)) :
    NavierStokes d flow pressure shearViscosity bulkViscosity ↔
      ConvectiveNavierStokes d flow pressure shearViscosity bulkViscosity := by
  constructor
  · intro hConservative
    refine ⟨hConservative.1, ?_, hConservative.2.2⟩
    exact (cauchy_momentum_iff_convective_cauchy_momentum d flow
      hConservative.1 hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mp
        hConservative.2.1
  · intro hConvective
    refine ⟨hConvective.1, ?_, hConvective.2.2⟩
    exact (cauchy_momentum_iff_convective_cauchy_momentum d flow
      hConvective.1 hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mpr
        hConvective.2.1

end FluidDynamics
