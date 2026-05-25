/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.Momentum
public import Physlib.SpaceAndTime.Space.Derivatives.Grad
/-!

# Euler equation for fluid flows

## i. Overview

This module defines the Euler momentum equation for inviscid fluid flow. The pressure gradient
and body force terms are kept explicit, while the conservative and convective left-hand sides
reuse the corresponding Navier-Stokes balance-law definitions.

## ii. Key results

- `FluidInEulerBalance` : A fluid state with pressure and body force.
- `eulerMomentumRHS` : The pressure-gradient and body-force side of Euler momentum balance.
- `EulerMomentumEquation` : Euler momentum balance in conservative form.
- `ConvectiveEulerMomentumEquation` : Euler momentum balance in convective form.
- `Euler` : Classical continuity and conservative Euler momentum together.
- `ConvectiveEuler` : Classical continuity and convective Euler momentum together.
- `Euler_iff_ConvectiveEuler` : Equivalence of the conservative and convective forms when the
  fields are differentiable.

## iii. Table of contents

- A. Euler data
- B. Euler momentum equations
- C. Full Euler forms
- D. Equivalence of conservative and convective Euler forms

## iv. References

-/

@[expose] public section

open Space
open Time

namespace FluidDynamics

/-!

## A. Euler data

-/

/-- The fields needed for Euler momentum balance: fluid state, pressure, and body force. -/
structure FluidInEulerBalance (d : ℕ) extends FluidState d where
  /-- The pressure field. -/
  pressure : ScalarField d
  /-- The body-force field per unit mass. -/
  bodyForce : BodyForce d

/-!

## B. Euler momentum equations

-/

/-- The right-hand side of Euler momentum balance, `-grad p + rho f`. -/
noncomputable def eulerMomentumRHS (d : ℕ) (data : FluidInEulerBalance d) : VectorField d :=
  fun t x => -(∇ (data.pressure t) x) + data.rho t x • data.bodyForce t x

/-- Euler momentum balance in conservative form,
`partial_t (rho u) + matrixDiv (rho u ⊗ u) = -grad p + rho f`. -/
def EulerMomentumEquation (d : ℕ) (data : FluidInEulerBalance d) : Prop :=
  ∀ t x, conservativeMomentumLHS d data.toFluidState t x =
    eulerMomentumRHS d data t x

/-- Euler momentum balance in convective form,
`rho (partial_t u + (u · grad)u) = -grad p + rho f`. -/
def ConvectiveEulerMomentumEquation (d : ℕ) (data : FluidInEulerBalance d) : Prop :=
  ∀ t x, convectiveMomentumLHS d data.toFluidState t x =
    eulerMomentumRHS d data t x

/-!

## C. Full Euler forms

-/

/-- The conservative Euler equations: classical continuity and conservative momentum balance. -/
def Euler (d : ℕ) (data : FluidInEulerBalance d) : Prop :=
  ClassicalContinuityEquation d data.toFluidState ∧
    EulerMomentumEquation d data

/-- The convective Euler equations: classical continuity and convective momentum balance. -/
def ConvectiveEuler (d : ℕ) (data : FluidInEulerBalance d) : Prop :=
  ClassicalContinuityEquation d data.toFluidState ∧
    ConvectiveEulerMomentumEquation d data

/-!

## D. Equivalence of conservative and convective Euler forms

-/

/-- The conservative and convective Euler forms are equivalent when the fields are
differentiable enough for the product rules. -/
theorem Euler_iff_ConvectiveEuler
    (d : ℕ) (data : FluidInEulerBalance d)
    (hRhoTime : ∀ t x, DifferentiableAt ℝ (data.rho · x) t)
    (hVelocityTime : ∀ t x, DifferentiableAt ℝ (data.velocity · x) t)
    (hMomentumDensity : ∀ t,
      Differentiable ℝ (momentumDensity d data.toFluidState t))
    (hVelocitySpace : ∀ t, Differentiable ℝ (data.velocity t)) :
    Euler d data ↔ ConvectiveEuler d data := by
  constructor
  · intro hConservative
    refine ⟨hConservative.1, ?_⟩
    intro t x
    have hMassFluxSpace :
        DifferentiableAt ℝ (fun x' => data.rho t x' • data.velocity t x') x := by
      simpa [momentumDensity] using (hMomentumDensity t).differentiableAt
    have hResidual : continuityResidual d data.toFluidState t x = 0 := by
      simpa [continuityResidual] using
        hConservative.1 t x (by simpa using hRhoTime t x) hMassFluxSpace
    have hLhs :=
      conservativeMomentumLHS_eq_convectiveMomentumLHS_add_continuityResidual_smul
        d data.toFluidState t x (hRhoTime t x) (hVelocityTime t x)
        (hMomentumDensity t) (hVelocitySpace t)
    have hLhs' :
        conservativeMomentumLHS d data.toFluidState t x =
          convectiveMomentumLHS d data.toFluidState t x := by
      rw [hLhs, hResidual, zero_smul, add_zero]
    rw [← hLhs']
    exact hConservative.2 t x
  · intro hConvective
    refine ⟨hConvective.1, ?_⟩
    intro t x
    have hMassFluxSpace :
        DifferentiableAt ℝ (fun x' => data.rho t x' • data.velocity t x') x := by
      simpa [momentumDensity] using (hMomentumDensity t).differentiableAt
    have hResidual : continuityResidual d data.toFluidState t x = 0 := by
      simpa [continuityResidual] using
        hConvective.1 t x (by simpa using hRhoTime t x) hMassFluxSpace
    have hLhs :=
      conservativeMomentumLHS_eq_convectiveMomentumLHS_add_continuityResidual_smul
        d data.toFluidState t x (hRhoTime t x) (hVelocityTime t x)
        (hMomentumDensity t) (hVelocitySpace t)
    have hLhs' :
        conservativeMomentumLHS d data.toFluidState t x =
          convectiveMomentumLHS d data.toFluidState t x := by
      rw [hLhs, hResidual, zero_smul, add_zero]
    rw [hLhs']
    exact hConvective.2 t x

end FluidDynamics
