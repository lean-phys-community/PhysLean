/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.FluidFlow.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Grad
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# Kinematic quantities for fluid flows

## i. Overview

This module defines basic kinematic predicates and scalar quantities associated to `FluidFlow`.

## ii. Key results

- `FluidFlow.DensityTimeIndependent` : A fluid flow whose density has zero time derivative.
- `FluidFlow.VelocityTimeIndependent` : A fluid flow whose velocity has zero time derivative.
- `FluidFlow.materialDerivative` : The material derivative along a fluid velocity field.
- `FluidFlow.specificKineticEnergy` : The specific kinetic energy `|u|^2 / 2`.

## iii. Table of contents

- A. Time-independence predicates
- B. Flow-derived scalar quantities

## iv. References

-/

@[expose] public section

open scoped InnerProductSpace
open Space
open Time

namespace FluidDynamics

namespace FluidFlow

/-!

## A. Time-independence predicates

-/

/-- A fluid flow has time-independent density when the density has zero time derivative at
each spatial point. -/
def DensityTimeIndependent (d : ℕ) (fluid : FluidFlow d) : Prop :=
  ∀ t x, ∂ₜ (fluid.rho · x) t = 0

/-- A fluid flow has time-independent velocity when the velocity has zero time derivative at
each spatial point. -/
def VelocityTimeIndependent (d : ℕ) (fluid : FluidFlow d) : Prop :=
  ∀ t x, ∂ₜ (fluid.velocity · x) t = 0

/-!

## B. Flow-derived scalar quantities

-/

/-- The material derivative `D_t f = partial_t f + u · grad f` of a scalar field. -/
noncomputable def materialDerivative (d : ℕ) (fluid : FluidFlow d)
    (field : ScalarField d) : ScalarField d :=
  fun t x => ∂ₜ (field · x) t + ⟪fluid.velocity t x, ∇ (field t) x⟫_ℝ

/-- The specific kinetic energy `|u|^2 / 2` of a fluid flow. -/
noncomputable def specificKineticEnergy (d : ℕ) (fluid : FluidFlow d) : ScalarField d :=
  fun t x => (1 / 2 : ℝ) * ⟪fluid.velocity t x, fluid.velocity t x⟫_ℝ

end FluidFlow

end FluidDynamics
