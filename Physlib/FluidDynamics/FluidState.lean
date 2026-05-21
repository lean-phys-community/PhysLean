/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Physlib.SpaceAndTime.Time.Basic
/-!

# Fluid states

## i. Overview

This module defines the basic fields used to describe a fluid on `d`-dimensional space.
The core structure `FluidState` contains only the density and velocity fields. Additional
fields used by specific balance laws are provided by extension structures.

## ii. Key results

- `ScalarField` : A time-dependent scalar field on space.
- `VectorField` : A time-dependent vector field on space.
- `MassDensity` : A time-dependent scalar density field.
- `VelocityField` : A time-dependent vector velocity field.
- `MomentumDensityField` : A time-dependent vector momentum density field.
- `StressTensor` : A time-dependent matrix-valued stress field.
- `BodyForce` : A time-dependent vector body-force field per unit mass.
- `FluidState` : The density and velocity fields of a fluid.
- `FluidInMomentumBalance` : A fluid state with stress and body force.

## iii. Table of contents

- A. Field types
- B. Fluid state structures

## iv. References

-/

@[expose] public section

namespace FluidDynamics

/-!

## A. Field types

-/

/-- A scalar field on `d`-dimensional space, depending on time. -/
abbrev ScalarField (d : ℕ) := Time → Space d → ℝ

/-- A vector field on `d`-dimensional space, depending on time. -/
abbrev VectorField (d : ℕ) := Time → Space d → EuclideanSpace ℝ (Fin d)

/-- A mass density field on `d`-dimensional space. -/
abbrev MassDensity (d : ℕ) := ScalarField d

/-- A velocity field on `d`-dimensional space. -/
abbrev VelocityField (d : ℕ) := VectorField d

/-- A momentum density field on `d`-dimensional space. -/
abbrev MomentumDensityField (d : ℕ) := VectorField d

/-- A matrix-valued stress tensor field on `d`-dimensional space. -/
abbrev StressTensor (d : ℕ) := Time → Space d → Matrix (Fin d) (Fin d) ℝ

/-- A body-force field per unit mass on `d`-dimensional space. -/
abbrev BodyForce (d : ℕ) := VectorField d

/-!

## B. Fluid state structures

-/

/-- The density and velocity fields of a fluid on `d`-dimensional space. -/
structure FluidState (d : ℕ) where
  /-- The mass density field. -/
  rho : MassDensity d
  /-- The velocity field. -/
  velocity : VelocityField d

/-- The fields needed for a momentum balance: fluid state, stress, and body force. -/
structure FluidInMomentumBalance (d : ℕ) extends FluidState d where
  /-- The stress tensor field. -/
  stress : StressTensor d
  /-- The body-force field per unit mass. -/
  bodyForce : BodyForce d

end FluidDynamics
