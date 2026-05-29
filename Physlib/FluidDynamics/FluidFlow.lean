/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Physlib.SpaceAndTime.Time.Basic
/-!

# Fluid flows

## i. Overview

This module defines the basic fields used to describe a fluid on `d`-dimensional space.
The core structure `FluidFlow` contains only the density and velocity fields. Additional
fields used by momentum balance and thermodynamic laws are provided by extension structures.

## ii. Key results

- `ScalarField` : A time-dependent scalar field on space.
- `VectorField` : A time-dependent vector field on space.
- `MassDensity` : A time-dependent scalar density field.
- `VelocityField` : A time-dependent vector velocity field.
- `MomentumDensityField` : A time-dependent vector momentum density field.
- `StressTensor` : A time-dependent matrix-valued stress field.
- `BodyForce` : A time-dependent vector body-force field per unit mass.
- `FluidFlow` : The density and velocity fields of a fluid.
- `CauchyFlow` : A fluid flow with Cauchy stress and body force.
- `ThermodynamicCauchyFlow` : A Cauchy flow with entropy and enthalpy fields.

## iii. Table of contents

- A. Field types
- B. Fluid flow structures

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

## B. Fluid flow structures

-/

/-- The density and velocity fields of a fluid on `d`-dimensional space. -/
structure FluidFlow (d : ℕ) where
  /-- The mass density field. -/
  rho : MassDensity d
  /-- The velocity field. -/
  velocity : VelocityField d

/-- A fluid flow equipped with Cauchy stress and body-force fields. -/
structure CauchyFlow (d : ℕ) extends FluidFlow d where
  /-- The Cauchy stress tensor field. -/
  stress : StressTensor d
  /-- The body-force field per unit mass. -/
  bodyForce : BodyForce d

/-- A Cauchy flow equipped with thermodynamic entropy and enthalpy fields. -/
structure ThermodynamicCauchyFlow (d : ℕ) extends CauchyFlow d where
  /-- The specific entropy field. -/
  entropy : ScalarField d
  /-- The specific enthalpy field. -/
  enthalpy : ScalarField d

end FluidDynamics
