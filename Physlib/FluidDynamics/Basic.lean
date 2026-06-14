/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Grad
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# Fluid flows

## i. Overview

This module defines the basic fields used to describe a fluid on `d`-dimensional space.
The core structure `FluidFlow` contains only the density and velocity fields, so it is the
minimal data needed for kinematic and mass-transport constructions such as continuity,
incompressibility, momentum density, and material derivatives. The structure `CauchyFlow`
adds Cauchy stress and specific body-force fields, the extra data used for momentum balances.
The structure `ThermodynamicCauchyFlow` adds entropy and enthalpy fields for thermodynamic
laws such as Bernoulli-type statements.

## ii. Key results

- `ScalarField` : A time-dependent scalar field on space.
- `VectorField` : A time-dependent vector field on space.
- `MassDensity` : A time-dependent scalar density field.
- `VelocityField` : A time-dependent vector velocity field.
- `MomentumDensityField` : A time-dependent vector momentum density field.
- `StressTensor` : A time-dependent matrix-valued stress field.
- `FluidFlow` : The density and velocity fields of a fluid.
- `CauchyFlow` : A fluid flow with Cauchy stress and specific body force.
- `ThermodynamicCauchyFlow` : A Cauchy flow with entropy and enthalpy fields.
- `FluidFlow.DensityTimeIndependent` : A fluid flow whose density has zero time derivative.
- `FluidFlow.VelocityTimeIndependent` : A fluid flow whose velocity has zero time derivative.
- `FluidFlow.materialDerivative` : The material derivative along a fluid velocity field.
- `FluidFlow.specificKineticEnergy` : The specific kinetic energy `|u|^2 / 2`.
- `ThermodynamicCauchyFlow.IsIsentropic` : A thermodynamic Cauchy flow whose entropy is
  materially conserved.

## iii. Table of contents

- A. Field types
- B. Fluid flow structures
- C. Time-independence predicates
- D. Flow-derived scalar quantities
- E. Thermodynamic-flow predicates

## iv. References

-/

@[expose] public section

open scoped InnerProductSpace
open Space
open Time

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

/-!

## B. Fluid flow structures

-/

/-- The density and velocity fields of a fluid on `d`-dimensional space.

This is the kinematic/mass-transport layer of the fluid API. It intentionally contains no
stress, body force, or thermodynamic fields. Those are introduced only by the extension
structures that need them. -/
structure FluidFlow (d : ℕ) where
  /-- The mass density field. -/
  rho : MassDensity d
  /-- The velocity field. -/
  velocity : VelocityField d

/-- A fluid flow equipped with Cauchy stress and specific body-force fields.

This is the momentum-balance layer of the fluid API. The Cauchy stress is the primitive
dynamic field; pressure and viscosity enter through stress laws rather than as fields of
`CauchyFlow` itself. -/
structure CauchyFlow (d : ℕ) extends FluidFlow d where
  /-- The Cauchy stress tensor field. -/
  stress : StressTensor d
  /-- The specific body-force field, i.e. force per unit mass. -/
  specificBodyForce : VectorField d

/-- A Cauchy flow equipped with thermodynamic entropy and enthalpy fields.

This extends the kinematic and momentum-balance data with thermodynamic fields used by
isentropic and Bernoulli-type laws. -/
structure ThermodynamicCauchyFlow (d : ℕ) extends CauchyFlow d where
  /-- The specific entropy field. -/
  entropy : ScalarField d
  /-- The specific enthalpy field. -/
  enthalpy : ScalarField d

/-!

## C. Time-independence predicates

-/

namespace FluidFlow

/-- A fluid flow has time-independent density when the density has zero time derivative at
each spatial point. -/
def DensityTimeIndependent (d : ℕ) (fluid : FluidFlow d) : Prop :=
  ∀ t x, ∂ₜ (fluid.rho · x) t = 0

/-- A fluid flow has time-independent velocity when the velocity has zero time derivative at
each spatial point. -/
def VelocityTimeIndependent (d : ℕ) (fluid : FluidFlow d) : Prop :=
  ∀ t x, ∂ₜ (fluid.velocity · x) t = 0

end FluidFlow

/-!

## D. Flow-derived scalar quantities

-/

namespace FluidFlow

/-- The material derivative `D_t f = partial_t f + u · grad f` of a scalar field. -/
noncomputable def materialDerivative (d : ℕ) (fluid : FluidFlow d)
    (field : ScalarField d) : ScalarField d :=
  fun t x => ∂ₜ (field · x) t + ⟪fluid.velocity t x, ∇ (field t) x⟫_ℝ

/-- The specific kinetic energy `|u|^2 / 2` of a fluid flow. -/
noncomputable def specificKineticEnergy (d : ℕ) (fluid : FluidFlow d) : ScalarField d :=
  fun t x => (1 / 2 : ℝ) * ⟪fluid.velocity t x, fluid.velocity t x⟫_ℝ

end FluidFlow

/-!

## E. Thermodynamic-flow predicates

-/

namespace ThermodynamicCauchyFlow

/-- A thermodynamic flow is isentropic when the entropy is materially conserved along the
underlying fluid velocity field. -/
def IsIsentropic (d : ℕ) (flow : ThermodynamicCauchyFlow d) : Prop :=
  ∀ t x, FluidFlow.materialDerivative d flow.toFluidFlow flow.entropy t x = 0

end ThermodynamicCauchyFlow

end FluidDynamics
