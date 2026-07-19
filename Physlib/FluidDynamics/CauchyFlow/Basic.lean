/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.FluidFlow.Basic
/-!

# Basic API for Cauchy flows

## i. Overview

This module defines `CauchyFlow`, the momentum-balance layer of the fluid API.
Specialized predicates and equations for Cauchy flows are organized in sibling modules.

A local Cauchy momentum balance needs two kinds of force data beyond density and velocity. The
stress tensor encodes contact forces through its divergence, while the specific body force encodes
volumetric forces per unit mass and therefore contributes mass density times specific body force.
Together these fields are sufficient to state the balance without choosing a material model.

The momentum equation constrains the flow and forces but does not define a constitutive relation
between them. Pressure and viscosity are therefore not stored as additional fields.
They enter through constitutive stress laws, such as the inviscid and Newtonian predicates,
which avoids duplicating data and imposing consistency conditions inside the carrier.
Thermodynamic data is deferred to `ThermodynamicCauchyFlow` because it is not needed
for momentum balance alone.

## ii. Key results

- `CauchyFlow` : A fluid flow with Cauchy stress and specific body force.

## iii. Table of contents

- A. Cauchy-flow structure

## iv. References

-/

@[expose] public section

namespace FluidDynamics

/-!

## A. Cauchy-flow structure

-/

/-- A fluid flow equipped with Cauchy stress and specific body-force fields.

These are the additional independent fields needed to state a local momentum balance. The Cauchy
stress represents contact forces, and the specific body force represents volumetric force per unit
mass. Pressure and viscosity enter through stress laws rather than as redundant fields of
`CauchyFlow` itself. -/
structure CauchyFlow (d : ℕ) extends FluidFlow d where
  /-- The Cauchy stress tensor field. -/
  stress : StressTensor d
  /-- The specific body-force field, i.e. force per unit mass. -/
  specificBodyForce : VectorField d

end FluidDynamics
