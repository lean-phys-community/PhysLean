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

This is the momentum-balance layer of the fluid API. The Cauchy stress is the primitive
dynamic field; pressure and viscosity enter through stress laws rather than as fields of
`CauchyFlow` itself. -/
structure CauchyFlow (d : ℕ) extends FluidFlow d where
  /-- The Cauchy stress tensor field. -/
  stress : StressTensor d
  /-- The specific body-force field, i.e. force per unit mass. -/
  specificBodyForce : VectorField d

end FluidDynamics
