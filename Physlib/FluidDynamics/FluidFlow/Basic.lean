/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.Basic
/-!

# Basic API for fluid flows

## i. Overview

This module defines `FluidFlow`, the kinematic/mass-transport layer of the fluid API.

## ii. Key results

- `FluidFlow` : The density and velocity fields of a fluid.

## iii. Table of contents

- A. Fluid-flow structure

## iv. References

-/

@[expose] public section

namespace FluidDynamics

/-!

## A. Fluid-flow structure

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

namespace FluidFlow

end FluidFlow

end FluidDynamics
