/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Basic
/-!

# Basic predicates for thermodynamic Cauchy flows

## i. Overview

This module defines `ThermodynamicCauchyFlow`.

## ii. Key results

- `ThermodynamicCauchyFlow` : A Cauchy flow with entropy and enthalpy fields.

## iii. Table of contents

- A. Thermodynamic Cauchy-flow structure

## iv. References

-/

@[expose] public section

namespace FluidDynamics

/-!

## A. Thermodynamic Cauchy-flow structure

-/

/-- A Cauchy flow equipped with thermodynamic entropy and enthalpy fields.

This extends the kinematic and momentum-balance data with thermodynamic fields used by
isentropic and Bernoulli-type laws. -/
structure ThermodynamicCauchyFlow (d : ℕ) extends CauchyFlow d where
  /-- The specific entropy field. -/
  entropy : ScalarField d
  /-- The specific enthalpy field. -/
  enthalpy : ScalarField d

namespace ThermodynamicCauchyFlow

end ThermodynamicCauchyFlow

end FluidDynamics
