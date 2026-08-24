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

This module defines `ThermodynamicCauchyFlow`, the thermodynamic layer currently needed for
isentropic and Bernoulli-type statements.

This structure is intentionally the minimal carrier for the present thermodynamic API, not a claim
that entropy and enthalpy describe every thermodynamic process. Temperature, heat flux, and other
state data should be introduced by a further extension when an energy or heat-transport law needs
them. Keeping those fields out here lets Bernoulli and isentropic results avoid assumptions
unrelated to their statements.

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

These fields are independent of the kinematic and momentum-balance data unless additional
thermodynamic constitutive laws are imposed. They are sufficient for the current isentropic and
Bernoulli APIs; other thermodynamic fields belong in later extensions that require them. -/
structure ThermodynamicCauchyFlow (d : ℕ) extends CauchyFlow d where
  /-- The specific entropy field. -/
  entropy : ScalarField d
  /-- The specific enthalpy field. -/
  enthalpy : ScalarField d

namespace ThermodynamicCauchyFlow

end ThermodynamicCauchyFlow

end FluidDynamics
