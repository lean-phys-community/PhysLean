/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.FluidState
public import Physlib.SpaceAndTime.Space.Derivatives.Div
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# The Navier-Stokes continuity equation

## i. Overview

This module defines the conservative mass-balance equation for a fluid state and the
corresponding continuity residual.

## ii. Key results

- `ContinuityEquation` : Conservation of mass in conservative form.
- `continuityResidual` : The scalar residual `partial_t rho + div (rho u)`.

## iii. Table of contents

- A. Continuity equation

## iv. References

-/

@[expose] public section

open Space
open Time

namespace FluidDynamics
namespace NavierStokes

/-!

## A. Continuity equation

-/

/-- Conservation of mass in conservative form, `partial_t rho + div (rho u) = 0`. -/
def ContinuityEquation (d : ℕ) (fluid : FluidState d) : Prop :=
  ∀ t x,
    ∂ₜ (fun t' => fluid.rho t' x) t +
      (∇ ⬝ fun x' => fluid.rho t x' • fluid.velocity t x') x =
        0

/-- The scalar continuity-equation residual
`partial_t rho + div (rho u)`. -/
noncomputable def continuityResidual (d : ℕ) (fluid : FluidState d) :
    Time → Space d → ℝ :=
  fun t x =>
    ∂ₜ (fun t' => fluid.rho t' x) t +
      (∇ ⬝ fun x' => fluid.rho t x' • fluid.velocity t x') x

end NavierStokes
end FluidDynamics
