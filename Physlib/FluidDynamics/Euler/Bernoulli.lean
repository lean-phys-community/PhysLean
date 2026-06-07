/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.Euler.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Grad
/-!

# Bernoulli theory for Euler flows

## i. Overview

This module is reserved for Bernoulli definitions and results derived from Euler-flow
assumptions. The intended development uses the shared `ThermodynamicCauchyFlow` data together
with an explicit external potential parameter, rather than defining a separate Bernoulli-flow
structure.

## ii. Key results

- `HasBodyForcePotential` : Predicate encoding the convention `specificBodyForce = -grad Phi`.
- `HasConservativeBodyForce` : Predicate saying a specific body force has some potential.
- `bernoulliFunction` : The Bernoulli function `|u|^2 / 2 + h + Phi`.
- `LocalBernoulliLaw` : Vanishing spatial gradient of the Bernoulli function.
- `BernoulliLaw` : Spatial constancy of the Bernoulli function at each time.

## iii. Table of contents

- A. Conservative-force convention
- B. Bernoulli function
- C. Bernoulli-law predicates

## iv. References

-/

@[expose] public section

open Space

namespace FluidDynamics

/-!

## A. Conservative-force convention

-/

/-- A flow has body-force potential `Phi` when its specific body force is minus the gradient of
`Phi`. -/
def HasBodyForcePotential (d : ℕ) (flow : CauchyFlow d) (potential : Space d → ℝ) : Prop :=
  ∀ t x, flow.specificBodyForce t x = -(∇ potential x)

/-- A flow has conservative body force when its specific body force has some potential. -/
def HasConservativeBodyForce (d : ℕ) (flow : CauchyFlow d) : Prop :=
  ∃ potential : Space d → ℝ, HasBodyForcePotential d flow potential

/-!

## B. Bernoulli function

-/

/-- The Bernoulli function `|u|^2 / 2 + h + Phi`. -/
noncomputable def bernoulliFunction
    (d : ℕ) (flow : ThermodynamicCauchyFlow d) (potential : Space d → ℝ) : ScalarField d :=
  fun t x => FluidFlow.specificKineticEnergy d flow.toFluidFlow t x + flow.enthalpy t x +
    potential x

/-!

## C. Bernoulli-law predicates

-/

/-- A local Bernoulli law: the Bernoulli function has zero spatial gradient. -/
def LocalBernoulliLaw
    (d : ℕ) (flow : ThermodynamicCauchyFlow d) (potential : Space d → ℝ) : Prop :=
  ∀ t x, (∇ (bernoulliFunction d flow potential t)) x = 0

/-- A global Bernoulli law: the Bernoulli function is spatially constant at each time. -/
def BernoulliLaw
    (d : ℕ) (flow : ThermodynamicCauchyFlow d) (potential : Space d → ℝ) : Prop :=
  ∀ t x y, bernoulliFunction d flow potential t x = bernoulliFunction d flow potential t y

end FluidDynamics
