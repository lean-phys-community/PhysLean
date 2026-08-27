/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Grad
/-!

# Body-force predicates for Cauchy flows

## i. Overview

This module defines predicates for conservative specific body forces on `CauchyFlow`.

## ii. Key results

- `CauchyFlow.HasBodyForcePotential` : Predicate encoding the convention
  `specificBodyForce = -grad Phi`.
- `CauchyFlow.HasConservativeBodyForce` : Predicate saying the specific body force has some
  potential.

## iii. Table of contents

- A. Conservative-force convention

## iv. References

-/

@[expose] public section

open Space

namespace FluidDynamics

namespace CauchyFlow

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

end CauchyFlow

end FluidDynamics
