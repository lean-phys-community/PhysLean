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
- `materialDerivative` : Material derivative of a scalar field along a fluid velocity field.
- `IsIsentropic` : Predicate saying the entropy is materially conserved.
- `specificKineticEnergy` : The specific kinetic energy `|u|^2 / 2`.
- `bernoulliFunction` : The Bernoulli function `|u|^2 / 2 + h + Phi`.
- `LocalBernoulliLaw` : Vanishing spatial gradient of the Bernoulli function.
- `BernoulliLaw` : Spatial constancy of the Bernoulli function at each time.

## iii. Table of contents

- A. Conservative-force convention
- B. Thermodynamic-flow predicates
- C. Bernoulli function
- D. Bernoulli-law predicates

## iv. References

-/

@[expose] public section

open scoped InnerProductSpace
open Space
open Time

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

## B. Thermodynamic-flow predicates

-/

/-- The material derivative `D_t f = partial_t f + u · grad f` of a scalar field. -/
noncomputable def materialDerivative (d : ℕ) (fluid : FluidFlow d)
    (field : ScalarField d) : ScalarField d :=
  fun t x => ∂ₜ (field · x) t + ⟪fluid.velocity t x, ∇ (field t) x⟫_ℝ

/-- A thermodynamic flow is isentropic when the entropy is materially conserved. -/
def IsIsentropic (d : ℕ) (flow : ThermodynamicCauchyFlow d) : Prop :=
  ∀ t x, materialDerivative d flow.toFluidFlow flow.entropy t x = 0

/-!

## C. Bernoulli function

-/

/-- The specific kinetic energy `|u|^2 / 2` of a fluid flow. -/
noncomputable def specificKineticEnergy (d : ℕ) (fluid : FluidFlow d) : ScalarField d :=
  fun t x => (1 / 2 : ℝ) * ⟪fluid.velocity t x, fluid.velocity t x⟫_ℝ

/-- The Bernoulli function `|u|^2 / 2 + h + Phi`. -/
noncomputable def bernoulliFunction
    (d : ℕ) (flow : ThermodynamicCauchyFlow d) (potential : Space d → ℝ) : ScalarField d :=
  fun t x => specificKineticEnergy d flow.toFluidFlow t x + flow.enthalpy t x + potential x

/-!

## D. Bernoulli-law predicates

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
