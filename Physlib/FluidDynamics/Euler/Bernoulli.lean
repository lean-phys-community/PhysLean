/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.Euler.Basic
/-!

# Bernoulli theory for Euler flows

## i. Overview

This module is reserved for Bernoulli definitions and results derived from Euler-flow
assumptions. The intended development includes the Bernoulli function associated with
velocity, enthalpy, and an external potential, together with assumptions under which it is
conserved.

## ii. Key results

- `FluidInBernoulliFlow` : Euler-flow data with enthalpy and potential fields.
- `isSteady` : Predicate saying the velocity field has no time dependence.
- `materialDerivative` : Material derivative of a scalar field along a fluid velocity field.
- `isIsentropic` : Predicate saying the entropy is materially conserved.
- `specificKineticEnergy` : The specific kinetic energy `|u|^2 / 2`.
- `bernoulliFunction` : The Bernoulli function `|u|^2 / 2 + h + Phi`.
- `LocalBernoulliLaw` : Vanishing spatial gradient of the Bernoulli function.
- `BernoulliLaw` : Spatial constancy of the Bernoulli function at each time.

## iii. Table of contents

- A. Bernoulli data
- B. Flow-state predicates
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

## A. Bernoulli data

-/

/-- The fields needed for Bernoulli theory: Euler data, entropy, enthalpy, and an external
potential.

The potential is the scalar field `Phi` that would satisfy `bodyForce = -grad Phi` in the
standard conservative-force setting. This relation is not imposed by the data structure.
-/
structure FluidInBernoulliFlow (d : ℕ) extends FluidInEulerBalance d where
  /-- The specific entropy field. -/
  entropy : ScalarField d
  /-- The specific enthalpy field. -/
  enthalpy : ScalarField d
  /-- The external potential field. -/
  potential : Space d → ℝ

/-!

## B. Flow-state predicates

-/

/-- A fluid state is steady when the velocity has zero time derivative everywhere. -/
def isSteady (d : ℕ) (fluid : FluidState d) : Prop :=
  ∀ t x, ∂ₜ (fluid.velocity · x) t = 0

/-- The material derivative `D_t f = partial_t f + u · grad f` of a scalar field. -/
noncomputable def materialDerivative (d : ℕ) (fluid : FluidState d)
    (field : ScalarField d) : ScalarField d :=
  fun t x => ∂ₜ (field · x) t + ⟪fluid.velocity t x, ∇ (field t) x⟫_ℝ

/-- A Bernoulli flow is isentropic when the entropy is materially conserved. -/
def isIsentropic (d : ℕ) (data : FluidInBernoulliFlow d) : Prop :=
  ∀ t x, materialDerivative d data.toFluidState data.entropy t x = 0

/-!

## C. Bernoulli function

-/

/-- The specific kinetic energy `|u|^2 / 2` of a fluid state. -/
noncomputable def specificKineticEnergy (d : ℕ) (fluid : FluidState d) : ScalarField d :=
  fun t x => (1 / 2 : ℝ) * ⟪fluid.velocity t x, fluid.velocity t x⟫_ℝ

/-- The Bernoulli function `|u|^2 / 2 + h + Phi`. -/
noncomputable def bernoulliFunction (d : ℕ) (data : FluidInBernoulliFlow d) : ScalarField d :=
  fun t x => specificKineticEnergy d data.toFluidState t x + data.enthalpy t x +
    data.potential x

/-!

## D. Bernoulli-law predicates

-/

/-- A local Bernoulli law: the Bernoulli function has zero spatial gradient. -/
def LocalBernoulliLaw (d : ℕ) (data : FluidInBernoulliFlow d) : Prop :=
  ∀ t x, (∇ (bernoulliFunction d data t)) x = 0

/-- A global Bernoulli law: the Bernoulli function is spatially constant at each time. -/
def BernoulliLaw (d : ℕ) (data : FluidInBernoulliFlow d) : Prop :=
  ∀ t x y, bernoulliFunction d data t x = bernoulliFunction d data t y

end FluidDynamics
