/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.FluidFlow.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Div
/-!

# Incompressible fluid flows

## i. Overview

This module defines general incompressibility predicates for fluid flows. These predicates are
not tied to a particular equation of motion, so they can be reused later by incompressible
Navier-Stokes, incompressible Euler, and Bernoulli-style developments.

## ii. Key results

- `FluidFlow.incompressibilityResidual` : The divergence of the velocity field.
- `FluidFlow.ClassicalIncompressible` : Incompressibility guarded by velocity differentiability.
- `FluidFlow.SmoothIncompressible` : Incompressibility with globally differentiable velocity.
- `FluidFlow.classicalIncompressible_of_smoothIncompressible` : Smooth incompressibility implies
  classical incompressibility.

## iii. Table of contents

- A. Incompressibility predicates

## iv. References

-/

@[expose] public section

open Space

namespace FluidDynamics

namespace FluidFlow

/-!

## A. Incompressibility predicates

-/

/-- The incompressibility residual, given by the divergence of the velocity field. -/
noncomputable def incompressibilityResidual (d : ℕ) (fluid : FluidFlow d) :
    Time → Space d → ℝ :=
  fun t x => (∇ ⬝ fluid.velocity t) x

/-- A classical incompressible flow has divergence-free velocity at points where the velocity
field is differentiable. -/
def ClassicalIncompressible (d : ℕ) (fluid : FluidFlow d) : Prop :=
  ∀ t x, DifferentiableAt ℝ (fluid.velocity t) x →
    incompressibilityResidual d fluid t x = 0

/-- A smooth incompressible flow has globally differentiable velocity and vanishing
incompressibility residual everywhere. -/
def SmoothIncompressible (d : ℕ) (fluid : FluidFlow d) : Prop :=
  (∀ t, Differentiable ℝ (fluid.velocity t)) ∧
    ∀ t x, incompressibilityResidual d fluid t x = 0

/-- A smooth incompressible flow is classically incompressible. -/
lemma classicalIncompressible_of_smoothIncompressible
    (d : ℕ) (fluid : FluidFlow d) :
    SmoothIncompressible d fluid → ClassicalIncompressible d fluid := by
  intro hSmooth t x _
  simpa [incompressibilityResidual] using hSmooth.2 t x

end FluidFlow

end FluidDynamics
