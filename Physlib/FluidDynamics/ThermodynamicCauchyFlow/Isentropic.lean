/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.FluidFlow.Kinematics
public import Physlib.FluidDynamics.ThermodynamicCauchyFlow.Basic
/-!

# Isentropic thermodynamic Cauchy flows

## i. Overview

This module defines the isentropic predicate for thermodynamic Cauchy flows.

## ii. Key results

- `ThermodynamicCauchyFlow.IsIsentropic` : A thermodynamic Cauchy flow whose entropy is
  materially conserved.

## iii. Table of contents

- A. Thermodynamic-flow predicates

## iv. References

-/

@[expose] public section

namespace FluidDynamics

namespace ThermodynamicCauchyFlow

/-!

## A. Thermodynamic-flow predicates

-/

/-- A thermodynamic flow is isentropic when the entropy is materially conserved along the
underlying fluid velocity field. -/
def IsIsentropic (d : ℕ) (flow : ThermodynamicCauchyFlow d) : Prop :=
  ∀ t x, FluidFlow.materialDerivative d flow.toFluidFlow flow.entropy t x = 0

end ThermodynamicCauchyFlow

end FluidDynamics
