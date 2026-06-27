/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Div
/-!

# Newtonian stress laws for Cauchy flows

## i. Overview

This module defines the Newtonian constitutive stress law for `CauchyFlow`.

## ii. Key results

- `CauchyFlow.velocityGradient` : The spatial velocity-gradient matrix.
- `CauchyFlow.newtonianStressTensor` : The Newtonian stress tensor determined by pressure and
  viscosity.
- `CauchyFlow.IsNewtonian` : Predicate saying the Cauchy stress has Newtonian constitutive form.

## iii. Table of contents

- A. Newtonian stress law

## iv. References

-/

@[expose] public section

open Space

namespace FluidDynamics

namespace CauchyFlow

/-!

## A. Newtonian stress law

-/

/-- The spatial velocity-gradient matrix, with entries `partial_j u_i`. -/
noncomputable def velocityGradient (d : ℕ) (flow : FluidFlow d) :
    Time → Space d → Matrix (Fin d) (Fin d) ℝ :=
  fun t x i j => ∂[j] (fun x' => flow.velocity t x' i) x

/-- The Newtonian stress tensor
`-p I + mu (grad u + grad u^T) + lambda (div u) I`.

The scalar fields are pressure, shear viscosity, and second viscosity.
-/
noncomputable def newtonianStressTensor (d : ℕ) (flow : FluidFlow d)
    (pressure shearViscosity secondViscosity : ScalarField d) : StressTensor d :=
  fun t x =>
    (-(pressure t x)) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      shearViscosity t x •
        (velocityGradient d flow t x + Matrix.transpose (velocityGradient d flow t x)) +
        (secondViscosity t x * (∇ ⬝ flow.velocity t) x) •
          (1 : Matrix (Fin d) (Fin d) ℝ)

/-- A Cauchy flow is Newtonian when its stress tensor has the Newtonian constitutive form. -/
def IsNewtonian
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity secondViscosity : ScalarField d) : Prop :=
  ∀ t x,
    flow.stress t x =
      newtonianStressTensor d flow.toFluidFlow pressure shearViscosity secondViscosity t x

end CauchyFlow

end FluidDynamics
