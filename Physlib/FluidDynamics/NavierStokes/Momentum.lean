/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.Momentum
/-!

# The Navier-Stokes momentum equations

## i. Overview

This module defines the conservative and convective momentum equations for a fluid with
stress and body-force fields. The stress tensor is left as an input field, so this is the
balance-law layer before specializing to a Newtonian stress law.

## ii. Key results

- `MomentumEquation` : Conservation of momentum using `Space.matrixDiv`.
- `ConvectiveMomentumEquation` : The momentum equation in convective form.
- `momentumEquation_iff_convectiveMomentumEquation` : Equivalence of the two
  momentum equations when continuity holds and the fields are differentiable.

## iii. Table of contents

- A. Conservative momentum equation
- B. Convective momentum equation
- C. Equivalence of conservative and convective momentum

## iv. References

-/

@[expose] public section

open Space
open Time

namespace FluidDynamics
namespace NavierStokes

/-!

## A. Conservative momentum equation

-/

/-- Conservation of momentum in conservative matrix-divergence form.

The equation is

`partial_t (rho u) + matrixDiv (rho u ⊗ u) = matrixDiv sigma + rho f`.

Here `stress` is intentionally not yet specialized to a Newtonian stress law.
-/
def MomentumEquation (d : ℕ) (data : CauchyFlow d) : Prop :=
  ∀ t x,
    conservativeMomentumLHS d data.toFluidFlow t x =
      matrixDiv d (data.stress t) x + data.rho t x • data.bodyForce t x

/-!

## B. Convective momentum equation

-/

/-- Conservation of momentum in convective form.

The equation is

`rho (partial_t u + (u · ∇)u) = matrixDiv sigma + rho f`.

Here `stress` is intentionally not yet specialized to a Newtonian stress law.
-/
def ConvectiveMomentumEquation (d : ℕ) (data : CauchyFlow d) : Prop :=
  ∀ t x,
    data.rho t x • materialAcceleration d data.toFluidFlow t x =
      matrixDiv d (data.stress t) x + data.rho t x • data.bodyForce t x

/-!

## C. Equivalence of conservative and convective momentum

-/

/-- The conservative and convective momentum equations are equivalent when the classical
continuity equation holds.

The differentiability assumptions are exactly the product-rule assumptions used to rewrite
`partial_t (rho u)` and `matrixDiv (rho u ⊗ u)`.
-/
theorem momentumEquation_iff_convectiveMomentumEquation
    (d : ℕ) (data : CauchyFlow d)
    (hContinuity : ClassicalContinuityEquation d data.toFluidFlow)
    (hRhoTime : ∀ t x, DifferentiableAt ℝ (data.rho · x) t)
    (hVelocityTime : ∀ t x, DifferentiableAt ℝ (data.velocity · x) t)
    (hMomentumDensity : ∀ t, Differentiable ℝ (momentumDensity d data.toFluidFlow t))
    (hVelocitySpace : ∀ t, Differentiable ℝ (data.velocity t)) :
    MomentumEquation d data ↔ ConvectiveMomentumEquation d data := by
  have conservative_eq_convective_lhs : ∀ t x, conservativeMomentumLHS d data.toFluidFlow t x =
      convectiveMomentumLHS d data.toFluidFlow t x := by
    intro t x
    have hResidual : continuityResidual d data.toFluidFlow t x = 0 := by
      simpa [continuityResidual] using
        hContinuity t x (by simpa using hRhoTime t x) (hMomentumDensity t).differentiableAt
    rw [conservativeMomentumLHS_eq_convectiveMomentumLHS_add_continuityResidual_smul
        d data.toFluidFlow t x (hRhoTime t x) (hVelocityTime t x)
        (hMomentumDensity t) (hVelocitySpace t), hResidual, zero_smul, add_zero]
  exact ⟨fun h t x => (conservative_eq_convective_lhs t x).symm.trans (h t x),
    fun h t x => (conservative_eq_convective_lhs t x).trans (h t x)⟩

end NavierStokes
end FluidDynamics
