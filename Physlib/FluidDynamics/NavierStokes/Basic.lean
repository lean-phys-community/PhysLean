/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Mathlib.Data.Matrix.Mul
public import Physlib.SpaceAndTime.Space.Derivatives.Div
public import Physlib.SpaceAndTime.Space.Derivatives.TensorDiv
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# The Navier-Stokes equations

## i. Overview

The Navier-Stokes equations are a set of partial differential equations that describe
the motion of viscous fluid substances. They are fundamental in fluid dynamics and are
used to model the behavior of fluids in various contexts, including gas flow and water flow.

This file starts with the conservative tensor-divergence form and the convective form. The
stress tensor is left as an input field, so this is the balance-law layer before specializing
to a Newtonian stress law.

## ii. Key results

- `MassDensity` : A time-dependent scalar density field.
- `VelocityField` : A time-dependent vector velocity field.
- `StressTensor` : A time-dependent matrix-valued stress field.
- `momentumDensity` : The vector momentum density `rho u`.
- `momentumFlux` : The convective momentum flux `rho u ⊗ u`.
- `convectiveTerm` : The nonlinear transport term `(u · ∇)u`.
- `materialAcceleration` : The material acceleration `∂ₜ u + (u · ∇)u`.
- `ContinuityEquation` : Conservation of mass.
- `ConservativeMomentumEquation` : Conservation of momentum using `Space.tensorDiv`.
- `ConservativeForm` : Continuity and conservative momentum equations together.
- `ConvectiveMomentumEquation` : The momentum equation in convective form.
- `ConvectiveForm` : Continuity and convective momentum equations together.

## iii. Table of contents

- A. Field types
- B. Momentum fields
- C. Conservative equations
- D. Convective equations

## iv. References

-/

@[expose] public section

open Space
open Time

namespace FluidDynamics
namespace NavierStokes

/-!

## A. Field types

-/

/-- A mass density field on `d`-dimensional space. -/
abbrev MassDensity (d : ℕ) := Time → Space d → ℝ

/-- A velocity field on `d`-dimensional space. -/
abbrev VelocityField (d : ℕ) := Time → Space d → EuclideanSpace ℝ (Fin d)

/-- A matrix-valued stress tensor field on `d`-dimensional space. -/
abbrev StressTensor (d : ℕ) := Time → Space d → Matrix (Fin d) (Fin d) ℝ

/-- A body-force field per unit mass on `d`-dimensional space. -/
abbrev BodyForce (d : ℕ) := Time → Space d → EuclideanSpace ℝ (Fin d)

/-!

## B. Momentum fields

-/

/-- The momentum density `rho u`. -/
def momentumDensity (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d) :
    VelocityField d :=
  fun time position => rho time position • velocity time position

/-- The convective momentum flux `rho u ⊗ u`. -/
def momentumFlux (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d) :
    Time → Space d → Matrix (Fin d) (Fin d) ℝ :=
  fun time position =>
    rho time position • Matrix.vecMulVec
      (fun i => velocity time position i) (fun j => velocity time position j)

lemma momentumDensity_apply (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d)
    (time : Time) (position : Space d) :
    momentumDensity d rho velocity time position =
      rho time position • velocity time position := rfl

lemma momentumFlux_apply (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d)
    (time : Time) (position : Space d) (i j : Fin d) :
    momentumFlux d rho velocity time position i j =
      rho time position * velocity time position i * velocity time position j := by
  simp [momentumFlux, Matrix.vecMulVec_apply, mul_assoc]

/-!

## C. Conservative equations

-/

/-- Conservation of mass in conservative form, `partial_t rho + div (rho u) = 0`. -/
def ContinuityEquation (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d) :
    Prop :=
  ∀ time position,
    ∂ₜ (fun time' => rho time' position) time +
      (∇ ⬝ fun position' => rho time position' • velocity time position') position = 0

/-- Conservation of momentum in conservative tensor-divergence form.

The equation is

`partial_t (rho u) + div_tensor (rho u ⊗ u) = div_tensor sigma + rho f`.

Here `stress` is intentionally not yet specialized to a Newtonian stress law.
-/
def ConservativeMomentumEquation (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d)
    (stress : StressTensor d) (bodyForce : BodyForce d) : Prop :=
  ∀ time position,
    ∂ₜ (fun time' => momentumDensity d rho velocity time' position) time +
        tensorDiv d (momentumFlux d rho velocity time) position =
      tensorDiv d (stress time) position + rho time position • bodyForce time position

/-- The conservative Navier-Stokes balance-law form with an externally supplied stress tensor. -/
def ConservativeForm (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d)
    (stress : StressTensor d) (bodyForce : BodyForce d) : Prop :=
  ContinuityEquation d rho velocity ∧
    ConservativeMomentumEquation d rho velocity stress bodyForce

/-!

## D. Convective equations

-/

/-- The nonlinear transport term `(u · ∇)u`. -/
noncomputable def convectiveTerm (d : ℕ) (velocity : VelocityField d) : VelocityField d :=
  fun time position => ∑ j, velocity time position j • ∂[j] (velocity time) position

/-- The material acceleration `∂ₜ u + (u · ∇)u`. -/
noncomputable def materialAcceleration (d : ℕ) (velocity : VelocityField d) : VelocityField d :=
  fun time position =>
    ∂ₜ (fun time' => velocity time' position) time +
      convectiveTerm d velocity time position

lemma convectiveTerm_apply (d : ℕ) (velocity : VelocityField d)
    (time : Time) (position : Space d) :
    convectiveTerm d velocity time position =
      ∑ j, velocity time position j • ∂[j] (velocity time) position := rfl

lemma materialAcceleration_apply (d : ℕ) (velocity : VelocityField d)
    (time : Time) (position : Space d) :
    materialAcceleration d velocity time position =
      ∂ₜ (fun time' => velocity time' position) time +
        convectiveTerm d velocity time position := rfl

/-- Conservation of momentum in convective form.

The equation is

`rho (partial_t u + (u · ∇)u) = div_tensor sigma + rho f`.

Here `stress` is intentionally not yet specialized to a Newtonian stress law.
-/
def ConvectiveMomentumEquation (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d)
    (stress : StressTensor d) (bodyForce : BodyForce d) : Prop :=
  ∀ time position,
    rho time position • materialAcceleration d velocity time position =
      tensorDiv d (stress time) position + rho time position • bodyForce time position

/-- The convective Navier-Stokes form with an externally supplied stress tensor. -/
def ConvectiveForm (d : ℕ) (rho : MassDensity d) (velocity : VelocityField d)
    (stress : StressTensor d) (bodyForce : BodyForce d) : Prop :=
  ContinuityEquation d rho velocity ∧
    ConvectiveMomentumEquation d rho velocity stress bodyForce

end NavierStokes
end FluidDynamics
