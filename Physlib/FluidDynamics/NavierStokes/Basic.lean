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
- `FluidState` : The density and velocity fields of a fluid.
- `MomentumBalanceData` : The fluid state together with stress and body force.
- `momentumDensity` : The vector momentum density `rho u`.
- `momentumFlux` : The convective momentum flux `rho u ⊗ u`.
- `convectiveTerm` : The nonlinear transport term `(u · ∇)u`.
- `materialAcceleration` : The material acceleration `∂ₜ u + (u · ∇)u`.
- `ContinuityEquation` : Conservation of mass.
- `ConservativeMomentumEquation` : Conservation of momentum using `Space.tensorDiv`.
- `ConservativeForm` : Continuity and conservative momentum equations together.
- `ConvectiveMomentumEquation` : The momentum equation in convective form.
- `ConvectiveForm` : Continuity and convective momentum equations together.
- `ConservativeMomentumEquation_iff_ConvectiveMomentumEquation` : Equivalence of the two
  momentum equations when continuity holds and the fields are differentiable.
- `ConservativeForm_iff_ConvectiveForm` : Equivalence of the two forms when the
  fields are differentiable.

## iii. Table of contents

- A. Field types
- B. Fluid and momentum-balance data
- C. Momentum fields
- D. Conservative equations
- E. Convective equations
- F. Equivalence of conservative and convective forms

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

## B. Fluid and momentum-balance data

-/

/-- The density and velocity fields of a fluid on `d`-dimensional space. -/
structure FluidState (d : ℕ) where
  /-- The mass density field. -/
  rho : MassDensity d
  /-- The velocity field. -/
  velocity : VelocityField d

/-- The data needed for a momentum balance: fluid state, stress, and body force. -/
structure MomentumBalanceData (d : ℕ) extends FluidState d where
  /-- The stress tensor field. -/
  stress : StressTensor d
  /-- The body-force field per unit mass. -/
  bodyForce : BodyForce d

/-!

## C. Momentum fields

-/

/-- The momentum density `rho u`. -/
def momentumDensity (d : ℕ) (fluid : FluidState d) : VelocityField d :=
  fun time position => fluid.rho time position • fluid.velocity time position

/-- The convective momentum flux `rho u ⊗ u`. -/
def momentumFlux (d : ℕ) (fluid : FluidState d) :
    Time → Space d → Matrix (Fin d) (Fin d) ℝ :=
  fun time position =>
    fluid.rho time position • Matrix.vecMulVec
      (fun i => fluid.velocity time position i) (fun j => fluid.velocity time position j)

/-!

## D. Conservative equations

-/

/-- Conservation of mass in conservative form, `partial_t rho + div (rho u) = 0`. -/
def ContinuityEquation (d : ℕ) (fluid : FluidState d) : Prop :=
  ∀ time position,
    ∂ₜ (fun time' => fluid.rho time' position) time +
      (∇ ⬝ fun position' => fluid.rho time position' • fluid.velocity time position') position =
        0

/-- Conservation of momentum in conservative tensor-divergence form.

The equation is

`partial_t (rho u) + div_tensor (rho u ⊗ u) = div_tensor sigma + rho f`.

Here `stress` is intentionally not yet specialized to a Newtonian stress law.
-/
def ConservativeMomentumEquation (d : ℕ) (data : MomentumBalanceData d) : Prop :=
  ∀ time position,
    ∂ₜ (fun time' => momentumDensity d data.toFluidState time' position) time +
        tensorDiv d (momentumFlux d data.toFluidState time) position =
      tensorDiv d (data.stress time) position +
        data.rho time position • data.bodyForce time position

/-- The conservative Navier-Stokes balance-law form with an externally supplied stress tensor. -/
def ConservativeForm (d : ℕ) (data : MomentumBalanceData d) : Prop :=
  ContinuityEquation d data.toFluidState ∧
    ConservativeMomentumEquation d data

/-!

## E. Convective equations

-/

/-- The nonlinear transport term `(u · ∇)u`. -/
noncomputable def convectiveTerm (d : ℕ) (velocity : VelocityField d) : VelocityField d :=
  fun time position => ∑ j, velocity time position j • ∂[j] (velocity time) position

/-- The material acceleration `∂ₜ u + (u · ∇)u`. -/
noncomputable def materialAcceleration (d : ℕ) (velocity : VelocityField d) : VelocityField d :=
  fun time position =>
    ∂ₜ (fun time' => velocity time' position) time +
      convectiveTerm d velocity time position

/-- Conservation of momentum in convective form.

The equation is

`rho (partial_t u + (u · ∇)u) = div_tensor sigma + rho f`.

Here `stress` is intentionally not yet specialized to a Newtonian stress law.
-/
def ConvectiveMomentumEquation (d : ℕ) (data : MomentumBalanceData d) : Prop :=
  ∀ time position,
    data.rho time position • materialAcceleration d data.velocity time position =
      tensorDiv d (data.stress time) position +
        data.rho time position • data.bodyForce time position

/-- The convective Navier-Stokes form with an externally supplied stress tensor. -/
def ConvectiveForm (d : ℕ) (data : MomentumBalanceData d) : Prop :=
  ContinuityEquation d data.toFluidState ∧
    ConvectiveMomentumEquation d data

/-!

## F. Equivalence of conservative and convective forms

-/

/-- The scalar continuity-equation residual
`partial_t rho + div (rho u)`. -/
noncomputable def continuityResidual (d : ℕ) (fluid : FluidState d) :
    Time → Space d → ℝ :=
  fun time position =>
    ∂ₜ (fun time' => fluid.rho time' position) time +
      (∇ ⬝ fun position' => fluid.rho time position' • fluid.velocity time position') position

/-- The left-hand side of the conservative momentum equation. -/
noncomputable def conservativeMomentumLHS (d : ℕ) (fluid : FluidState d) : VelocityField d :=
  fun time position =>
    ∂ₜ (fun time' => momentumDensity d fluid time' position) time +
      tensorDiv d (momentumFlux d fluid time) position

/-- The left-hand side of the convective momentum equation. -/
noncomputable def convectiveMomentumLHS (d : ℕ) (fluid : FluidState d) : VelocityField d :=
  fun time position => fluid.rho time position • materialAcceleration d fluid.velocity time position

/-- Product rule for the time derivative of a scalar field times a velocity field. -/
lemma timeDeriv_smul_velocity (d : ℕ) (rhoAtPosition : Time → ℝ)
    (velocityAtPosition : Time → EuclideanSpace ℝ (Fin d)) (time : Time)
    (hRho : DifferentiableAt ℝ rhoAtPosition time)
    (hVelocity : DifferentiableAt ℝ velocityAtPosition time) :
    ∂ₜ (fun time' => rhoAtPosition time' • velocityAtPosition time') time =
      rhoAtPosition time • ∂ₜ velocityAtPosition time +
        ∂ₜ rhoAtPosition time • velocityAtPosition time := by
  rw [Time.deriv_eq, Time.deriv_eq, Time.deriv_eq]
  change (fderiv ℝ (rhoAtPosition • velocityAtPosition) time) 1 =
    rhoAtPosition time • (fderiv ℝ velocityAtPosition time) 1 +
      (fderiv ℝ rhoAtPosition time) 1 • velocityAtPosition time
  rw [fderiv_smul hRho hVelocity]
  rfl

/-- Product rule for the time derivative of the momentum density `rho u`. -/
lemma timeDeriv_momentumDensity (d : ℕ) (fluid : FluidState d)
    (time : Time) (position : Space d)
    (hRho : DifferentiableAt ℝ (fun time' => fluid.rho time' position) time)
    (hVelocity : DifferentiableAt ℝ (fun time' => fluid.velocity time' position) time) :
    ∂ₜ (fun time' => momentumDensity d fluid time' position) time =
      fluid.rho time position • ∂ₜ (fun time' => fluid.velocity time' position) time +
        ∂ₜ (fun time' => fluid.rho time' position) time • fluid.velocity time position := by
  simpa [momentumDensity] using
    timeDeriv_smul_velocity d (fun time' => fluid.rho time' position)
      (fun time' => fluid.velocity time' position) time hRho hVelocity

/-- Product rule for one spatial derivative of one component of `rho u ⊗ u`. -/
lemma spaceDeriv_momentumFlux_component (d : ℕ) (fluid : FluidState d)
    (time : Time) (position : Space d) (i j : Fin d)
    (hMomentumDensity : Differentiable ℝ (momentumDensity d fluid time))
    (hVelocity : Differentiable ℝ (fluid.velocity time)) :
    ∂[j] (fun position' => momentumFlux d fluid time position' i j) position =
      fluid.velocity time position i •
        ∂[j] (fun position' => momentumDensity d fluid time position' j) position +
      ∂[j] (fun position' => fluid.velocity time position' i) position •
        momentumDensity d fluid time position j := by
  have hProduct := Space.deriv_smul (u := j) (x := position)
    (c := fun position' => fluid.velocity time position' i)
    (f := fun position' => momentumDensity d fluid time position' j)
    ((differentiable_euclidean.mp hVelocity i).differentiableAt)
    ((differentiable_euclidean.mp hMomentumDensity j).differentiableAt)
  rw [← hProduct]
  congr
  funext position'
  simp [momentumFlux, momentumDensity, Matrix.vecMulVec_apply, mul_left_comm]

/-- The tensor divergence of `rho u ⊗ u` split into continuity and convective parts. -/
lemma tensorDiv_momentumFlux (d : ℕ) (fluid : FluidState d)
    (time : Time) (position : Space d)
    (hMomentumDensity : Differentiable ℝ (momentumDensity d fluid time))
    (hVelocity : Differentiable ℝ (fluid.velocity time)) :
    tensorDiv d (momentumFlux d fluid time) position =
      (∇ ⬝ momentumDensity d fluid time) position • fluid.velocity time position +
        fluid.rho time position • convectiveTerm d fluid.velocity time position := by
  ext i
  simp [tensorDiv_apply, div, convectiveTerm, smul_eq_mul]
  change (∑ j, ∂[j] (fun position' =>
      momentumFlux d fluid time position' i j) position) =
    (∑ j, ∂[j] (fun position' =>
      momentumDensity d fluid time position' j) position) *
        fluid.velocity time position i +
      fluid.rho time position *
        (∑ j, fluid.velocity time position j * ∂[j] (fluid.velocity time) position i)
  calc
    (∑ j, ∂[j] (fun position' =>
        momentumFlux d fluid time position' i j) position)
        = ∑ j,
            (fluid.velocity time position i *
                ∂[j] (fun position' =>
                  momentumDensity d fluid time position' j) position +
              ∂[j] (fun position' => fluid.velocity time position' i) position *
                momentumDensity d fluid time position j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [spaceDeriv_momentumFlux_component d fluid time position i j
            hMomentumDensity hVelocity]
          simp [smul_eq_mul]
    _ = fluid.velocity time position i *
          (∑ j, ∂[j] (fun position' =>
            momentumDensity d fluid time position' j) position) +
        fluid.rho time position *
          (∑ j, fluid.velocity time position j * ∂[j] (fluid.velocity time) position i) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Space.deriv_euclid (ν := j) (μ := i) (f := fluid.velocity time)
              hVelocity position]
            simp [momentumDensity, mul_comm, mul_assoc]
    _ = (∑ j, ∂[j] (fun position' =>
          momentumDensity d fluid time position' j) position) *
          fluid.velocity time position i +
        fluid.rho time position *
          (∑ j, fluid.velocity time position j * ∂[j] (fluid.velocity time) position i) := by
          ring

/-- The algebraic bridge between conservative and convective momentum.

The conservative momentum left-hand side equals the convective momentum left-hand side plus
the continuity residual times the velocity field.
-/
lemma conservativeMomentumLHS_eq_convectiveMomentumLHS_add_continuityResidual_smul
    (d : ℕ) (fluid : FluidState d)
    (time : Time) (position : Space d)
    (hRhoTime : DifferentiableAt ℝ (fun time' => fluid.rho time' position) time)
    (hVelocityTime : DifferentiableAt ℝ (fun time' => fluid.velocity time' position) time)
    (hMomentumDensity : Differentiable ℝ (momentumDensity d fluid time))
    (hVelocitySpace : Differentiable ℝ (fluid.velocity time)) :
    conservativeMomentumLHS d fluid time position =
      convectiveMomentumLHS d fluid time position +
        continuityResidual d fluid time position • fluid.velocity time position := by
  rw [conservativeMomentumLHS, convectiveMomentumLHS, continuityResidual]
  rw [timeDeriv_momentumDensity d fluid time position hRhoTime hVelocityTime]
  rw [tensorDiv_momentumFlux d fluid time position hMomentumDensity hVelocitySpace]
  ext i
  simp [materialAcceleration, convectiveTerm, div, momentumDensity, smul_eq_mul]
  ring_nf

/-- The conservative and convective momentum equations are equivalent when the continuity
equation holds.

The differentiability assumptions are exactly the product-rule assumptions used to rewrite
`partial_t (rho u)` and `div_tensor (rho u ⊗ u)`.
-/
theorem ConservativeMomentumEquation_iff_ConvectiveMomentumEquation
    (d : ℕ) (data : MomentumBalanceData d)
    (hContinuity : ContinuityEquation d data.toFluidState)
    (hRhoTime : ∀ time position,
      DifferentiableAt ℝ (fun time' => data.rho time' position) time)
    (hVelocityTime : ∀ time position,
      DifferentiableAt ℝ (fun time' => data.velocity time' position) time)
    (hMomentumDensity : ∀ time,
      Differentiable ℝ (momentumDensity d data.toFluidState time))
    (hVelocitySpace : ∀ time, Differentiable ℝ (data.velocity time)) :
    ConservativeMomentumEquation d data ↔
      ConvectiveMomentumEquation d data := by
  constructor
  · intro hConservative time position
    have hResidual : continuityResidual d data.toFluidState time position = 0 := by
      simpa [continuityResidual] using hContinuity time position
    have hLhs := conservativeMomentumLHS_eq_convectiveMomentumLHS_add_continuityResidual_smul
      d data.toFluidState time position (hRhoTime time position) (hVelocityTime time position)
      (hMomentumDensity time) (hVelocitySpace time)
    have hLhs' :
        conservativeMomentumLHS d data.toFluidState time position =
          convectiveMomentumLHS d data.toFluidState time position := by
      rw [hLhs, hResidual, zero_smul, add_zero]
    change convectiveMomentumLHS d data.toFluidState time position =
      tensorDiv d (data.stress time) position +
        data.rho time position • data.bodyForce time position
    rw [← hLhs']
    exact hConservative time position
  · intro hConvective time position
    have hResidual : continuityResidual d data.toFluidState time position = 0 := by
      simpa [continuityResidual] using hContinuity time position
    have hLhs := conservativeMomentumLHS_eq_convectiveMomentumLHS_add_continuityResidual_smul
      d data.toFluidState time position (hRhoTime time position) (hVelocityTime time position)
      (hMomentumDensity time) (hVelocitySpace time)
    have hLhs' :
        conservativeMomentumLHS d data.toFluidState time position =
          convectiveMomentumLHS d data.toFluidState time position := by
      rw [hLhs, hResidual, zero_smul, add_zero]
    change conservativeMomentumLHS d data.toFluidState time position =
      tensorDiv d (data.stress time) position +
        data.rho time position • data.bodyForce time position
    rw [hLhs']
    exact hConvective time position

/-- The conservative and convective Navier-Stokes forms are equivalent when the fields are
differentiable enough for the product rules. -/
theorem ConservativeForm_iff_ConvectiveForm
    (d : ℕ) (data : MomentumBalanceData d)
    (hRhoTime : ∀ time position,
      DifferentiableAt ℝ (fun time' => data.rho time' position) time)
    (hVelocityTime : ∀ time position,
      DifferentiableAt ℝ (fun time' => data.velocity time' position) time)
    (hMomentumDensity : ∀ time,
      Differentiable ℝ (momentumDensity d data.toFluidState time))
    (hVelocitySpace : ∀ time, Differentiable ℝ (data.velocity time)) :
    ConservativeForm d data ↔
      ConvectiveForm d data := by
  constructor
  · intro hConservative
    refine ⟨hConservative.1, ?_⟩
    exact (ConservativeMomentumEquation_iff_ConvectiveMomentumEquation d data hConservative.1
      hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mp
      hConservative.2
  · intro hConvective
    refine ⟨hConvective.1, ?_⟩
    exact (ConservativeMomentumEquation_iff_ConvectiveMomentumEquation d data hConvective.1
      hRhoTime hVelocityTime hMomentumDensity hVelocitySpace).mpr
      hConvective.2

end NavierStokes
end FluidDynamics
