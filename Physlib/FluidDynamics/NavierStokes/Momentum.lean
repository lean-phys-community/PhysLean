/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.NavierStokes.Continuity
public import Physlib.SpaceAndTime.Space.Derivatives.MatrixDiv
/-!

# The Navier-Stokes momentum equations

## i. Overview

This module defines the conservative and convective momentum equations for a fluid with
stress and body-force fields. The stress tensor is left as an input field, so this is the
balance-law layer before specializing to a Newtonian stress law.

## ii. Key results

- `momentumDensity` : The vector momentum density `rho u`.
- `momentumFlux` : The convective momentum flux `rho u ⊗ u`.
- `ConservativeMomentumEquation` : Conservation of momentum using `Space.matrixDiv`.
- `convectiveTerm` : The nonlinear transport term `(u · ∇)u`.
- `materialAcceleration` : The material acceleration `∂ₜ u + (u · ∇)u`.
- `ConvectiveMomentumEquation` : The momentum equation in convective form.
- `ConservativeMomentumEquation_iff_ConvectiveMomentumEquation` : Equivalence of the two
  momentum equations when continuity holds and the fields are differentiable.

## iii. Table of contents

- A. Momentum fields
- B. Conservative momentum equation
- C. Convective momentum equation
- D. Equivalence of conservative and convective momentum

## iv. References

-/

@[expose] public section

open Space
open Time

namespace FluidDynamics
namespace NavierStokes

/-!

## A. Momentum fields

-/

/-- The momentum density `rho u`. -/
def momentumDensity (d : ℕ) (fluid : FluidState d) : MomentumDensityField d :=
  fun time position => fluid.rho time position • fluid.velocity time position

/-- The convective momentum flux `rho u ⊗ u`. -/
def momentumFlux (d : ℕ) (fluid : FluidState d) :
    Time → Space d → Matrix (Fin d) (Fin d) ℝ :=
  fun time position =>
    fluid.rho time position • Matrix.vecMulVec
      (fun i => fluid.velocity time position i) (fun j => fluid.velocity time position j)

/-!

## B. Conservative momentum equation

-/

/-- Conservation of momentum in conservative matrix-divergence form.

The equation is

`partial_t (rho u) + matrixDiv (rho u ⊗ u) = matrixDiv sigma + rho f`.

Here `stress` is intentionally not yet specialized to a Newtonian stress law.
-/
def ConservativeMomentumEquation (d : ℕ) (data : MomentumBalanceFields d) : Prop :=
  ∀ time position,
    ∂ₜ (fun time' => momentumDensity d data.toFluidState time' position) time +
        matrixDiv d (momentumFlux d data.toFluidState time) position =
      matrixDiv d (data.stress time) position +
        data.rho time position • data.bodyForce time position

/-!

## C. Convective momentum equation

-/

/-- The nonlinear transport term `(u · ∇)u`. -/
noncomputable def convectiveTerm (d : ℕ) (velocity : VelocityField d) : VectorField d :=
  fun time position => ∑ j, velocity time position j • ∂[j] (velocity time) position

/-- The material acceleration `∂ₜ u + (u · ∇)u`. -/
noncomputable def materialAcceleration (d : ℕ) (velocity : VelocityField d) : VectorField d :=
  fun time position =>
    ∂ₜ (fun time' => velocity time' position) time +
      convectiveTerm d velocity time position

/-- Conservation of momentum in convective form.

The equation is

`rho (partial_t u + (u · ∇)u) = matrixDiv sigma + rho f`.

Here `stress` is intentionally not yet specialized to a Newtonian stress law.
-/
def ConvectiveMomentumEquation (d : ℕ) (data : MomentumBalanceFields d) : Prop :=
  ∀ time position,
    data.rho time position • materialAcceleration d data.velocity time position =
      matrixDiv d (data.stress time) position +
        data.rho time position • data.bodyForce time position

/-!

## D. Equivalence of conservative and convective momentum

-/

/-- The left-hand side of the conservative momentum equation. -/
noncomputable def conservativeMomentumLHS (d : ℕ) (fluid : FluidState d) : VectorField d :=
  fun time position =>
    ∂ₜ (fun time' => momentumDensity d fluid time' position) time +
      matrixDiv d (momentumFlux d fluid time) position

/-- The left-hand side of the convective momentum equation. -/
noncomputable def convectiveMomentumLHS (d : ℕ) (fluid : FluidState d) : VectorField d :=
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

/-- The matrix divergence of `rho u ⊗ u` split into continuity and convective parts. -/
lemma matrixDiv_momentumFlux (d : ℕ) (fluid : FluidState d)
    (time : Time) (position : Space d)
    (hMomentumDensity : Differentiable ℝ (momentumDensity d fluid time))
    (hVelocity : Differentiable ℝ (fluid.velocity time)) :
    matrixDiv d (momentumFlux d fluid time) position =
      (∇ ⬝ momentumDensity d fluid time) position • fluid.velocity time position +
        fluid.rho time position • convectiveTerm d fluid.velocity time position := by
  ext i
  simp [matrixDiv_apply, div, convectiveTerm, smul_eq_mul]
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
  rw [matrixDiv_momentumFlux d fluid time position hMomentumDensity hVelocitySpace]
  ext i
  simp [materialAcceleration, convectiveTerm, div, momentumDensity, smul_eq_mul]
  ring_nf

/-- The conservative and convective momentum equations are equivalent when the continuity
equation holds.

The differentiability assumptions are exactly the product-rule assumptions used to rewrite
`partial_t (rho u)` and `matrixDiv (rho u ⊗ u)`.
-/
theorem ConservativeMomentumEquation_iff_ConvectiveMomentumEquation
    (d : ℕ) (data : MomentumBalanceFields d)
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
      matrixDiv d (data.stress time) position +
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
      matrixDiv d (data.stress time) position +
        data.rho time position • data.bodyForce time position
    rw [hLhs']
    exact hConvective time position

end NavierStokes
end FluidDynamics
