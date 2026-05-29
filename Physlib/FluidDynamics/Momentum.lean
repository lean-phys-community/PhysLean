/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.Continuity
public import Physlib.SpaceAndTime.Space.Derivatives.MatrixDiv
/-!

# Momentum fields for fluid flows

## i. Overview

This module defines the generic momentum fields and conservative/convective momentum left-hand
sides for fluid flow. The definitions do not choose a particular force law or stress model, so
they can be reused by Navier-Stokes, Euler, and related systems.

## ii. Key results

- `momentumDensity` : The vector momentum density `rho u`.
- `momentumFlux` : The convective momentum flux `rho u ⊗ u`.
- `convectiveTerm` : The nonlinear transport term `(u · ∇)u`.
- `materialAcceleration` : The material acceleration `∂ₜ u + (u · ∇)u`.
- `conservativeMomentumLHS` : The conservative momentum-balance left-hand side.
- `convectiveMomentumLHS` : The convective momentum-balance left-hand side.
- `conservativeMomentumLHS_eq_convectiveMomentumLHS_add_continuityResidual_smul` : The bridge
  between conservative and convective momentum forms.

## iii. Table of contents

- A. Momentum fields
- B. Conservative and convective left-hand sides
- C. Equivalence of conservative and convective momentum left-hand sides

## iv. References

-/

@[expose] public section

open Space
open Time

namespace FluidDynamics

/-!

## A. Momentum fields

-/

/-- The momentum density `rho u`. -/
def momentumDensity (d : ℕ) (fluid : FluidFlow d) : MomentumDensityField d :=
  fun t x => fluid.rho t x • fluid.velocity t x

/-- The convective momentum flux `rho u ⊗ u`. -/
def momentumFlux (d : ℕ) (fluid : FluidFlow d) : Time → Space d → Matrix (Fin d) (Fin d) ℝ :=
  fun t x =>
    fluid.rho t x • Matrix.vecMulVec (fun i => fluid.velocity t x i)
      (fun j => fluid.velocity t x j)

/-- The nonlinear transport term `(u · ∇)u`. -/
noncomputable def convectiveTerm (d : ℕ) (fluid : FluidFlow d) : VectorField d :=
  fun t x => ∑ j, fluid.velocity t x j • ∂[j] (fluid.velocity t) x

/-- The material acceleration `∂ₜ u + (u · ∇)u`. -/
noncomputable def materialAcceleration (d : ℕ) (fluid : FluidFlow d) : VectorField d :=
  fun t x => ∂ₜ (fluid.velocity · x) t + convectiveTerm d fluid t x

/-!

## B. Conservative and convective left-hand sides

-/

/-- The left-hand side of the conservative momentum equation. -/
noncomputable def conservativeMomentumLHS (d : ℕ) (fluid : FluidFlow d) : VectorField d :=
  fun t x => ∂ₜ (momentumDensity d fluid · x) t + matrixDiv d (momentumFlux d fluid t) x

/-- The left-hand side of the convective momentum equation. -/
noncomputable def convectiveMomentumLHS (d : ℕ) (fluid : FluidFlow d) : VectorField d :=
  fun t x => fluid.rho t x • materialAcceleration d fluid t x

/-!

## C. Equivalence of conservative and convective momentum left-hand sides

-/

/-- Product rule for the time derivative of a scalar field times a velocity field. -/
lemma timeDeriv_smul_velocity (d : ℕ) (rhoAtPosition : Time → ℝ)
    (velocityAtPosition : Time → EuclideanSpace ℝ (Fin d)) (t : Time)
    (hRho : DifferentiableAt ℝ rhoAtPosition t)
    (hVelocity : DifferentiableAt ℝ velocityAtPosition t) :
    ∂ₜ (fun t' => rhoAtPosition t' • velocityAtPosition t') t =
      rhoAtPosition t • ∂ₜ velocityAtPosition t + ∂ₜ rhoAtPosition t • velocityAtPosition t := by
  rw [Time.deriv_eq, Time.deriv_eq, Time.deriv_eq]
  change (fderiv ℝ (rhoAtPosition • velocityAtPosition) t) 1 =
    rhoAtPosition t • (fderiv ℝ velocityAtPosition t) 1 +
      (fderiv ℝ rhoAtPosition t) 1 • velocityAtPosition t
  rw [fderiv_smul hRho hVelocity]
  rfl

/-- Product rule for the time derivative of the momentum density `rho u`. -/
lemma timeDeriv_momentumDensity (d : ℕ) (fluid : FluidFlow d)
    (t : Time) (x : Space d)
    (hRho : DifferentiableAt ℝ (fluid.rho · x) t)
    (hVelocity : DifferentiableAt ℝ (fluid.velocity · x) t) :
    ∂ₜ (momentumDensity d fluid · x) t =
      fluid.rho t x • ∂ₜ (fluid.velocity · x) t + ∂ₜ (fluid.rho · x) t • fluid.velocity t x := by
  simpa [momentumDensity] using
    timeDeriv_smul_velocity d (fluid.rho · x) (fluid.velocity · x) t hRho hVelocity

/-- Product rule for one spatial derivative of one component of `rho u ⊗ u`. -/
lemma spaceDeriv_momentumFlux_component (d : ℕ) (fluid : FluidFlow d)
    (t : Time) (x : Space d) (i j : Fin d)
    (hMomentumDensity : Differentiable ℝ (momentumDensity d fluid t))
    (hVelocity : Differentiable ℝ (fluid.velocity t)) :
    ∂[j] (fun x' => momentumFlux d fluid t x' i j) x =
      fluid.velocity t x i • ∂[j] (fun x' => momentumDensity d fluid t x' j) x +
      ∂[j] (fun x' => fluid.velocity t x' i) x • momentumDensity d fluid t x j := by
  have hProduct := Space.deriv_smul (u := j) (x := x)
    (c := fun x' => fluid.velocity t x' i)
    (f := fun x' => momentumDensity d fluid t x' j)
    ((differentiable_euclidean.mp hVelocity i).differentiableAt)
    ((differentiable_euclidean.mp hMomentumDensity j).differentiableAt)
  rw [← hProduct]
  congr
  funext x'
  simp [momentumFlux, momentumDensity, Matrix.vecMulVec_apply, mul_left_comm]

/-- The matrix divergence of `rho u ⊗ u` split into continuity and convective parts. -/
lemma matrixDiv_momentumFlux (d : ℕ) (fluid : FluidFlow d)
    (t : Time) (x : Space d)
    (hMomentumDensity : Differentiable ℝ (momentumDensity d fluid t))
    (hVelocity : Differentiable ℝ (fluid.velocity t)) :
    matrixDiv d (momentumFlux d fluid t) x =
      (∇ ⬝ momentumDensity d fluid t) x • fluid.velocity t x +
        fluid.rho t x • convectiveTerm d fluid t x := by
  ext i
  simp [matrixDiv_apply, div, convectiveTerm, smul_eq_mul]
  change (∑ j, ∂[j] (fun x' => momentumFlux d fluid t x' i j) x) =
    (∑ j, ∂[j] (fun x' => momentumDensity d fluid t x' j) x) * fluid.velocity t x i +
      fluid.rho t x * (∑ j, fluid.velocity t x j * ∂[j] (fluid.velocity t) x i)
  calc
    (∑ j, ∂[j] (fun x' => momentumFlux d fluid t x' i j) x)
        = ∑ j,
            (fluid.velocity t x i * ∂[j] (fun x' => momentumDensity d fluid t x' j) x +
              ∂[j] (fun x' => fluid.velocity t x' i) x * momentumDensity d fluid t x j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [spaceDeriv_momentumFlux_component d fluid t x i j
            hMomentumDensity hVelocity]
          simp [smul_eq_mul]
    _ = fluid.velocity t x i * (∑ j, ∂[j] (fun x' => momentumDensity d fluid t x' j) x) +
        fluid.rho t x * (∑ j, fluid.velocity t x j * ∂[j] (fluid.velocity t) x i) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Space.deriv_euclid (ν := j) (μ := i) (f := fluid.velocity t)
              hVelocity x]
            simp [momentumDensity, mul_comm, mul_assoc]
    _ = (∑ j, ∂[j] (fun x' => momentumDensity d fluid t x' j) x) * fluid.velocity t x i +
        fluid.rho t x * (∑ j, fluid.velocity t x j * ∂[j] (fluid.velocity t) x i) := by
          ring

/-- The algebraic bridge between conservative and convective momentum.

The conservative momentum left-hand side equals the convective momentum left-hand side plus
the continuity residual times the velocity field.
-/
lemma conservativeMomentumLHS_eq_convectiveMomentumLHS_add_continuityResidual_smul
    (d : ℕ) (fluid : FluidFlow d)
    (t : Time) (x : Space d)
    (hRhoTime : DifferentiableAt ℝ (fluid.rho · x) t)
    (hVelocityTime : DifferentiableAt ℝ (fluid.velocity · x) t)
    (hMomentumDensity : Differentiable ℝ (momentumDensity d fluid t))
    (hVelocitySpace : Differentiable ℝ (fluid.velocity t)) :
    conservativeMomentumLHS d fluid t x =
      convectiveMomentumLHS d fluid t x + continuityResidual d fluid t x • fluid.velocity t x := by
  rw [conservativeMomentumLHS, convectiveMomentumLHS, continuityResidual]
  rw [timeDeriv_momentumDensity d fluid t x hRhoTime hVelocityTime]
  rw [matrixDiv_momentumFlux d fluid t x hMomentumDensity hVelocitySpace]
  ext i
  simp [materialAcceleration, convectiveTerm, div, momentumDensity, smul_eq_mul]
  ring_nf

end FluidDynamics
