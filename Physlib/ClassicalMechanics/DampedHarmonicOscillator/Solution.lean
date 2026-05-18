/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-!

# Solutions to the damped harmonic oscillator

## i. Overview

In this module we define the regime-specific solutions to the damped harmonic oscillator
and prove that they satisfy the equation of motion. The formulas are split into an
exponential decay factor and a regime-specific base trajectory: trigonometric for the
underdamped case, polynomial for the critically damped case, and hyperbolic for the
overdamped case.

## ii. Key results

- `InitialConditions` is a structure for the initial position and velocity.
- `trajectoryUnderdamped`, `trajectoryCriticallyDamped`, and `trajectoryOverdamped` are the
  explicit regime-specific trajectories.
- `trajectory_underdamped_equationOfMotion`,
  `trajectory_criticallydamped_equationOfMotion`, and
  `trajectory_overdamped_equationOfMotion` prove that those trajectories satisfy the equation
  of motion in their corresponding damping regimes.

## iii. Table of contents

- A. The initial conditions
- B. Trajectories associated with the initial conditions
  - B.1. Explicit regime-specific trajectories
  - B.2. Shared calculus lemmas
  - B.3. Derivatives of the base trajectories
- C. Trajectories and equation of motion
  - C.1. Uniqueness of the solutions

## iv. References

References for the damped harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 76, section 25.
- Goldstein, Classical Mechanics, Chapter 2.

-/

@[expose] public section

namespace ClassicalMechanics
open Real
open Time
open ContDiff

namespace DampedHarmonicOscillator

variable (S : DampedHarmonicOscillator)

/-!

## A. The initial conditions

We define the type of initial conditions for the damped harmonic oscillator. The initial
conditions are the position and velocity at time `0`.

-/

/-- The initial conditions for the damped harmonic oscillator, specified by an initial
position and an initial velocity. -/
@[ext]
structure InitialConditions where
  /-- The initial position of the damped harmonic oscillator. -/
  x₀ : EuclideanSpace ℝ (Fin 1)
  /-- The initial velocity of the damped harmonic oscillator. -/
  v₀ : EuclideanSpace ℝ (Fin 1)

/-!

## B. Trajectories associated with the initial conditions

For each damping regime, we give an explicit formula for the trajectory with the specified
initial conditions.

### B.1. Explicit regime-specific trajectories

-/

/-- The oscillatory part of the underdamped trajectory before exponential decay. -/
noncomputable def underdampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cos (S.underdampedAngularFrequency * t) • IC.x₀
    + (sin (S.underdampedAngularFrequency * t)/S.underdampedAngularFrequency) •
      (IC.v₀ + S.decayRate • IC.x₀)

/-- Given initial conditions, the solution in the underdamped regime. -/
noncomputable def trajectoryUnderdamped
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  exp (-S.decayRate * t) • S.underdampedBase IC t

/-- The polynomial part of the critically damped trajectory before exponential decay. -/
noncomputable def criticallyDampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  IC.x₀ + (t : ℝ) • (IC.v₀ + S.decayRate • IC.x₀)

/-- Given initial conditions, the solution in the critically damped regime. -/
noncomputable def trajectoryCriticallyDamped
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  exp (-S.decayRate * t) • S.criticallyDampedBase IC t

/-- The hyperbolic part of the overdamped trajectory before exponential decay. -/
noncomputable def overdampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cosh (S.overdampedSplitRate * t) • IC.x₀
      + (sinh (S.overdampedSplitRate * t) / S.overdampedSplitRate) •
        (IC.v₀ + S.decayRate • IC.x₀)

/-- Given initial conditions, the solution in the overdamped regime. -/
noncomputable def trajectoryOverdamped
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  exp (-S.decayRate * t) • S.overdampedBase IC t

/-!

### B.2. Shared calculus lemmas

The three solution formulas all have the form `exp (-a * t) • y t`. The following private
lemmas compute the first and second derivatives of that expression and package the common
equation-of-motion argument.

-/

private lemma exp_decay_smul_velocity
    (a : ℝ) (y : Time → EuclideanSpace ℝ (Fin 1)) (hy : Differentiable ℝ y) :
    ∂ₜ (fun t : Time => exp (-a * t.val) • y t) =
      fun t : Time => exp (-a * t.val) • (∂ₜ y t - a • y t) := by
  funext t
  rw [Time.deriv]
  rw [fderiv_fun_smul (by fun_prop) (hy t)]
  rw [fderiv_exp (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    fderiv_fun_neg, fderiv_fun_const, Pi.zero_apply, Time.fderiv_val,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [← Time.deriv_eq]
  simp [smul_sub, smul_smul]
  module

private lemma exp_decay_smul_acceleration
    (a μ : ℝ) (y : Time → EuclideanSpace ℝ (Fin 1))
    (hy : Differentiable ℝ y) (hdy : Differentiable ℝ (∂ₜ y))
    (hy'' : ∂ₜ (∂ₜ y) = fun t => μ • y t) :
    ∂ₜ (∂ₜ (fun t : Time => exp (-a * t.val) • y t)) =
      fun t : Time => exp (-a * t.val) •
        (μ • y t - (2 * a) • ∂ₜ y t + a^2 • y t) := by
  rw [exp_decay_smul_velocity a y hy]
  funext t
  rw [Time.deriv]
  rw [fderiv_fun_smul (by fun_prop) (by fun_prop)]
  rw [fderiv_exp (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
  rw [fderiv_fun_sub (hdy t) (by fun_prop)]
  rw [fderiv_fun_const_smul (hy t)]
  have hy''_t := congrFun hy'' t
  rw [Time.deriv] at hy''_t
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, fderiv_fun_neg, fderiv_fun_const,
    Pi.zero_apply, Time.fderiv_val, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [hy''_t, ← Time.deriv_eq]
  simp [smul_add, smul_sub, smul_smul]
  module

private lemma exp_decay_smul_equationOfMotion
    (a μ : ℝ) (y : Time → EuclideanSpace ℝ (Fin 1))
    (hy : Differentiable ℝ y) (hdy : Differentiable ℝ (∂ₜ y))
    (hy'' : ∂ₜ (∂ₜ y) = fun t => μ • y t)
    (hγ : S.γ = 2 * S.m * a) (hk : S.k = S.m * (a^2 - μ)) :
    S.EquationOfMotion (fun t : Time => exp (-a * t.val) • y t) := by
  intro t
  rw [exp_decay_smul_acceleration a μ y hy hdy hy'']
  rw [exp_decay_smul_velocity a y hy]
  rw [hγ, hk]
  simp [smul_add, smul_sub, smul_smul]
  module

/-!

### B.3. Derivatives of the base trajectories

The remaining private lemmas compute the velocity and acceleration of the trigonometric,
polynomial, and hyperbolic base trajectories before the exponential decay factor is applied.

-/

private lemma criticallyDampedBase_velocity (IC : InitialConditions) :
    ∂ₜ (S.criticallyDampedBase IC) =
      fun _ : Time => IC.v₀ + S.decayRate • IC.x₀ := by
  funext t
  change ∂ₜ (fun t : Time =>
    IC.x₀ + t.val • (IC.v₀ + S.decayRate • IC.x₀)) t = _
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_fun_const]
  rw [fderiv_smul_const (by fun_prop)]
  simp

private lemma criticallyDampedBase_acceleration (IC : InitialConditions) :
    ∂ₜ (∂ₜ (S.criticallyDampedBase IC)) =
      fun _ => (0 : EuclideanSpace ℝ (Fin 1)) := by
  rw [criticallyDampedBase_velocity]
  funext t
  simp

private lemma underdamped_base_velocity (IC : InitialConditions) (hS : S.IsUnderdamped) :
    ∂ₜ (fun t : Time =>
      cos (S.underdampedAngularFrequency * t.val) • IC.x₀ +
        (sin (S.underdampedAngularFrequency * t.val) / S.underdampedAngularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) =
    fun t : Time =>
      (-S.underdampedAngularFrequency * sin (S.underdampedAngularFrequency * t.val)) • IC.x₀ +
        cos (S.underdampedAngularFrequency * t.val) •
          (IC.v₀ + S.decayRate • IC.x₀) := by
  funext t
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  have hΩ : S.underdampedAngularFrequency ≠ 0 := S.underdampedAngularFrequency_ne_zero hS
  have hcos :
      (fderiv ℝ (fun y : Time => cos (S.underdampedAngularFrequency * y.val)) t) 1 =
        -S.underdampedAngularFrequency *
          sin (S.underdampedAngularFrequency * t.val) := by
    rw [fderiv_cos (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [mul_comm]
  have hsin :
      (fderiv ℝ (fun y : Time =>
          sin (S.underdampedAngularFrequency * y.val) /
            S.underdampedAngularFrequency) t) 1 =
        cos (S.underdampedAngularFrequency * t.val) := by
    have hscale :
        fderiv ℝ (fun y : Time =>
            sin (S.underdampedAngularFrequency * y.val) /
              S.underdampedAngularFrequency) t =
          (1 / S.underdampedAngularFrequency) •
            fderiv ℝ (fun y : Time =>
              sin (S.underdampedAngularFrequency * y.val)) t := by
      rw [← fderiv_mul_const]
      congr
      funext y
      field_simp [hΩ]
      ring_nf
      fun_prop
    rw [hscale, fderiv_sin (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [hΩ, mul_comm]
  simp [hcos, hsin]

private lemma underdamped_base_acceleration (IC : InitialConditions) (hS : S.IsUnderdamped) :
    ∂ₜ (∂ₜ (fun t : Time =>
      cos (S.underdampedAngularFrequency * t.val) • IC.x₀ +
        (sin (S.underdampedAngularFrequency * t.val) / S.underdampedAngularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀))) =
    fun t : Time => -S.underdampedAngularFrequency^2 •
      (cos (S.underdampedAngularFrequency * t.val) • IC.x₀ +
        (sin (S.underdampedAngularFrequency * t.val) / S.underdampedAngularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) := by
  funext t
  rw [S.underdamped_base_velocity IC hS]
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  have hΩ : S.underdampedAngularFrequency ≠ 0 := S.underdampedAngularFrequency_ne_zero hS
  have hsin :
      (fderiv ℝ (fun y : Time =>
        S.underdampedAngularFrequency * sin (S.underdampedAngularFrequency * y.val)) t) 1 =
      S.underdampedAngularFrequency^2 * cos (S.underdampedAngularFrequency * t.val) := by
    rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
    rw [fderiv_sin (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [pow_two, mul_comm, mul_assoc]
  have hcos :
      (fderiv ℝ (fun y : Time => cos (S.underdampedAngularFrequency * y.val)) t) 1 =
      -S.underdampedAngularFrequency * sin (S.underdampedAngularFrequency * t.val) := by
    rw [fderiv_cos (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [mul_comm]
  simp [hsin, hcos, smul_add, smul_smul]
  field_simp [hΩ]

private lemma overdamped_base_velocity (IC : InitialConditions) (hS : S.IsOverdamped) :
    ∂ₜ (fun t : Time =>
      cosh (S.overdampedSplitRate * t.val) • IC.x₀ +
        (sinh (S.overdampedSplitRate * t.val) / S.overdampedSplitRate) •
          (IC.v₀ + S.decayRate • IC.x₀)) =
    fun t : Time =>
      (S.overdampedSplitRate * sinh (S.overdampedSplitRate * t.val)) • IC.x₀ +
        cosh (S.overdampedSplitRate * t.val) •
          (IC.v₀ + S.decayRate • IC.x₀) := by
  funext t
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  have hLambda : S.overdampedSplitRate ≠ 0 := S.overdampedSplitRate_ne_zero hS
  have hcosh :
      (fderiv ℝ (fun y : Time => cosh (S.overdampedSplitRate * y.val)) t) 1 =
        S.overdampedSplitRate * sinh (S.overdampedSplitRate * t.val) := by
    rw [fderiv_cosh (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [mul_comm]
  have hsinh :
      (fderiv ℝ (fun y : Time =>
          sinh (S.overdampedSplitRate * y.val) / S.overdampedSplitRate) t) 1 =
        cosh (S.overdampedSplitRate * t.val) := by
    have hscale :
        fderiv ℝ (fun y : Time =>
            sinh (S.overdampedSplitRate * y.val) / S.overdampedSplitRate) t =
          (1 / S.overdampedSplitRate) •
            fderiv ℝ (fun y : Time => sinh (S.overdampedSplitRate * y.val)) t := by
      rw [← fderiv_mul_const]
      congr
      funext y
      field_simp [hLambda]
      ring_nf
      fun_prop
    rw [hscale, fderiv_sinh (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [hLambda, mul_comm]
  simp [hcosh, hsinh]

private lemma overdamped_base_acceleration (IC : InitialConditions) (hS : S.IsOverdamped) :
    ∂ₜ (∂ₜ (fun t : Time =>
      cosh (S.overdampedSplitRate * t.val) • IC.x₀ +
        (sinh (S.overdampedSplitRate * t.val) / S.overdampedSplitRate) •
          (IC.v₀ + S.decayRate • IC.x₀))) =
    fun t : Time => S.overdampedSplitRate^2 •
      (cosh (S.overdampedSplitRate * t.val) • IC.x₀ +
        (sinh (S.overdampedSplitRate * t.val) / S.overdampedSplitRate) •
          (IC.v₀ + S.decayRate • IC.x₀)) := by
  funext t
  rw [S.overdamped_base_velocity IC hS]
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  have hLambda : S.overdampedSplitRate ≠ 0 := S.overdampedSplitRate_ne_zero hS
  have hsinh :
      (fderiv ℝ (fun y : Time =>
        S.overdampedSplitRate * sinh (S.overdampedSplitRate * y.val)) t) 1 =
      S.overdampedSplitRate^2 * cosh (S.overdampedSplitRate * t.val) := by
    rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
    rw [fderiv_sinh (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [pow_two, mul_comm, mul_assoc]
  have hcosh :
      (fderiv ℝ (fun y : Time => cosh (S.overdampedSplitRate * y.val)) t) 1 =
      S.overdampedSplitRate * sinh (S.overdampedSplitRate * t.val) := by
    rw [fderiv_cosh (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [mul_comm]
  simp [hsinh, hcosh, smul_add, smul_smul]
  field_simp [hLambda]

/-!
## C. Trajectories and equation of motion

The regime-specific trajectories satisfy the equation of motion for the damped harmonic
oscillator.

-/

/-- The critically damped trajectory satisfies the damped equation of motion. -/
lemma trajectory_criticallydamped_equationOfMotion (IC : InitialConditions)
    (hS : S.IsCriticallyDamped) :
    S.EquationOfMotion (S.trajectoryCriticallyDamped IC) := by
  change S.EquationOfMotion
    (fun t : Time => exp (-S.decayRate * t.val) • S.criticallyDampedBase IC t)
  have hγ : S.γ = 2 * S.m * S.decayRate := S.gamma_eq_two_mul_m_mul_decayRate
  have hk : S.k = S.m * (S.decayRate^2 - 0) := by
    simpa [sub_zero] using S.k_eq_m_mul_decayRate_sq_of_criticallyDamped hS
  have hbase :
      ∂ₜ (∂ₜ (S.criticallyDampedBase IC)) =
        fun t => (0 : ℝ) • S.criticallyDampedBase IC t := by
    simpa using S.criticallyDampedBase_acceleration IC
  exact S.exp_decay_smul_equationOfMotion S.decayRate 0 (S.criticallyDampedBase IC)
    (by
      change Differentiable ℝ (fun t : Time =>
        IC.x₀ + t.val • (IC.v₀ + S.decayRate • IC.x₀))
      fun_prop)
    (by
      rw [S.criticallyDampedBase_velocity IC]
      fun_prop)
    hbase hγ hk

/-- The underdamped trajectory satisfies the damped equation of motion. -/
lemma trajectory_underdamped_equationOfMotion (IC : InitialConditions)
    (hS : S.IsUnderdamped) :
    S.EquationOfMotion (S.trajectoryUnderdamped IC) := by
  change S.EquationOfMotion
    (fun t : Time => exp (-S.decayRate * t.val) • S.underdampedBase IC t)
  have hγ : S.γ = 2 * S.m * S.decayRate := S.gamma_eq_two_mul_m_mul_decayRate
  have hk : S.k = S.m * (S.decayRate^2 - (-S.underdampedAngularFrequency^2)) := by
    rw [S.k_eq_m_mul_ω_sq, S.underdampedAngularFrequency_sq hS]
    ring
  have hbase :
      ∂ₜ (∂ₜ (S.underdampedBase IC)) =
        fun t => (-S.underdampedAngularFrequency^2) • S.underdampedBase IC t := by
    change ∂ₜ (∂ₜ (fun t : Time =>
        cos (S.underdampedAngularFrequency * t.val) • IC.x₀ +
          (sin (S.underdampedAngularFrequency * t.val) / S.underdampedAngularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))) =
      fun t => -S.underdampedAngularFrequency^2 •
        (cos (S.underdampedAngularFrequency * t.val) • IC.x₀ +
          (sin (S.underdampedAngularFrequency * t.val) / S.underdampedAngularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))
    exact S.underdamped_base_acceleration IC hS
  exact S.exp_decay_smul_equationOfMotion S.decayRate
    (-S.underdampedAngularFrequency^2) (S.underdampedBase IC)
    (by
      change Differentiable ℝ (fun t : Time =>
        cos (S.underdampedAngularFrequency * t.val) • IC.x₀ +
          (sin (S.underdampedAngularFrequency * t.val) / S.underdampedAngularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))
      fun_prop)
    (by
      change Differentiable ℝ (∂ₜ (fun t : Time =>
        cos (S.underdampedAngularFrequency * t.val) • IC.x₀ +
          (sin (S.underdampedAngularFrequency * t.val) / S.underdampedAngularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀)))
      rw [S.underdamped_base_velocity IC hS]
      fun_prop)
    hbase hγ hk

/-- The overdamped trajectory satisfies the damped equation of motion. -/
lemma trajectory_overdamped_equationOfMotion (IC : InitialConditions)
    (hS : S.IsOverdamped) :
    S.EquationOfMotion (S.trajectoryOverdamped IC) := by
  change S.EquationOfMotion
    (fun t : Time => exp (-S.decayRate * t.val) • S.overdampedBase IC t)
  have hγ : S.γ = 2 * S.m * S.decayRate := S.gamma_eq_two_mul_m_mul_decayRate
  have hk : S.k = S.m * (S.decayRate^2 - S.overdampedSplitRate^2) := by
    rw [S.k_eq_m_mul_ω_sq, S.overdampedSplitRate_sq hS]
    ring
  have hbase :
      ∂ₜ (∂ₜ (S.overdampedBase IC)) =
        fun t => S.overdampedSplitRate^2 • S.overdampedBase IC t := by
    change ∂ₜ (∂ₜ (fun t : Time =>
        cosh (S.overdampedSplitRate * t.val) • IC.x₀ +
          (sinh (S.overdampedSplitRate * t.val) / S.overdampedSplitRate) •
            (IC.v₀ + S.decayRate • IC.x₀))) =
      fun t => S.overdampedSplitRate^2 •
        (cosh (S.overdampedSplitRate * t.val) • IC.x₀ +
          (sinh (S.overdampedSplitRate * t.val) / S.overdampedSplitRate) •
            (IC.v₀ + S.decayRate • IC.x₀))
    exact S.overdamped_base_acceleration IC hS
  exact S.exp_decay_smul_equationOfMotion S.decayRate (S.overdampedSplitRate^2)
    (S.overdampedBase IC)
    (by
      change Differentiable ℝ (fun t : Time =>
        cosh (S.overdampedSplitRate * t.val) • IC.x₀ +
          (sinh (S.overdampedSplitRate * t.val) / S.overdampedSplitRate) •
            (IC.v₀ + S.decayRate • IC.x₀))
      fun_prop)
    (by
      change Differentiable ℝ (∂ₜ (fun t : Time =>
        cosh (S.overdampedSplitRate * t.val) • IC.x₀ +
          (sinh (S.overdampedSplitRate * t.val) / S.overdampedSplitRate) •
            (IC.v₀ + S.decayRate • IC.x₀)))
      rw [S.overdamped_base_velocity IC hS]
      fun_prop)
    hbase hγ hk

/-!

### C.1. Uniqueness of the solutions

Future work: prove that, in each damping regime, the corresponding explicit trajectory is
the unique solution of the damped equation of motion with the given initial conditions.

-/

/- The uniqueness theorem should compare an arbitrary smooth solution with the appropriate
regime-specific trajectory and use the matching initial position and velocity at time `0`. -/

end DampedHarmonicOscillator

end ClassicalMechanics
