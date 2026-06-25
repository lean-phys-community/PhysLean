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

In this module we define the solution to the damped harmonic oscillator for given initial
conditions and prove that it satisfies the equation of motion. The solution selects the
appropriate closed form from the sign of the discriminant: trigonometric for the underdamped
case, polynomial for the critically damped case, and hyperbolic for the overdamped case.

## ii. Key results

- `InitialConditions` is a structure for the initial position and velocity.
- `trajectory` selects the appropriate regime-specific trajectory from the sign of the
  discriminant.
- `trajectory_equationOfMotion_of_underdamped`,
  `trajectory_equationOfMotion_of_criticallyDamped`, and
  `trajectory_equationOfMotion_of_overdamped` prove the selected trajectory satisfies the
  equation of motion in each damping regime.
- `trajectory_equationOfMotion` proves that the selected trajectory satisfies the equation
  of motion.

## iii. Table of contents

- A. The initial conditions
- B. Trajectories associated with the initial conditions
  - B.1. Regime-specific base trajectories
  - B.2. The selected trajectory
  - B.3. Shared calculus lemmas
  - B.4. Derivatives of the base trajectories
- C. Trajectories and equation of motion
  - C.1. The selected trajectory satisfies the equation of motion
  - C.2. Uniqueness of the solutions

## iv. References

References for the damped harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 76, section 25.
- Goldstein, Classical Mechanics, Chapter 2.

## v. TODOs

-/
TODO "Prove that the selected trajectory is the unique solution of the equation of motion with
the given initial conditions."

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

### B.1. Regime-specific base trajectories

-/

/-- The oscillatory part of the underdamped trajectory before exponential decay. -/
noncomputable def underdampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cos (S.angularFrequency * t) • IC.x₀
    + (sin (S.angularFrequency * t)/S.angularFrequency) •
      (IC.v₀ + S.decayRate • IC.x₀)

/-- The polynomial part of the critically damped trajectory before exponential decay. -/
noncomputable def criticallyDampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  IC.x₀ + (t : ℝ) • (IC.v₀ + S.decayRate • IC.x₀)

/-- The hyperbolic part of the overdamped trajectory before exponential decay. -/
noncomputable def overdampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cosh (S.angularFrequency * t) • IC.x₀
      + (sinh (S.angularFrequency * t) / S.angularFrequency) •
        (IC.v₀ + S.decayRate • IC.x₀)

/-!

### B.2. The selected trajectory

-/

/-- Given initial conditions, the solution selected from the damping regime of the
oscillator. -/
noncomputable def trajectory
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := by
  classical
  exact
    if S.IsUnderdamped then
      fun t : Time => exp (-S.decayRate * t) • S.underdampedBase IC t
    else if S.IsCriticallyDamped then
      fun t : Time => exp (-S.decayRate * t) • S.criticallyDampedBase IC t
    else
      fun t : Time => exp (-S.decayRate * t) • S.overdampedBase IC t

/-- In the underdamped regime, the selected trajectory uses the trigonometric base. -/
lemma trajectory_eq_of_underdamped (IC : InitialConditions) (hS : S.IsUnderdamped) :
    S.trajectory IC =
      fun t : Time => exp (-S.decayRate * t) • S.underdampedBase IC t := by
  classical
  simp [trajectory, hS]

/-- In the critically damped regime, the selected trajectory uses the polynomial base. -/
lemma trajectory_eq_of_criticallyDamped (IC : InitialConditions) (hS : S.IsCriticallyDamped) :
    S.trajectory IC =
      fun t : Time => exp (-S.decayRate * t) • S.criticallyDampedBase IC t := by
  classical
  have hnotUnder : ¬ S.IsUnderdamped := by
    intro hUnder
    rw [IsUnderdamped] at hUnder
    rw [IsCriticallyDamped] at hS
    linarith
  simp [trajectory, hnotUnder, hS]

/-- In the overdamped regime, the selected trajectory uses the hyperbolic base. -/
lemma trajectory_eq_of_overdamped (IC : InitialConditions) (hS : S.IsOverdamped) :
    S.trajectory IC =
      fun t : Time => exp (-S.decayRate * t) • S.overdampedBase IC t := by
  classical
  have hnotUnder : ¬ S.IsUnderdamped := by
    intro hUnder
    rw [IsUnderdamped] at hUnder
    rw [IsOverdamped] at hS
    linarith
  have hnotCritical : ¬ S.IsCriticallyDamped := by
    intro hCritical
    rw [IsCriticallyDamped] at hCritical
    rw [IsOverdamped] at hS
    linarith
  simp [trajectory, hnotUnder, hnotCritical]

/-!

### B.3. Shared calculus lemmas

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
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    fderiv_fun_neg, fderiv_fun_const, Pi.zero_apply, Time.fderiv_val,
    _root_.neg_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
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
  simp only [add_apply, _root_.sub_apply,
    ContinuousLinearMap.smulRight_apply, fderiv_fun_neg, fderiv_fun_const,
    Pi.zero_apply, Time.fderiv_val, _root_.neg_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
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

### B.4. Derivatives of the base trajectories

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

private lemma underdampedBase_velocity (IC : InitialConditions) (hS : S.IsUnderdamped) :
    ∂ₜ (fun t : Time =>
      cos (S.angularFrequency * t.val) • IC.x₀ +
        (sin (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) =
    fun t : Time =>
      (-S.angularFrequency * sin (S.angularFrequency * t.val)) • IC.x₀ +
        cos (S.angularFrequency * t.val) •
          (IC.v₀ + S.decayRate • IC.x₀) := by
  funext t
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  have hΩ : S.angularFrequency ≠ 0 := S.angularFrequency_ne_zero_of_underdamped hS
  have hcos :
      (fderiv ℝ (fun y : Time => cos (S.angularFrequency * y.val)) t) 1 =
        -S.angularFrequency *
          sin (S.angularFrequency * t.val) := by
    rw [fderiv_cos (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [mul_comm]
  have hsin :
      (fderiv ℝ (fun y : Time =>
          sin (S.angularFrequency * y.val) /
            S.angularFrequency) t) 1 =
        cos (S.angularFrequency * t.val) := by
    have hscale :
        fderiv ℝ (fun y : Time =>
            sin (S.angularFrequency * y.val) /
              S.angularFrequency) t =
          (1 / S.angularFrequency) •
            fderiv ℝ (fun y : Time =>
              sin (S.angularFrequency * y.val)) t := by
      rw [← fderiv_mul_const]
      congr
      funext y
      field_simp [hΩ]
      ring_nf
      fun_prop
    rw [hscale, fderiv_sin (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [hΩ, mul_comm]
  simp [hcos, hsin]

private lemma underdampedBase_acceleration (IC : InitialConditions) (hS : S.IsUnderdamped) :
    ∂ₜ (∂ₜ (fun t : Time =>
      cos (S.angularFrequency * t.val) • IC.x₀ +
        (sin (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀))) =
    fun t : Time => -S.angularFrequency^2 •
      (cos (S.angularFrequency * t.val) • IC.x₀ +
        (sin (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) := by
  funext t
  rw [S.underdampedBase_velocity IC hS]
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  have hΩ : S.angularFrequency ≠ 0 := S.angularFrequency_ne_zero_of_underdamped hS
  have hsin :
      (fderiv ℝ (fun y : Time =>
        S.angularFrequency * sin (S.angularFrequency * y.val)) t) 1 =
      S.angularFrequency^2 * cos (S.angularFrequency * t.val) := by
    rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
    rw [fderiv_sin (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [pow_two, mul_comm, mul_assoc]
  have hcos :
      (fderiv ℝ (fun y : Time => cos (S.angularFrequency * y.val)) t) 1 =
      -S.angularFrequency * sin (S.angularFrequency * t.val) := by
    rw [fderiv_cos (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [mul_comm]
  simp [hsin, hcos, smul_add, smul_smul]
  field_simp [hΩ]

private lemma overdampedBase_velocity (IC : InitialConditions) (hS : S.IsOverdamped) :
    ∂ₜ (fun t : Time =>
      cosh (S.angularFrequency * t.val) • IC.x₀ +
        (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) =
    fun t : Time =>
      (S.angularFrequency * sinh (S.angularFrequency * t.val)) • IC.x₀ +
        cosh (S.angularFrequency * t.val) •
          (IC.v₀ + S.decayRate • IC.x₀) := by
  funext t
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  have hLambda : S.angularFrequency ≠ 0 := S.angularFrequency_ne_zero_of_overdamped hS
  have hcosh :
      (fderiv ℝ (fun y : Time => cosh (S.angularFrequency * y.val)) t) 1 =
        S.angularFrequency * sinh (S.angularFrequency * t.val) := by
    rw [fderiv_cosh (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [mul_comm]
  have hsinh :
      (fderiv ℝ (fun y : Time =>
          sinh (S.angularFrequency * y.val) / S.angularFrequency) t) 1 =
        cosh (S.angularFrequency * t.val) := by
    have hscale :
        fderiv ℝ (fun y : Time =>
            sinh (S.angularFrequency * y.val) / S.angularFrequency) t =
          (1 / S.angularFrequency) •
            fderiv ℝ (fun y : Time => sinh (S.angularFrequency * y.val)) t := by
      rw [← fderiv_mul_const]
      congr
      funext y
      field_simp [hLambda]
      ring_nf
      fun_prop
    rw [hscale, fderiv_sinh (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [hLambda, mul_comm]
  simp [hcosh, hsinh]

private lemma overdampedBase_acceleration (IC : InitialConditions) (hS : S.IsOverdamped) :
    ∂ₜ (∂ₜ (fun t : Time =>
      cosh (S.angularFrequency * t.val) • IC.x₀ +
        (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀))) =
    fun t : Time => S.angularFrequency^2 •
      (cosh (S.angularFrequency * t.val) • IC.x₀ +
        (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) := by
  funext t
  rw [S.overdampedBase_velocity IC hS]
  rw [Time.deriv]
  rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop)]
  have hLambda : S.angularFrequency ≠ 0 := S.angularFrequency_ne_zero_of_overdamped hS
  have hsinh :
      (fderiv ℝ (fun y : Time =>
        S.angularFrequency * sinh (S.angularFrequency * y.val)) t) 1 =
      S.angularFrequency^2 * cosh (S.angularFrequency * t.val) := by
    rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
    rw [fderiv_sinh (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [pow_two, mul_comm, mul_assoc]
  have hcosh :
      (fderiv ℝ (fun y : Time => cosh (S.angularFrequency * y.val)) t) 1 =
      S.angularFrequency * sinh (S.angularFrequency * t.val) := by
    rw [fderiv_cosh (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [mul_comm]
  simp [hsinh, hcosh, smul_add, smul_smul]
  field_simp [hLambda]

/-!
## C. Trajectories and equation of motion

The regime-specific trajectories satisfy the equation of motion for the damped harmonic
oscillator.

### C.1. The selected trajectory satisfies the equation of motion
-/

/-- In the critically damped regime, the selected trajectory satisfies the damped equation
of motion. -/
lemma trajectory_equationOfMotion_of_criticallyDamped (IC : InitialConditions)
    (hS : S.IsCriticallyDamped) :
    S.EquationOfMotion (S.trajectory IC) := by
  rw [S.trajectory_eq_of_criticallyDamped IC hS]
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

/-- In the underdamped regime, the selected trajectory satisfies the damped equation of
motion. -/
lemma trajectory_equationOfMotion_of_underdamped (IC : InitialConditions)
    (hS : S.IsUnderdamped) :
    S.EquationOfMotion (S.trajectory IC) := by
  rw [S.trajectory_eq_of_underdamped IC hS]
  have hγ : S.γ = 2 * S.m * S.decayRate := S.gamma_eq_two_mul_m_mul_decayRate
  have hk : S.k = S.m * (S.decayRate^2 - (-S.angularFrequency^2)) := by
    rw [S.k_eq_m_mul_ω_sq, S.angularFrequency_sq_of_underdamped hS]
    ring
  have hbase :
      ∂ₜ (∂ₜ (S.underdampedBase IC)) =
        fun t => (-S.angularFrequency^2) • S.underdampedBase IC t := by
    change ∂ₜ (∂ₜ (fun t : Time =>
        cos (S.angularFrequency * t.val) • IC.x₀ +
          (sin (S.angularFrequency * t.val) / S.angularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))) =
      fun t => -S.angularFrequency^2 •
        (cos (S.angularFrequency * t.val) • IC.x₀ +
          (sin (S.angularFrequency * t.val) / S.angularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))
    exact S.underdampedBase_acceleration IC hS
  exact S.exp_decay_smul_equationOfMotion S.decayRate
    (-S.angularFrequency^2) (S.underdampedBase IC)
    (by
      change Differentiable ℝ (fun t : Time =>
        cos (S.angularFrequency * t.val) • IC.x₀ +
          (sin (S.angularFrequency * t.val) / S.angularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))
      fun_prop)
    (by
      change Differentiable ℝ (∂ₜ (fun t : Time =>
        cos (S.angularFrequency * t.val) • IC.x₀ +
          (sin (S.angularFrequency * t.val) / S.angularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀)))
      rw [S.underdampedBase_velocity IC hS]
      fun_prop)
    hbase hγ hk

/-- In the overdamped regime, the selected trajectory satisfies the damped equation of
motion. -/
lemma trajectory_equationOfMotion_of_overdamped (IC : InitialConditions)
    (hS : S.IsOverdamped) :
    S.EquationOfMotion (S.trajectory IC) := by
  rw [S.trajectory_eq_of_overdamped IC hS]
  have hγ : S.γ = 2 * S.m * S.decayRate := S.gamma_eq_two_mul_m_mul_decayRate
  have hk : S.k = S.m * (S.decayRate^2 - S.angularFrequency^2) := by
    rw [S.k_eq_m_mul_ω_sq, S.angularFrequency_sq_of_overdamped hS]
    ring
  have hbase :
      ∂ₜ (∂ₜ (S.overdampedBase IC)) =
        fun t => S.angularFrequency^2 • S.overdampedBase IC t := by
    change ∂ₜ (∂ₜ (fun t : Time =>
        cosh (S.angularFrequency * t.val) • IC.x₀ +
          (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))) =
      fun t => S.angularFrequency^2 •
        (cosh (S.angularFrequency * t.val) • IC.x₀ +
          (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))
    exact S.overdampedBase_acceleration IC hS
  exact S.exp_decay_smul_equationOfMotion S.decayRate (S.angularFrequency^2)
    (S.overdampedBase IC)
    (by
      change Differentiable ℝ (fun t : Time =>
        cosh (S.angularFrequency * t.val) • IC.x₀ +
          (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀))
      fun_prop)
    (by
      change Differentiable ℝ (∂ₜ (fun t : Time =>
        cosh (S.angularFrequency * t.val) • IC.x₀ +
          (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
            (IC.v₀ + S.decayRate • IC.x₀)))
      rw [S.overdampedBase_velocity IC hS]
      fun_prop)
    hbase hγ hk

/-- The selected trajectory satisfies the damped equation of motion. -/
lemma trajectory_equationOfMotion (IC : InitialConditions) :
    S.EquationOfMotion (S.trajectory IC) := by
  by_cases hUnder : S.IsUnderdamped
  · exact S.trajectory_equationOfMotion_of_underdamped IC hUnder
  · by_cases hCritical : S.IsCriticallyDamped
    · exact S.trajectory_equationOfMotion_of_criticallyDamped IC hCritical
    · have hOver : S.IsOverdamped := by
        rw [IsOverdamped, IsUnderdamped, IsCriticallyDamped] at *
        by_contra hNotOver
        have hNonneg : 0 ≤ S.discriminant := le_of_not_gt hUnder
        have hNonpos : S.discriminant ≤ 0 := le_of_not_gt hNotOver
        exact hCritical (le_antisymm hNonpos hNonneg)
      exact S.trajectory_equationOfMotion_of_overdamped IC hOver

/-!

### C.2. Uniqueness of the solutions

Future work: prove that, in each damping regime, the selected explicit branch is the unique
solution of the damped equation of motion with the given initial conditions.

-/

end DampedHarmonicOscillator

end ClassicalMechanics
