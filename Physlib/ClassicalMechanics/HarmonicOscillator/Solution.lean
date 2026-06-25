/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
/-!

# Solutions to the classical harmonic oscillator

## i. Overview

In this module we define the solutions to the classical harmonic oscillator,
prove that they satisfy the equation of motion, and prove some properties of the solutions.

## ii. Key results

- `InitialConditions` is a structure for the initial conditions for the harmonic oscillator.
- `trajectories` is the trajectories to the harmonic oscillator for given initial conditions.
- `trajectories_equationOfMotion` proves that the solution satisfies the equation of motion.

## iii. Table of contents

- A. The initial conditions
  - A.1. Definition of the initial conditions
  - A.2. Relation to other types of initial conditions
    - A.2.1. Initial conditions at arbitrary time
    - A.2.2. Initial conditions from two positions at different times
    - A.2.3. Initial conditions from two velocities at different times
  - A.3. The zero initial conditions
    - A.3.1. Simple results for the zero initial conditions
- B. Trajectories associated with the initial conditions
  - B.1. The trajectory associated with the initial conditions
    - B.1.1. Definitional equality for the trajectory
  - B.2. The trajectory for zero initial conditions
  - B.3. Smoothness of the trajectories
  - B.4. Velocity of the trajectories
  - B.5. Acceleration of the trajectories
  - B.6. The initial conditions of the trajectories
- C. Trajectories and Equation of motion
  - C.1. Uniqueness of the solutions
- D. The energy of the trajectories
  - D.1. Correctness of InitialConditionsAtTime conversion
  - D.2. Correctness of InitialConditionsFromTwoPositions conversion
  - D.3. Correctness of InitialConditionsFromTwoVelocities conversion
- E. The trajectories at zero velocity
  - E.1. The times at which the velocity is zero
  - E.2. A time when the velocity is zero
  - E.3. The position when the velocity is zero
- F. Some open TODOs

## iv. References

References for the classical harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 58, section 21.

-/

@[expose] public section

namespace ClassicalMechanics
open Real Time ContDiff

namespace HarmonicOscillator

variable (S : HarmonicOscillator)

/-!

## A. The initial conditions

We define the type of initial conditions for the harmonic oscillator.
The initial conditions are currently defined as an initial position and an initial velocity,
that is the values of the solution and its time derivative at time `0`.

-/
/-!

### A.1. Definition of the initial conditions

We start by defining the type of initial conditions for the harmonic oscillator.

-/

/-- The initial conditions for the harmonic oscillator specified by an initial position,
  and an initial velocity.

The `@[ext]` attribute provides an extensionality lemma for `InitialConditions`.
That is, a lemma which states that two initial conditions are equal if their
initial positions and initial velocities are equal. -/
@[ext] structure InitialConditions where
  /-- The initial position of the harmonic oscillator. -/
  x₀ : EuclideanSpace ℝ (Fin 1)
  /-- The initial velocity of the harmonic oscillator. -/
  v₀ : EuclideanSpace ℝ (Fin 1)

/-!

### A.2. Relation to other types of initial conditions

We relate the initial condition given by an initial position and an initial velocity
to other specifications of initial conditions.

In this section, we implement alternative ways to specify initial conditions for the harmonic
oscillator. The standard `InitialConditions` type specifies position and velocity at time `t=0`,
but in practice it is often useful to specify initial conditions at other times or in other forms.

Currently implemented:
- **Initial conditions at arbitrary time**: Specify position and velocity at any time `t₀`,
  not necessarily at `t=0`.
  This is useful for problems where the natural reference time is not zero.
- **Initial conditions from two positions at different times**: Specify the position at two
  distinct times `t₁` and `t₂` that satisfy the non-degeneracy condition.
- **Initial conditions from two velocities at different times**: Specify the velocity at two
  distinct times `t₁` and `t₂` that satisfy the non-degeneracy condition.

Future work (to be added in separate PRs) :
- Amplitude-phase parametrization

All alternative forms can be converted to the standard `InitialConditions` type via conversion
functions, and we prove that the converted initial conditions produce trajectories that satisfy
the original specifications.

-/

/-!

#### A.2.1. Initial conditions at arbitrary time

We define a type for initial conditions specified at an arbitrary time `t₀`, rather than at `t=0`.
This is useful when the natural reference point for a problem is not at time zero.

The conversion to the standard `InitialConditions` works by "running the trajectory backward in
time" from `t₀` to `0`. Given that we know `x(t₀)` and `v(t₀)`, we use the harmonic oscillator
solution formula with time-reversal to determine what `x(0)` and `v(0)` must have been.

Mathematically, if `x(t) = cos(ωt)·x₀ + (sin(ωt)/ω)·v₀`, then setting `t = t₀`:
  `x(t₀) = cos(ωt₀)·x₀ + (sin(ωt₀)/ω)·v₀`
  `v(t₀) = -ω·sin(ωt₀)·x₀ + cos(ωt₀)·v₀`

Solving this linear system for `x₀` and `v₀` gives the formulas in `toInitialConditions` below.

-/

/-- Initial conditions for the harmonic oscillator specified at an arbitrary time `t₀`.

  This structure allows specifying the position and velocity at any time `t₀`, not necessarily
  at `t=0`. This is useful for problems where the natural reference time is not zero.

  The conditions can be converted to the standard `InitialConditions` format (at `t=0`)
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsAtTime where
  /-- The time at which the initial conditions are specified. -/
  t₀ : Time
  /-- The position at time t₀. -/
  x_t₀ : EuclideanSpace ℝ (Fin 1)
  /-- The velocity at time t₀. -/
  v_t₀ : EuclideanSpace ℝ (Fin 1)

namespace InitialConditionsAtTime

/-- Convert initial conditions at time `t₀` to standard initial conditions at `t=0`.

  This conversion uses the harmonic oscillator solution formula with time-reversal.
  The resulting `InitialConditions` will produce a trajectory that passes through
  `x_t₀` with velocity `v_t₀` at time `t₀`.

  See `toInitialConditions_trajectory_at_t₀` and `toInitialConditions_velocity_at_t₀` for
  the correctness proofs. -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) : InitialConditions where
  x₀ := cos (S.ω * IC.t₀) • IC.x_t₀ - (sin (S.ω * IC.t₀) / S.ω) • IC.v_t₀
  v₀ := S.ω • sin (S.ω * IC.t₀) • IC.x_t₀ + cos (S.ω * IC.t₀) • IC.v_t₀

/-!
The correctness proofs showing that the conversion produces the expected trajectory
are given later in section D.1, after the trajectory machinery has been defined.
-/

end InitialConditionsAtTime


/-!

#### A.2.2. Initial conditions from two positions at different times

We define a type for initial conditions specified by two measured positions `x_t₁` and `x_t₂`
at two distinct times `t₁` and `t₂`.

The conversion to the standard `InitialConditions` is obtained by solving for `x₀` and `v₀` the
two equations given by evaluating the trajectory at `t₁` and `t₂`:
  `x_t₁ = cos(ωt₁)·x₀ + (sin(ωt₁)/ω)·v₀`
  `x_t₂ = cos(ωt₂)·x₀ + (sin(ωt₂)/ω)·v₀`

This linear system has determinant `(cos(ωt₁)·sin(ωt₂) - cos(ωt₂)·sin(ωt₁))/ω = sin(ω(t₂-t₁))/ω`.
Writing `Δ = sin(ω(t₂-t₁))`, solving the system gives the formulas used below:
  `x₀ = (sin(ωt₂)·x_t₁ - sin(ωt₁)·x_t₂)/Δ`
  `v₀ = ω·(cos(ωt₁)·x_t₂ - cos(ωt₂)·x_t₁)/Δ`

The conversion is defined as a total function, but it recovers the initial conditions only when
`Δ = sin(ω(t₂-t₁)) ≠ 0`, i.e. when `t₂ - t₁` is not an integer multiple of half a period. The
correctness proofs, under this nondegeneracy condition, are given later in section D.2.

-/

/-- Initial conditions for the harmonic oscillator specified by two positions
  `x_t₁` and `x_t₂` measured at two times `t₁` and `t₂` respectively.

  The conditions can be converted to the standard `InitialConditions` format
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsFromTwoPositions where
  /-- The first measurement time. -/
  t₁ : Time
  /-- The position at time `t₁`. -/
  x_t₁ : EuclideanSpace ℝ (Fin 1)
  /-- The second measurement time. -/
  t₂ : Time
  /-- The position at time `t₂`. -/
  x_t₂ : EuclideanSpace ℝ (Fin 1)


namespace InitialConditionsFromTwoPositions

/-- Convert two-position initial conditions to standard initial conditions at `t = 0`.

  Obtained by solving the 2×2 linear system from the trajectory formula at `t₁` and `t₂`.
  See `toInitialConditions_trajectory_at_t₁` and `toInitialConditions_trajectory_at_t₂` in
  section D.2 for the correctness proofs (valid under `sin (S.ω * (t₂ - t₁)) ≠ 0`). -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions) : InitialConditions where
  x₀ := (sin (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.x_t₁
      - (sin (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.x_t₂
  v₀ := (S.ω * cos (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.x_t₂
      - (S.ω * cos (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.x_t₁

end InitialConditionsFromTwoPositions

/-!

#### A.2.3. Initial conditions from two velocities at different times

We define a type for initial conditions specified by two measured velocities `v_t₁` and `v_t₂`
at two distinct times `t₁` and `t₂`.

The conversion to the standard `InitialConditions` is obtained by solving for `x₀` and `v₀` the
two equations given by evaluating the velocity of the trajectory at `t₁` and `t₂`:
  `v_t₁ = -ω·sin(ωt₁)·x₀ + cos(ωt₁)·v₀`
  `v_t₂ = -ω·sin(ωt₂)·x₀ + cos(ωt₂)·v₀`

This linear system has determinant `ω·(cos(ωt₁)·sin(ωt₂) - cos(ωt₂)·sin(ωt₁)) = ω·sin(ω(t₂-t₁))`.
Writing `Δ = sin(ω(t₂-t₁))`, solving the system gives the formulas used below:
  `x₀ = (cos(ωt₂)·v_t₁ - cos(ωt₁)·v_t₂)/(ω·Δ)`
  `v₀ = (sin(ωt₂)·v_t₁ - sin(ωt₁)·v_t₂)/Δ`

The conversion is defined as a total function, but it recovers the initial conditions only when
`Δ = sin(ω(t₂-t₁)) ≠ 0`, i.e. when `t₂ - t₁` is not an integer multiple of half a period. The
correctness proofs, under this nondegeneracy condition, are given later in section D.3.

-/

/-- Initial conditions for the harmonic oscillator specified by two velocities
  `v_t₁` and `v_t₂` measured at two times `t₁` and `t₂` respectively.

  The conditions can be converted to the standard `InitialConditions` format
  using the `toInitialConditions` function. -/
@[ext] structure InitialConditionsFromTwoVelocities where
  /-- The first measurement time. -/
  t₁ : Time
  /-- The velocity at time `t₁`. -/
  v_t₁ : EuclideanSpace ℝ (Fin 1)
  /-- The second measurement time. -/
  t₂ : Time
  /-- The velocity at time `t₂`. -/
  v_t₂ : EuclideanSpace ℝ (Fin 1)

namespace InitialConditionsFromTwoVelocities

/-- Convert two-velocity initial conditions to standard initial conditions at `t = 0`.

  Obtained by solving the 2×2 linear system from the velocity formula at `t₁` and `t₂`.
  See `toInitialConditions_velocity_at_t₁` and `toInitialConditions_velocity_at_t₂` in
  section D.3 for the correctness proofs (valid under `sin (S.ω * (t₂ - t₁)) ≠ 0`). -/
noncomputable def toInitialConditions (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities) : InitialConditions where
  x₀ := (cos (S.ω * IC.t₂) / (S.ω * sin (S.ω * (IC.t₂ - IC.t₁)))) • IC.v_t₁
      - (cos (S.ω * IC.t₁) / (S.ω * sin (S.ω * (IC.t₂ - IC.t₁)))) • IC.v_t₂
  v₀ := (sin (S.ω * IC.t₂) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.v_t₁
      - (sin (S.ω * IC.t₁) / sin (S.ω * (IC.t₂ - IC.t₁))) • IC.v_t₂

end InitialConditionsFromTwoVelocities

/-!

### A.3. The zero initial conditions

The zero initial conditions are the initial conditions with zero initial position
and zero initial velocity.

In the end, we will see that this corresponds to the solution which is identically zero,
i.e. the particle remains at rest at the origin.

-/

namespace InitialConditions

/-- The zero initial condition. -/
instance : Zero InitialConditions := ⟨0, 0⟩

/-!

#### A.3.1. Simple results for the zero initial conditions

Some simple results about the zero initial conditions.

-/
/-- The zero initial condition has zero starting point. -/
@[simp]
lemma x₀_zero : x₀ 0 = 0 := rfl

/-- The zero initial condition has zero starting velocity. -/
@[simp]
lemma v₀_zero : v₀ 0 = 0 := rfl

end InitialConditions
/-!

## B. Trajectories associated with the initial conditions

To each initial condition we association a trajectory. We will prove some basic properties
of these trajectories.

Eventually we will show that these trajectories satisfy the equation of motion, for
now we can think of them as some choice of trajectory associated with the initial conditions.

-/

namespace InitialConditions

/-!

### B.1. The trajectory associated with the initial conditions

-/

/-- Given initial conditions, the solution to the classical harmonic oscillator. -/
noncomputable def trajectory (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cos (S.ω * t) • IC.x₀ + (sin (S.ω * t)/S.ω) • IC.v₀

/-!

#### B.1.1. Definitional equality for the trajectory

We show a basic definitional equality for the trajectory.

-/
lemma trajectory_eq (IC : InitialConditions) :
    IC.trajectory S = fun t : Time => cos (S.ω * t) • IC.x₀ + (sin (S.ω * t)/S.ω) • IC.v₀ := rfl

/-!

### B.2. The trajectory for zero initial conditions

The trajectory for zero initial conditions is the zero function.

-/

/-- For zero initial conditions, the trajectory is zero. -/
@[simp]
lemma trajectory_zero : trajectory S 0 = fun _ => 0 := by
  simp [trajectory_eq]

/-!

### B.3. Smoothness of the trajectories

The trajectories for any initial conditions are smooth functions of time.

-/

@[fun_prop]
lemma trajectory_contDiff (S : HarmonicOscillator) (IC : InitialConditions) {n : WithTop ℕ∞} :
    ContDiff ℝ n (IC.trajectory S) := by
  rw [trajectory_eq]
  apply ContDiff.add
  · apply fun_smul
    · change ContDiff ℝ _ (((fun x => cos x) ∘ (fun y => S.ω * y))∘ Time.toRealCLM)
      refine ContDiff.comp_continuousLinearMap (ContDiff.comp contDiff_cos ?_)
      fun_prop
    · fun_prop
  · have hx := contDiff_sin (n := n)
    apply fun_smul
    · change ContDiff ℝ _ (((fun x => sin x / S.ω) ∘ (fun y => S.ω * y))∘ Time.toRealCLM)
      refine ContDiff.comp_continuousLinearMap (ContDiff.comp ?_ ?_)
      · fun_prop
      · fun_prop
    · fun_prop

/-!

### B.4. Velocity of the trajectories

We give a simplification of the velocity of the trajectory.

-/

lemma trajectory_velocity (IC : InitialConditions) : ∂ₜ (IC.trajectory S) =
    fun t : Time => - S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀ := by
  funext t
  rw [trajectory_eq, Time.deriv, fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  have h1 : (fderiv ℝ (fun t => sin (S.ω * t.val) / S.ω) t) =
    (1/ S.ω) • (fderiv ℝ (fun t => sin (S.ω * t.val)) t) := by
    rw [← fderiv_mul_const]
    congr
    funext t
    field_simp
    fun_prop
  simp [h1]
  rw [fderiv_cos (by fun_prop), fderiv_sin (by fun_prop),
    fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [fderiv_fun_const, Pi.zero_apply, smul_zero, add_zero, neg_smul,
    _root_.neg_apply, FunLike.coe_smul, Pi.smul_apply, fderiv_val,
    smul_eq_mul, mul_one]
  field_simp
  ring_nf
  rw [← mul_smul, mul_rotate, NonUnitalRing.mul_assoc]
  field_simp [mul_div_assoc, div_self, mul_one, S.ω_ne_zero]

/-!

### B.5. Acceleration of the trajectories

We give a simplification of the acceleration of the trajectory.

-/

lemma trajectory_acceleration (IC : InitialConditions) : ∂ₜ (∂ₜ (IC.trajectory S)) =
    fun t : Time => - S.ω^2 • cos (S.ω * t.val) • IC.x₀ - S.ω • sin (S.ω * t.val) • IC.v₀ := by
  funext t
  rw [trajectory_velocity, Time.deriv, fderiv_fun_add (by fun_prop) (by fun_prop)]
  rw [fderiv_smul_const (by fun_prop), fderiv_fun_const_smul (by fun_prop),
    fderiv_smul_const (by fun_prop)]
  simp only [neg_smul, add_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_cos (by fun_prop), fderiv_sin (by fun_prop),
    fderiv_fun_mul (by fun_prop) (by fun_prop)]
  field_simp [smul_smul]
  simp only [fderiv_fun_const, Pi.ofNat_apply, smul_zero, add_zero, _root_.neg_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply, fderiv_val,
    smul_eq_mul, mul_one, neg_smul]
  ring_nf
  module

/-!

### B.6. The initial conditions of the trajectories

We show that, unsurprisingly, the trajectories have the initial conditions
used to define them.

-/

/-- For a set of initial conditions `IC` the position of the solution at time `0` is
  `IC.x₀`. -/
@[simp]
lemma trajectory_position_at_zero (IC : InitialConditions) : IC.trajectory S 0 = IC.x₀ := by
  simp [trajectory]

@[simp]
lemma trajectory_velocity_at_zero (IC : InitialConditions) : ∂ₜ (IC.trajectory S) 0 = IC.v₀ := by
  simp [trajectory_velocity]

/-!

## C. Trajectories and Equation of motion

The trajectories satisfy the equation of motion for the harmonic oscillator.

-/

lemma trajectory_equationOfMotion (IC : InitialConditions) :
    EquationOfMotion S (IC.trajectory S) := by
  have hcont : ContDiff ℝ ∞ (IC.trajectory S) := trajectory_contDiff S IC
  rw [EquationOfMotion, gradLagrangian_eq_force (S := S) (xₜ := IC.trajectory S) hcont]
  funext t
  simp only [Pi.zero_apply]
  rw [trajectory_acceleration, force_eq_linear]
  ext
  have hω : S.ω ≠ 0 := ω_ne_zero S
  have hωm : S.ω ^ 2 * S.m = S.k := by
    rw [ω_sq]
    field_simp [m_ne_zero S]
  simp [trajectory_eq, smul_add, smul_smul, mul_comm]
  rw [← hωm]
  field_simp [hω]
  ring

/-!

### C.1. Uniqueness of the solutions

We show that the trajectories are the unique solutions to the equation of motion
for the given initial conditions.

-/
/-- The trajectories to the equation of motion for a given set of initial conditions
  are unique.

  Given any smooth `x` satisfying the equation of motion with the same initial
  position and velocity, the difference `y = x - IC.trajectory S` also solves the
  equation of motion with zero initial conditions; energy conservation then forces
  its energy, and hence `y`, to vanish identically, so `x = IC.trajectory S`. -/
lemma trajectories_unique (IC : InitialConditions) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) :
    S.EquationOfMotion x ∧ x 0 = IC.x₀ ∧ ∂ₜ x 0 = IC.v₀ →
    x = IC.trajectory S := by
  intro h
  rcases h with ⟨hEOM, hx0, hv0⟩

  -- Newton form for x
  have hNewt_x :
      ∀ t, S.m • ∂ₜ (∂ₜ x) t = force S (x t) :=
    (S.equationOfMotion_iff_newtons_2nd_law (xₜ := x) hx).1 hEOM

  -- Newton form for the explicit trajectory
  have hTrajContDiff : ContDiff ℝ ∞ (IC.trajectory S) := by
    -- trajectory_contDiff already exists and is [fun_prop]
    fun_prop

  have hNewt_traj :
      ∀ t, S.m • ∂ₜ (∂ₜ (IC.trajectory S)) t = force S ((IC.trajectory S) t) :=
    (S.equationOfMotion_iff_newtons_2nd_law (xₜ := IC.trajectory S) hTrajContDiff).1
      (trajectory_equationOfMotion S IC)

  -- Define the difference y = x - traj
  set y : Time → EuclideanSpace ℝ (Fin 1) := fun t => x t - IC.trajectory S t with hydef

  have hyContDiff : ContDiff ℝ ∞ y := by
    -- ContDiff closed under subtraction
    simpa [hydef] using hx.sub hTrajContDiff

  -- First derivative of y
  have hy_deriv : ∂ₜ y = fun t => ∂ₜ x t - ∂ₜ (IC.trajectory S) t := by
    funext t
    -- same style as in trajectory_velocity: unfold Time.deriv and use fderiv_fun_sub
    rw [hydef, Time.deriv]
    -- ContDiff implies DifferentiableAt - use this explicitly since fun_prop can't infer it
    -- ContDiff ℝ ∞ f implies ContDiffAt ℝ ∞ f t for any t
    have hx_contDiffAt : ContDiffAt ℝ ∞ x t := hx.contDiffAt
    have htraj_contDiffAt : ContDiffAt ℝ ∞ (IC.trajectory S) t := hTrajContDiff.contDiffAt
    have hx_diff : DifferentiableAt ℝ x t :=
      ContDiffAt.differentiableAt hx_contDiffAt (by simp)
    have htraj_diff : DifferentiableAt ℝ (IC.trajectory S) t :=
      ContDiffAt.differentiableAt htraj_contDiffAt (by simp)
    rw [fderiv_fun_sub hx_diff htraj_diff]
    simp only [_root_.sub_apply, Time.deriv]

  -- Second derivative of y
  have hy_deriv2 :
      ∂ₜ (∂ₜ y) = fun t => ∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ (IC.trajectory S)) t := by
    funext t
    rw [hy_deriv, Time.deriv]
    -- now differentiate (∂ₜ x - ∂ₜ traj)
    -- use differentiability of time-derivatives from ContDiff
    have hx1 : Differentiable ℝ (fun t => ∂ₜ x t) :=
      deriv_differentiable_of_contDiff x hx
    have htr1 : Differentiable ℝ (fun t => ∂ₜ (IC.trajectory S) t) :=
      deriv_differentiable_of_contDiff (IC.trajectory S) hTrajContDiff
    -- Apply fderiv_fun_sub and use Time.deriv to convert back
    -- Differentiable ℝ f means ∀ x, DifferentiableAt ℝ f x
    -- In Mathlib, Differentiable is defined as ∀ x, DifferentiableAt, so we can apply directly
    have hx1_at : DifferentiableAt ℝ (fun t => ∂ₜ x t) t := hx1 t
    have htr1_at : DifferentiableAt ℝ (fun t => ∂ₜ (IC.trajectory S) t) t := htr1 t
    rw [fderiv_fun_sub hx1_at htr1_at]
    -- Now we need to show fderiv of (fun t => fderiv ℝ x t 1) equals fderiv of (∂ₜ x)
    -- This follows from Time.deriv f t = fderiv ℝ f t 1
    simp only [sub_apply]
    rw [Time.deriv, Time.deriv]

  -- Newton form for y (linearity of force)
  have hNewt_y : ∀ t, S.m • ∂ₜ (∂ₜ y) t = force S (y t) := by
    intro t
    have hy2t : ∂ₜ (∂ₜ y) t =
        (∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ (IC.trajectory S)) t) := by
      simpa using congrFun hy_deriv2 t

    -- Expand and substitute Newton laws for x and traj, then fold back using force_eq_linear
    calc
      S.m • ∂ₜ (∂ₜ y) t
          = S.m • (∂ₜ (∂ₜ x) t - ∂ₜ (∂ₜ (IC.trajectory S)) t) := by
              simp [hy2t]
      _ = (S.m • ∂ₜ (∂ₜ x) t) - (S.m • ∂ₜ (∂ₜ (IC.trajectory S)) t) := by
              simp [smul_sub]
      _ = force S (x t) - force S ((IC.trajectory S) t) := by
              simp [hNewt_x t, hNewt_traj t]
      _ = force S (y t) := by
              -- force = -k•x, so it is linear: force(x) - force(traj) = force(x-traj)
              -- and y t = x t - traj t by definition
              simp [hydef, force_eq_linear, smul_sub]

  -- Turn Newton form back into EquationOfMotion for y
  have hEOM_y : S.EquationOfMotion y :=
    (S.equationOfMotion_iff_newtons_2nd_law (xₜ := y) hyContDiff).2 hNewt_y

  -- Initial conditions for y are zero
  have hy0 : y 0 = 0 := by
    -- y 0 = x 0 - traj 0 = IC.x₀ - IC.x₀
    simp [hydef, hx0]

  have hyv0 : ∂ₜ y 0 = 0 := by
    -- ∂ₜ y 0 = ∂ₜ x 0 - ∂ₜ traj 0 = IC.v₀ - IC.v₀
    rw [congr_fun hy_deriv 0]
    rw [hv0, trajectory_velocity_at_zero S IC]
    simp

  -- Energy at time 0 is 0
  have hE0 : S.energy y 0 = 0 := by
    -- unfold energy, kinetic, potential and use hy0, hyv0
    simp [HarmonicOscillator.energy, HarmonicOscillator.kineticEnergy,
      HarmonicOscillator.potentialEnergy, hy0, hyv0, one_div, smul_eq_mul]

  -- Energy is constant, hence always 0
  have hE : ∀ t, S.energy y t = 0 := by
    intro t
    have ht := S.energy_conservation_of_equationOfMotion' (xₜ := y) hyContDiff hEOM_y t
    simpa [hE0] using ht

  -- From energy=0 and positivity => y(t)=0
  have hy_all : ∀ t, y t = 0 := by
    intro t
    have hEt : S.energy y t = 0 := hE t

    have hk_nonneg : 0 ≤ S.kineticEnergy y t := by
      unfold HarmonicOscillator.kineticEnergy
      have hcoeff : 0 ≤ (1 / (2 : ℝ)) * S.m := by
        exact mul_nonneg (by norm_num) (le_of_lt S.m_pos)
      -- Use the same approach as for potential energy below
      have hin : 0 ≤ inner ℝ (∂ₜ y t) (∂ₜ y t) := by
        -- For EuclideanSpace ℝ (Fin 1), inner product with itself is nonnegative
        exact real_inner_self_nonneg (x := ∂ₜ y t)
      exact mul_nonneg hcoeff hin

    have hp_nonneg : 0 ≤ S.potentialEnergy (y t) := by
      unfold HarmonicOscillator.potentialEnergy
      -- potentialEnergy = (1/2) * k * ⟪y,y⟫
      simp only [one_div, smul_eq_mul]
      -- Goal is 0 ≤ 2⁻¹ * (S.k * inner ℝ (y t) (y t))
      apply mul_nonneg
      · norm_num -- 0 ≤ 2⁻¹
      · -- 0 ≤ S.k * inner ℝ (y t) (y t)
        have hk_pos : 0 ≤ S.k := le_of_lt S.k_pos
        have hin : 0 ≤ inner ℝ (y t) (y t) := by
          -- For EuclideanSpace ℝ (Fin 1), inner product with itself is nonnegative
          exact real_inner_self_nonneg (x := y t)
        exact mul_nonneg hk_pos hin

    have hp_le : S.potentialEnergy (y t) ≤ S.energy y t := by
      unfold HarmonicOscillator.energy
      exact le_add_of_nonneg_left hk_nonneg

    have hp0 : S.potentialEnergy (y t) = 0 := by
      have : S.potentialEnergy (y t) ≤ 0 := by
        calc
          S.potentialEnergy (y t) ≤ S.energy y t := hp_le
          _ = 0 := hEt
      exact le_antisymm this hp_nonneg

    -- extract ⟪y,y⟫ = 0 from potentialEnergy = 0, then y=0
    have hy_inner0 : inner ℝ (y t) (y t) = 0 := by
      -- potentialEnergy = (1/2) * k * ⟪y,y⟫
      have hmul : ((1 / (2 : ℝ)) * S.k) * inner ℝ (y t) (y t) = 0 := by
        simpa [HarmonicOscillator.potentialEnergy, one_div, smul_eq_mul, mul_assoc] using hp0
      have hcoeff : ((1 / (2 : ℝ)) * S.k) ≠ 0 := by
        exact mul_ne_zero (by norm_num) (S.k_ne_zero)
      rcases mul_eq_zero.mp hmul with hcoeff0 | hinner
      · exact (False.elim (hcoeff hcoeff0))
      · exact hinner

    exact (inner_self_eq_zero.mp hy_inner0)

  -- Conclude x = traj
  funext t
  have : y t = 0 := hy_all t
  -- y t = x t - traj t
  simpa [hydef] using (sub_eq_zero.mp this)

/-!

## D. The energy of the trajectories

For a given set of initial conditions, the energy of the trajectory is constant,
due to the conservation of energy. Here we show it's value.

-/

lemma trajectory_energy (IC : InitialConditions) : S.energy (IC.trajectory S) =
    fun _ => 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) := by
  funext t
  rw [energy_conservation_of_equationOfMotion' _ _ (by fun_prop) (trajectory_equationOfMotion S IC)]
  simp [energy, kineticEnergy, potentialEnergy]
  ring

end InitialConditions

/-!

## D.1. Correctness of InitialConditionsAtTime conversion

We now prove the correctness lemmas for the `InitialConditionsAtTime.toInitialConditions`
conversion function. These show that the conversion produces a trajectory that passes through
the specified position and velocity at the specified time.

-/

namespace InitialConditionsAtTime

/-- The trajectory resulting from `toInitialConditions` passes through the specified
  position `x_t₀` at time `t₀`. -/
@[simp]
lemma toInitialConditions_trajectory_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    (IC.toInitialConditions S).trajectory S IC.t₀ = IC.x_t₀ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [smul_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have h1 : cos (S.ω * IC.t₀.val) ^ 2 + sin (S.ω * IC.t₀.val) ^ 2 = 1 :=
    cos_sq_add_sin_sq (S.ω * IC.t₀.val)
  field_simp [S.ω_ne_zero]
  nth_rw 2 [← mul_one (S.ω * IC.x_t₀.ofLp i)]
  rw [← h1]
  ring

/-- The trajectory resulting from `toInitialConditions` has the specified
  velocity `v_t₀` at time `t₀`. -/
@[simp]
lemma toInitialConditions_velocity_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₀ = IC.v_t₀ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, smul_add, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  have h1 : cos (S.ω * IC.t₀.val) ^ 2 + sin (S.ω * IC.t₀.val) ^ 2 = 1 :=
    cos_sq_add_sin_sq (S.ω * IC.t₀.val)
  field_simp [S.ω_ne_zero]
  nth_rw 3 [← mul_one (IC.v_t₀.ofLp i)]
  rw [← h1]
  ring

/-- The energy of the trajectory at time `t₀` equals the energy computed from the
  initial conditions at `t₀`. -/
lemma toInitialConditions_energy_at_t₀ (S : HarmonicOscillator)
    (IC : InitialConditionsAtTime) :
    S.energy ((IC.toInitialConditions S).trajectory S) IC.t₀ =
    1/2 * (S.m * ‖IC.v_t₀‖^2 + S.k * ‖IC.x_t₀‖^2) := by
  unfold energy kineticEnergy potentialEnergy
  simp only [toInitialConditions_trajectory_at_t₀, toInitialConditions_velocity_at_t₀]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  simp only [smul_eq_mul]
  ring

end InitialConditionsAtTime

/-!

## D.2. Correctness of InitialConditionsFromTwoPositions conversion

The conversion recovers the initial conditions only when `sin (S.ω * (t₂ - t₁)) ≠ 0`. This
condition fails exactly when `ω·(t₂ - t₁) = n·π` for some integer `n`, i.e. when `t₂ - t₁` is an
integer multiple of half a period; in that case `x(t₂) = (-1)^n · x(t₁)` for every trajectory,
independent of `v₀`, so the two positions do not determine the initial conditions.

Under this nondegeneracy condition, we prove that the resulting trajectory passes through `x_t₁`
at `t₁` and `x_t₂` at `t₂`.

-/

namespace InitialConditionsFromTwoPositions

/-- The trajectory from `toInitialConditions` passes through `x_t₁` at time `t₁`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_trajectory_at_t₁ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    (IC.toInitialConditions S).trajectory S IC.t₁ = IC.x_t₁ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]

/-- The trajectory from `toInitialConditions` passes through `x_t₂` at time `t₂`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_trajectory_at_t₂ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoPositions)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    (IC.toInitialConditions S).trajectory S IC.t₂ = IC.x_t₂ := by
  rw [InitialConditions.trajectory_eq, toInitialConditions]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]

end InitialConditionsFromTwoPositions

/-!

## D.3. Correctness of InitialConditionsFromTwoVelocities conversion

The conversion recovers the initial conditions only when `sin (S.ω * (t₂ - t₁)) ≠ 0`. Under this
nondegeneracy condition, we prove that the resulting trajectory has velocity `v_t₁` at `t₁` and
`v_t₂` at `t₂`.

-/

namespace InitialConditionsFromTwoVelocities

/-- The trajectory from `toInitialConditions` has velocity `v_t₁` at time `t₁`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_velocity_at_t₁ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₁ = IC.v_t₁ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]

/-- The trajectory from `toInitialConditions` has velocity `v_t₂` at time `t₂`,
  provided `sin (S.ω * (t₂ - t₁)) ≠ 0`. -/
lemma toInitialConditions_velocity_at_t₂ (S : HarmonicOscillator)
    (IC : InitialConditionsFromTwoVelocities)
    (hΔ : sin (S.ω * (IC.t₂ - IC.t₁)) ≠ 0) :
    ∂ₜ ((IC.toInitialConditions S).trajectory S) IC.t₂ = IC.v_t₂ := by
  rw [InitialConditions.trajectory_velocity, toInitialConditions]
  ext i
  simp only [neg_smul, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  field_simp [S.ω_ne_zero]
  grind [mul_sub, Real.sin_sub]

end InitialConditionsFromTwoVelocities

namespace InitialConditions

/-!

## E. The trajectories at zero velocity

We study the properties of the trajectories when the velocity is zero.

-/

/-!

### E.1. The times at which the velocity is zero

We show that if the velocity of the trajectory is zero, then the time satisfies
the condition that
```
tan (S.ω * t) = IC.v₀ 0 / (S.ω * IC.x₀ 0)
```

-/
lemma tan_time_eq_of_trajectory_velocity_eq_zero (IC : InitialConditions) (t : Time)
    (h : ∂ₜ (IC.trajectory S) t = 0) (hx : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0) :
    tan (S.ω * t) = IC.v₀ 0 / (S.ω * IC.x₀ 0) := by
  rw [trajectory_velocity] at h
  simp at h
  have hx : S.ω ≠ 0 := by exact ω_ne_zero S
  by_cases h1 : IC.x₀ ≠ 0
  by_cases h2 : IC.v₀ ≠ 0
  have h1' : IC.x₀ 0 ≠ 0 := by
    intro hn
    apply h1
    ext i
    fin_cases i
    simp [hn]
  have hcos : cos (S.ω * t.val) ≠ 0 := by
    by_contra hn
    rw [hn] at h
    rw [Real.cos_eq_zero_iff_sin_eq] at hn
    simp_all
  rw [tan_eq_sin_div_cos]
  field_simp
  trans (sin (S.ω * t.val) * (S.ω * IC.x₀ 0)) +
    (-(S.ω • sin (S.ω * t.val) • IC.x₀) + cos (S.ω * t.val) • IC.v₀) 0
  · rw [h]
    simp only [Fin.isValue, PiLp.zero_apply, add_zero]
    ring_nf
  · simp only [Fin.isValue, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    ring_nf
  simp at h2
  rw [h2] at h ⊢
  simp_all
  simp [tan_eq_sin_div_cos, h]
  simp at h1
  rw [h1] at h ⊢
  simp_all
  simp [tan_eq_sin_div_cos, h]

/-!

### E.2. A time when the velocity is zero

We show that as long as the initial position is non-zero, then at
the time `arctan (IC.v₀ 0 / (S.ω * IC.x₀ 0)) / S.ω` the velocity is zero.

-/

lemma trajectory_velocity_eq_zero_at_arctan (IC : InitialConditions) (hx : IC.x₀ ≠ 0) :
    (∂ₜ (IC.trajectory S)) (arctan (IC.v₀ 0 / (S.ω * IC.x₀ 0)) / S.ω) = 0 := by
  rw [trajectory_velocity]
  simp [neg_smul]
  have hx' : S.ω ≠ 0 := by exact ω_ne_zero S
  field_simp
  rw [Real.sin_arctan, Real.cos_arctan]
  ext i
  simp [one_div]
  trans (-(S.ω * (IC.v₀ 0 / (S.ω * IC.x₀ 0) * IC.x₀ 0)) + IC.v₀ 0) *
    (√(1 + (IC.v₀ 0 / (S.ω * IC.x₀ 0)) ^ 2))⁻¹
  · fin_cases i
    simp only [Fin.isValue, Fin.zero_eta]
    ring
  simp [mul_eq_zero, inv_eq_zero]
  left
  field_simp
  have hx : IC.x₀ 0 ≠ 0 := by
    intro hn
    apply hx
    ext i
    fin_cases i
    simp [hn]
  field_simp
  ring

/-!

### E.3. The position when the velocity is zero

We show that the position is equal to `√(‖IC.x₀‖^2 + (‖IC.v₀‖/S.ω)^2) ` when
the velocity is zero.

-/

lemma trajectory_velocity_eq_zero_iff (IC : InitialConditions) (t : Time) :
    ∂ₜ (IC.trajectory S) t = 0 ↔
    ‖(IC.trajectory S) t‖ = √(‖IC.x₀‖^2 + (‖IC.v₀‖/S.ω)^2) := by
  have := by exact energy_eq S (trajectory S IC)
  have h_energy_t := congrFun this t
  simp only [kineticEnergy_eq, one_div, potentialEnergy_eq, smul_eq_mul] at h_energy_t
  rw [real_inner_self_eq_norm_sq (trajectory S IC t)] at h_energy_t
  have := by exact trajectory_energy S IC
  have h_init := congrFun this t
  have h_ω := by exact ω_sq S
  constructor
  · intro h_partial
    rw [h_partial, inner_zero_left, mul_zero, zero_add] at h_energy_t
    have h₁ : ‖trajectory S IC t‖ ^ 2 = S.energy (trajectory S IC) t * 2 * (1 / S.k) := by
      simp [h_energy_t]
      field_simp
    symm
    refine (sqrt_eq_iff_mul_self_eq ?_ ?_).mpr ?_
    · apply add_nonneg <;> apply sq_nonneg
    · apply norm_nonneg
    rw [← pow_two]
    rw [h₁, h_init]
    ring_nf
    rw [mul_assoc]
    rw [mul_inv_cancel₀]
    · rw [mul_one, inv_eq_one_div S.k, mul_assoc]
      rw [mul_one_div S.m S.k, ← inverse_ω_sq]
      ring
    · exact k_ne_zero S
  · intro h_norm
    apply norm_eq_zero.mp
    rw [real_inner_self_eq_norm_sq (∂ₜ (trajectory S IC) t)] at h_energy_t
    have energies : S.energy (trajectory S IC) t = S.energy (trajectory S IC) t := by rfl
    nth_rewrite 1 [h_energy_t] at energies
    nth_rewrite 1 [h_init] at energies
    rw [h_norm] at energies
    have h₁ : S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2 + S.k * (√(‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2) ^ 2)
            = S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2 := by
      calc
        S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2 + S.k * (√(‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2) ^ 2)
            = 2 * (2⁻¹ * S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2
            + 2⁻¹ * (S.k * √(‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2) ^ 2)) := by
          simp [mul_add]
          rw [← mul_assoc, ← mul_assoc]
          rw [mul_inv_cancel_of_invertible 2, one_mul]
      _ = 2 * (1 / 2 * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2)) := by rw [energies]
      _ = S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2 := by simp
    have h₂ : S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2 + S.k * (‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2)
        = S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2 := by
      rw [← h₁, sq_sqrt ?_]
      apply add_nonneg
      apply sq_nonneg
      apply sq_nonneg
    have h₃: ‖∂ₜ (trajectory S IC) t‖ ^ 2 = ‖IC.v₀‖ ^ 2 - (S.k / S.m) * (‖IC.v₀‖ / S.ω) ^ 2 := by
      calc
        ‖∂ₜ (trajectory S IC) t‖ ^ 2 = (1 / S.m) * (S.m * ‖∂ₜ (trajectory S IC) t‖ ^ 2
        + S.k * (‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2) - S.k * (‖IC.x₀‖ ^ 2
        + (‖IC.v₀‖ / S.ω) ^ 2)) := by simp
        _ = (1 / S.m) * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2
          - S.k * (‖IC.x₀‖ ^ 2 + (‖IC.v₀‖ / S.ω) ^ 2)) := by rw [h₂]
        _ = (1 / S.m) * (S.m * ‖IC.v₀‖ ^ 2 + S.k * ‖IC.x₀‖ ^ 2
          - S.k * ‖IC.x₀‖ ^ 2 - S.k * (‖IC.v₀‖ / S.ω) ^ 2) := by
          rw [mul_add S.k (‖IC.x₀‖ ^ 2) ((‖IC.v₀‖ /S.ω) ^2)]
          rw [← sub_sub_sub_eq (S.m * ‖IC.v₀‖ ^ 2) (S.k * ‖IC.x₀‖ ^ 2)
          (S.k * (‖IC.v₀‖ / S.ω) ^ 2) (S.k * ‖IC.x₀‖ ^ 2)]
          simp only [one_div, sub_sub_sub_cancel_right, add_sub_cancel_right]
        _ = (1 / S.m) * (S.m * ‖IC.v₀‖ ^ 2 - S.k * (‖IC.v₀‖ / S.ω) ^ 2) := by simp
        _ = (1 / S.m) * (S.m * ‖IC.v₀‖ ^ 2) - (1 / S.m) * (S.k * (‖IC.v₀‖ / S.ω) ^ 2) := by
          rw [mul_sub (1 / S.m) (S.m * ‖IC.v₀‖ ^ 2) (S.k * (‖IC.v₀‖ / S.ω) ^ 2)]
        _ = ‖IC.v₀‖ ^ 2 - (S.k / S.m) * (‖IC.v₀‖ / S.ω) ^ 2 := by
          simp only [one_div, ne_eq, m_ne_zero, not_false_eq_true, inv_mul_cancel_left₀,
            sub_right_inj]
          rw [← mul_assoc, inv_mul_eq_div S.m S.k]
    rw [← ω_sq, div_pow ‖IC.v₀‖ S.ω 2] at h₃
    rw [mul_div_cancel₀ (‖IC.v₀‖ ^ 2) ?_] at h₃
    rw [sub_self (‖IC.v₀‖ ^ 2)] at h₃
    rw [sq_eq_zero_iff] at h₃
    exact h₃
    rw [pow_ne_zero_iff ?_]
    apply ω_ne_zero
    exact Ne.symm (Nat.zero_ne_add_one 1)
end InitialConditions

/--
The period of a harmonic oscillator is `2 * π / ω`.
-/
noncomputable def period (S : HarmonicOscillator) : ℝ := 2 * π / S.ω

@[inherit_doc period]
scoped notation "T" => HarmonicOscillator.period

lemma period_eq : T S = 2 * π / S.ω := rfl

lemma period_pos : 0 < T S := by
  have := S.ω_pos
  rw [period_eq]
  positivity

/--
The trajectory of the harmonic oscillator is periodic with period of `2 * π / ω`.
-/
lemma trajectory_periodic (IC : InitialConditions) :
    Function.Periodic (IC.trajectory S) (T S) := fun t ↦ by
  have h : S.ω * (t.val + 2 * π / S.ω) = S.ω * t.val + 2 * π := by
    have := S.ω_ne_zero
    ring_nf; field_simp
  rw [InitialConditions.trajectory, add_val, period_eq, h, cos_add_two_pi, sin_add_two_pi]
  rfl

/--
Assuming that the initial coordinate and velocity are not simultaneously zero,
the time stamps when the harmonic oscillator returns to its initial coordinate and velocity is
a multiple of its period
-/
lemma return_time (IC : InitialConditions) (non_trivial : IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0)
    (t : Time) (ht : IC.trajectory S t = IC.x₀ ∧ ∂ₜ (IC.trajectory S) t = IC.v₀) :
    ∃ n : ℤ,  (n : ℝ) * (T S) = t := by
  have htx := ht.left
  have htv := ht.right
  rw [InitialConditions.trajectory_eq] at htx
  rw [InitialConditions.trajectory_velocity] at htv
  simp at htx
  simp at htv
  set c := cos (S.ω * t)
  set s :=  sin (S.ω * t)
  set xx := inner ℝ IC.x₀ IC.x₀
  set vv := inner ℝ IC.v₀ IC.v₀
  set xv := inner ℝ IC.x₀ IC.v₀
  set det := vv + xx *  S.ω^2
  have zero_lt_det :  0 < det := by
   cases non_trivial with
   | inl hx =>
    have  xx_gt_zero : 0 < xx  := by
        apply real_inner_self_pos.mpr
        exact hx
    calc
      0 < xx * S.ω^2 := by bound
      _ ≤  ‖IC.v₀‖^2 +   xx * S.ω^2  := by bound
      _ = vv +   xx * S.ω^2 := by rw [← real_inner_self_eq_norm_sq IC.v₀]
      _ = det := by rfl
   | inr hv =>
     have vv_gt_zero : 0 < vv := by
        apply real_inner_self_pos.mpr
        exact hv
     calc
        0 <  vv := vv_gt_zero
        _ ≤ vv +   ‖IC.x₀‖^2 * S.ω^2 := by bound
        _ = vv +   xx * S.ω^2  := by rw [← real_inner_self_eq_norm_sq IC.x₀]
        _ = det := by rfl
  have det_ne_zero : det ≠ 0 := by bound
  have hxx : c * xx + (s / S.ω) * xv = xx := by
    calc
     c * xx + (s / S.ω) * xv =  (inner ℝ (c • IC.x₀) IC.x₀) + (s / S.ω) * xv := by
       rw[real_inner_smul_left]
     (inner ℝ (c • IC.x₀) IC.x₀) + (s / S.ω) * xv =
       (inner ℝ (c • IC.x₀) IC.x₀) + (s / S.ω) * inner ℝ  IC.v₀ IC.x₀ := by
         rw [real_inner_comm IC.x₀ IC.v₀]
     _  = (inner ℝ (c • IC.x₀) IC.x₀) +  inner ℝ  ((s / S.ω)  • IC.v₀) IC.x₀ := by
       rw [real_inner_smul_left IC.v₀]
     _ = (inner ℝ (c • IC.x₀ + (s / S.ω)  • IC.v₀) IC.x₀) := by rw [inner_add_left]
     _ = xx := by rw [htx]
  have hvv : - S.ω * s * xv + c * vv = vv := by
    calc
     - S.ω * s * xv + c * vv = - S.ω * (s * xv) + c * vv := by ring_nf
     _ = - S.ω * inner ℝ (s • IC.x₀) IC.v₀ + c * vv := by rw[real_inner_smul_left]
     _ = inner ℝ  (- S.ω • s • IC.x₀ ) IC.v₀ + c * vv := by rw [← real_inner_smul_left]
     _ = inner ℝ  (- S.ω • s • IC.x₀ ) IC.v₀ + inner ℝ (c • IC.v₀) IC.v₀ := by
       rw [← real_inner_smul_left]
     _ = inner ℝ (- S.ω • s • IC.x₀ + c • IC.v₀) IC.v₀ := by rw [inner_add_left]
     _ = inner ℝ (-( S.ω • s • IC.x₀) + c • IC.v₀) IC.v₀ := by rw [neg_smul]
     _ = vv := by rw [htv]
  have hcos : 1 = cos (S.ω * t) := by
    calc
    1 =  det / det := by simp only [ne_eq, det_ne_zero, not_false_eq_true, div_self]
    _ = (vv + xx * S.ω^2 ) / det := by rfl
    _ = c * ((vv + xx * S.ω^2) / det) + s * xv *S.ω* (S.ω/S.ω-1 ) / det := by
      nth_rewrite 1 [← hvv, ← hxx]
      ring_nf
    _ = c * ((vv + xx * S.ω^2) / det ) := by
      simp only [ne_eq, S.ω_ne_zero, not_false_eq_true,
        div_self, sub_self, mul_zero, zero_div, add_zero]
    _ = c * (det / det) := by rfl
    _ = c := by simp only [ne_eq, det_ne_zero, not_false_eq_true, div_self, mul_one]
    _ = _ := by rfl
  let ⟨n, hn⟩ := (Real.cos_eq_one_iff (S.ω * t)).mp (Eq.symm hcos)
  use n
  calc
    (n : ℝ) * (T S) = (n : ℝ) * (2 * π / S.ω) := by rfl
    _ = ((n : ℝ) * (2 * π)) / S.ω := by ring_nf
    _ = (S.ω * t) / S.ω := by rw [hn]
    _ = t * (S.ω / S.ω) := by ring_nf
    _ = t := by simp only [ne_eq, S.ω_ne_zero, not_false_eq_true, div_self, mul_one]


/-!

## F. Some open TODOs

We give some open TODOs for the classical harmonic oscillator.

-/


TODO "For the classical harmonic oscillator find the times for
  which it passes through zero."

end HarmonicOscillator

end ClassicalMechanics
