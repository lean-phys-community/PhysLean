/-
Copyright (c) 2026 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini, Florian Wiesner
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
/-!

# The damped harmonic oscillator

## i. Overview

The damped harmonic oscillator is a classical mechanical system consisting of a mass `m`
under a restoring force `- k x` and a damping force `- γ ẋ`, where `k` is the spring
constant, `γ` is the damping coefficient, `x` is the position, and `ẋ` is the velocity.

The equation of motion for the damped harmonic oscillator is:
```
m ẍ + γ ẋ + k x = 0
```

Depending on the relationship between the damping coefficient and the natural frequency,
the system exhibits three different behaviors:
- **Underdamped** (`γ^2 < 4 * m * k`): oscillatory motion with exponentially decaying
  amplitude.
- **Critically damped** (`γ^2 = 4 * m * k`): fastest return to equilibrium without
  oscillation.
- **Overdamped** (`γ^2 > 4 * m * k`): slow return to equilibrium without oscillation.

In this file, the position and velocity both have type `EuclideanSpace ℝ (Fin 1)`. This
coordinate model is useful for a first formalization, but it works only because the
one-dimensional configuration space and its tangent space are both isomorphic to
one-dimensional Euclidean space. A more geometric formalization should represent the
configuration space and its tangent bundle directly.

## ii. Key results

The key results in the study of the classical damped harmonic oscillator are the following:

In the `Basic` module:
- `DampedHarmonicOscillator` contains the input data to the problem.
- `EquationOfMotion` defines the damped oscillator equation `m ẍ + γ ẋ + k x = 0`.
- `energy_dissipation_rate` computes the rate at which damping removes mechanical energy.
- `IsUnderdamped`, `IsCriticallyDamped`, and `IsOverdamped` define the three damping
  regimes from the discriminant `γ^2 - 4 * m * k`.
- `toUndamped_equationOfMotion` relates the damped and undamped equations of motion when
  the damping coefficient is zero.

In the `Solution` module:
- `InitialConditions` contains the initial position and velocity.
- `trajectory_underdamped`, `trajectory_criticallydamped`, and `trajectory_overdamped` give the
  explicit regime-specific solutions.

## iii. Table of contents

- A. The input data
- B. The equation of motion and energy dissipation
  - B.1. The equation of motion
  - B.2. Energy dissipation
- C. Newton's second law
  - C.1. The force
  - C.2. Equation of motion if and only if Newton's second law
- D. Damping regimes
- E. To undamped oscillator

## iv. References

References for the damped harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 76, section 25.
- Goldstein, Classical Mechanics, Chapter 2.

-/

@[expose] public section

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace
open MeasureTheory
open ContDiff
open Time

TODO "Create a new file for the geometric model which properly models the
 position as a configuration space and velocity as its tangent space, see the
 HarmonicOscillator file."

TODO "Define and prove properties of the quality factor Q."

TODO "Define and prove properties of the relaxation time τ."

/-!

## A. The input data

We start by defining a structure containing the input data of the damped harmonic oscillator.
The mass `m` and spring constant `k` are inherited from `HarmonicOscillator`; this file adds
the damping coefficient `γ`.

-/

/-- The classical damped harmonic oscillator is specified by a mass `m`, a spring
constant `k`, and a damping coefficient `γ`.

The mass and spring constant are inherited from `HarmonicOscillator` and are positive.
The damping coefficient is assumed to be nonnegative. -/
@[ext]
structure DampedHarmonicOscillator extends HarmonicOscillator where
  /-- The damping coefficient of the oscillator. -/
  γ : ℝ
  /-- The damping coefficient is nonnegative. -/
  γ_nonneg : 0 ≤ γ

namespace DampedHarmonicOscillator

variable (S : DampedHarmonicOscillator)

/-!
The mass/spring nonzero lemmas, the natural angular frequency, and the undamped energy API
are inherited from `HarmonicOscillator`.
-/

/-!

## B. The equation of motion and energy dissipation

### B.1. The equation of motion

-/

/-- The equation of motion for the damped harmonic oscillator:
`m ẍ + γ ẋ + k x = 0`. -/
noncomputable def EquationOfMotion (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ∀ t : Time, S.m • ∂ₜ (∂ₜ xₜ) t + S.γ • ∂ₜ xₜ t + S.k • xₜ t = 0

/-!

### B.2. Energy dissipation

The damped oscillator inherits the mechanical energy from the undamped harmonic oscillator.
Along a solution of the damped equation of motion, that energy decreases at a rate
proportional to `-γ ‖ẋ‖^2`.

-/

/-- The instantaneous energy dissipation rate along a trajectory. -/
noncomputable def energyDissipationRate (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ :=
  fun t => - S.γ * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ

/-- Along a smooth solution of the damped equation of motion, the derivative of the
mechanical energy is `-γ ‖ẋ‖^2`. -/
lemma energy_dissipation_rate (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : S.EquationOfMotion xₜ)
    (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (S.energy xₜ) t = - S.γ * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ := by
  rw [S.energy_deriv xₜ hx]
  simp only
  have heom := h1 t
  have hforce : S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t = - S.γ • ∂ₜ xₜ t := by
    have hsum : (S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t) + S.γ • ∂ₜ xₜ t = 0 := by
      simpa [add_assoc, add_left_comm, add_comm] using heom
    simpa [neg_smul] using eq_neg_of_add_eq_zero_left hsum
  rw [hforce]
  simp [inner_smul_right]

/-- If `γ > 0` and the velocity is nonzero at a time, the mechanical energy is strictly
decreasing at that time. -/
lemma energy_not_conserved (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time)
    (h1 : S.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ) (hdx : ∂ₜ xₜ t ≠ 0) (hγ : 0 < S.γ) :
    ∂ₜ (S.energy xₜ) t < 0 := by
  rw [energy_dissipation_rate S xₜ t h1 hx]
  rw [neg_mul]
  exact neg_neg_of_pos (mul_pos hγ (real_inner_self_pos.mpr hdx))

/-!
## C. Newton's second law

We define the force of the damped oscillator, and show that the equation of
motion is equivalent to Newton's second law.

-/

/-!

### C.1. The force

We define the force of the damped oscillator as `- k x - γ v`.

-/

/-- The force of the damped harmonic oscillator at a given position and time. -/
noncomputable def force (S : DampedHarmonicOscillator)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    EuclideanSpace ℝ (Fin 1) := - S.k • xₜ t - S.γ • ∂ₜ xₜ t

/-!


### C.2. Equation of motion if and only if Newton's second law

We show that the equation of motion is equivalent to Newton's second law.

-/

lemma equationOfMotion_iff_newtons_2nd_law (xₜ : Time → EuclideanSpace ℝ (Fin 1)):
    S.EquationOfMotion xₜ ↔
    (∀ t : Time, S.m • ∂ₜ (∂ₜ xₜ) t = force S xₜ t) := by
  simp only [EquationOfMotion, force]
  constructor
  · intro h t
    have h' :
        S.m • ∂ₜ (∂ₜ xₜ) t + (S.γ • ∂ₜ xₜ t + S.k • xₜ t) = 0 := by
      simpa [add_assoc] using h t
    have ha :
        S.m • ∂ₜ (∂ₜ xₜ) t = -(S.γ • ∂ₜ xₜ t + S.k • xₜ t) :=
      eq_neg_of_add_eq_zero_left h'
    simpa [sub_eq_add_neg, neg_add, add_comm] using ha
  · intro h t
    rw [h t]
    module

/-!
## D. Damping regimes

The sign of the discriminant `γ^2 - 4 * m * k` separates the underdamped, critically
damped, and overdamped regimes. We also define the decay rate and the real frequencies
that appear in the explicit solution formulas.

-/

/-- The discriminant that determines the damping regime. -/
noncomputable def discriminant : ℝ := S.γ^2 - 4 * S.m * S.k

/-- The exponential decay rate `γ / (2 * m)`. -/
noncomputable def decay_rate : ℝ := S.γ / (2 * S.m)

/-- The oscillation frequency in the underdamped regime. -/
noncomputable def underdampedAngularFrequency : ℝ := sqrt (- S.discriminant) / (2 * S.m)

/-- The real split rate between the two roots in the overdamped regime. -/
noncomputable def overdampedSplitRate : ℝ := sqrt S.discriminant / (2 * S.m)

/-- The system is underdamped when γ² < 4mk. -/
def IsUnderdamped : Prop := S.discriminant < 0

/-- The system is critically damped when γ² = 4mk. -/
def IsCriticallyDamped : Prop := S.discriminant = 0

/-- The system is overdamped when γ² > 4mk. -/
def IsOverdamped : Prop := S.discriminant > 0

/-- The system is undamped when γ = 0. -/
def IsUndamped : Prop := S.γ = 0

/-- The relationship between the discriminant, decay rate, and natural angular frequency. -/
lemma discriminant_eq_four_mul_m_sq_mul_decay_rate_sq_sub_ω_sq :
    S.discriminant = 4 * S.m^2 * (S.decay_rate^2 - S.ω^2) := by
  rw [discriminant, decay_rate, S.ω_sq]
  field_simp [S.m_ne_zero]
  ring

/-- The decay rate is nonnegative. -/
lemma decay_rate_nonneg : 0 ≤ S.decay_rate := by
  rw [decay_rate]
  exact div_nonneg S.γ_nonneg (by nlinarith [S.m_pos])

/-- An undamped oscillator lies in the underdamped regime. -/
lemma isUnderdamped_of_gamma_eq_zero (hγ : S.γ = 0) : S.IsUnderdamped := by
  rw [IsUnderdamped, discriminant_eq_four_mul_m_sq_mul_decay_rate_sq_sub_ω_sq S, decay_rate]
  rw [hγ]
  ring_nf
  nlinarith [sq_pos_of_pos S.m_pos, sq_pos_of_pos S.ω_pos]

/-- An underdamped system has decay rate less than the natural frequency. -/
lemma isUnderdamped_decay_rate (hS : S.IsUnderdamped) : S.ω > S.decay_rate := by
  rw [IsUnderdamped] at hS
  rw [discriminant_eq_four_mul_m_sq_mul_decay_rate_sq_sub_ω_sq] at hS
  have hm_sq_pos : 0 < 4 * S.m^2 := by
    have hsq : 0 < S.m^2 := sq_pos_of_pos S.m_pos
    nlinarith
  have hsq : S.decay_rate^2 < S.ω^2 := by
    nlinarith
  nlinarith [S.decay_rate_nonneg, S.ω_pos]

/-- A critically damped system has decay rate equal to the natural frequency. -/
lemma isCriticallyDamped_decay_rate (hS : S.IsCriticallyDamped) : S.ω = S.decay_rate := by
  rw [IsCriticallyDamped] at hS
  rw [discriminant_eq_four_mul_m_sq_mul_decay_rate_sq_sub_ω_sq] at hS
  have hm_sq_ne_zero : 4 * S.m^2 ≠ 0 := by
    have hm_sq_pos : 0 < 4 * S.m^2 := by
      have hsq : 0 < S.m^2 := sq_pos_of_pos S.m_pos
      nlinarith
    exact ne_of_gt hm_sq_pos
  have hsq : S.decay_rate^2 = S.ω^2 := by
    have hsub : S.decay_rate^2 - S.ω^2 = 0 := by
      exact (mul_eq_zero.mp hS).resolve_left hm_sq_ne_zero
    linarith
  nlinarith [S.decay_rate_nonneg, S.ω_pos]

/-- An overdamped system has decay rate greater than the natural frequency. -/
lemma isOverdamped_decay_rate (hS : S.IsOverdamped) : S.ω < S.decay_rate := by
  rw [IsOverdamped] at hS
  rw [discriminant_eq_four_mul_m_sq_mul_decay_rate_sq_sub_ω_sq] at hS
  have hm_sq_pos : 0 < 4 * S.m^2 := by
    have hsq : 0 < S.m^2 := sq_pos_of_pos S.m_pos
    nlinarith
  have hsq : S.ω^2 < S.decay_rate^2 := by
    nlinarith
  nlinarith [S.decay_rate_nonneg, S.ω_pos]

/-- In the underdamped regime, the damped angular frequency squares to `ω^2 - decay_rate^2`. -/
lemma underdampedAngularFrequency_sq (hS : S.IsUnderdamped) :
    S.underdampedAngularFrequency^2 = S.ω^2 - S.decay_rate^2 := by
  rw [underdampedAngularFrequency, div_pow, sq_sqrt]
  · rw [discriminant_eq_four_mul_m_sq_mul_decay_rate_sq_sub_ω_sq]
    field_simp [S.m_ne_zero]
    ring
  · rw [IsUnderdamped] at hS
    exact le_of_lt (neg_pos.mpr hS)

/-- The underdamped angular frequency is positive in the underdamped regime. -/
lemma underdampedAngularFrequency_pos (hS : S.IsUnderdamped) :
    0 < S.underdampedAngularFrequency := by
  rw [underdampedAngularFrequency]
  apply div_pos
  · rw [IsUnderdamped] at hS
    exact sqrt_pos.mpr (neg_pos.mpr hS)
  · nlinarith [S.m_pos]

/-- The underdamped angular frequency is nonzero in the underdamped regime. -/
lemma underdampedAngularFrequency_ne_zero (hS : S.IsUnderdamped) :
    S.underdampedAngularFrequency ≠ 0 :=
  Ne.symm (ne_of_lt (S.underdampedAngularFrequency_pos hS))

/-- In the overdamped regime, the split rate squares to `decay_rate^2 - ω^2`. -/
lemma overdampedSplitRate_sq (hS : S.IsOverdamped) :
    S.overdampedSplitRate^2 = S.decay_rate^2 - S.ω^2 := by
  rw [overdampedSplitRate, div_pow, sq_sqrt]
  · rw [discriminant_eq_four_mul_m_sq_mul_decay_rate_sq_sub_ω_sq]
    field_simp [S.m_ne_zero]
    ring
  · rw [IsOverdamped] at hS
    exact le_of_lt hS

/-- The overdamped split rate is positive in the overdamped regime. -/
lemma overdampedSplitRate_pos (hS : S.IsOverdamped) : 0 < S.overdampedSplitRate := by
  rw [overdampedSplitRate]
  apply div_pos
  · rw [IsOverdamped] at hS
    exact sqrt_pos.mpr hS
  · nlinarith [S.m_pos]

/-- The overdamped split rate is nonzero in the overdamped regime. -/
lemma overdampedSplitRate_ne_zero (hS : S.IsOverdamped) : S.overdampedSplitRate ≠ 0 :=
  Ne.symm (ne_of_lt (S.overdampedSplitRate_pos hS))

/-!
## E. To undamped oscillator

We show that the damped harmonic oscillator reduces to the undamped harmonic oscillator when the
damping coefficient is zero. The underlying mass and spring data are already inherited from
`HarmonicOscillator`; the proof argument records that this conversion is being used only in
the zero-damping case.

We also show that the equations of motion are equivalent in this case.
-/

/-- Convert a damped oscillator to its underlying undamped oscillator when `γ = 0`. -/
def toUndamped (S : DampedHarmonicOscillator) (_hS : S.IsUndamped) :
    HarmonicOscillator :=
  S.toHarmonicOscillator

/-- When `γ = 0`, the damped equation of motion is equivalent to the equation of motion
for the corresponding undamped harmonic oscillator. -/
lemma toUndamped_equationOfMotion (S : DampedHarmonicOscillator) (hS : S.IsUndamped)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔ (S.toUndamped hS).EquationOfMotion xₜ := by
  have hγ : S.γ = 0 := by
    simpa [IsUndamped] using hS
  rw [S.equationOfMotion_iff_newtons_2nd_law xₜ,
    (S.toUndamped hS).equationOfMotion_iff_newtons_2nd_law xₜ hx]
  constructor
  · intro h t
    calc
      (S.toUndamped hS).m • ∂ₜ (∂ₜ xₜ) t = S.m • ∂ₜ (∂ₜ xₜ) t := rfl
      _ = force S xₜ t := h t
      _ = HarmonicOscillator.force (S.toUndamped hS) (xₜ t) := by
        simp [force, HarmonicOscillator.force_eq_linear, toUndamped, hγ]
  · intro h t
    calc
      S.m • ∂ₜ (∂ₜ xₜ) t = (S.toUndamped hS).m • ∂ₜ (∂ₜ xₜ) t := rfl
      _ = HarmonicOscillator.force (S.toUndamped hS) (xₜ t) := h t
      _ = force S xₜ t := by
        simp [force, HarmonicOscillator.force_eq_linear, toUndamped, hγ]


end DampedHarmonicOscillator

end ClassicalMechanics
