/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!

# The complete elliptic integral of the first kind

This file may eventually be upstreamed to Mathlib.

## i. Overview

Legendre's complete elliptic integral of the first kind is, in the parameter convention,

`K(m) = ∫ φ in 0..π/2, (1 - m sin² φ) ^ (-1/2)`

(Abramowitz & Stegun 17.3.1). The physics literature more often uses the modulus convention and
writes `K(k)`, as Landau & Lifshitz do, for what is here `completeEllipticK (k ^ 2)`; the two
conventions are related by `m = k²`. Mathlib knows the Weierstrass elliptic function `℘`
(`PeriodPair.weierstrassP`) but has no Legendre-form elliptic integrals; this file defines the
complete integral of the first kind and develops its basic theory on the domain `m < 1`, where
the radicand `1 - m sin² φ` is positive and the integrand continuous.

The integral enters physics wherever a period or a potential is computed exactly rather than in a
small-parameter expansion. Physlib's use of it so far is the simple pendulum: released from rest
at amplitude `θ₀`, the pendulum has period `4 √(ℓ / g) K(sin² (θ₀ / 2))` (Landau & Lifshitz §11,
Problem 1), the consumer being `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.PeriodFormula`.
More broadly, the complete integrals of the first and second kind give the magnetic field of a
circular current loop and the potential of a uniformly charged ring, and the second kind, `E`,
gives the arc length of an ellipse. This file defines `K` so that such results can be stated.

For `m ≥ 1` the definition still elaborates, but its value is not Legendre's. At `m = 1` the
integrand is `1 / cos φ`, which is not interval integrable on `[0, π/2]`, so the integral is `0`
by `intervalIntegral.integral_undef`, whereas `K(1) = ∞`. For `m > 1` the radicand is negative on
`(arcsin (1/√m), π/2]`, where the real power at exponent `-(1/2)` of a negative base vanishes
(`Real.rpow_def_of_neg` supplies the factor `cos (-(1 / 2) * π) = 0`), so the Lean value is the
finite positive integral over `[0, arcsin (1/√m)]`; by the reciprocal-modulus transformation this
is `K(1/m) / √m`, the real part of the complex Legendre integral (DLMF §19.7(ii)) — not proved
here. Every lemma of this file about a general parameter therefore carries its domain hypothesis
`m < 1` explicitly.

## ii. Key results

- `completeEllipticK` : the complete elliptic integral of the first kind, as a function of
  the parameter `m`.
- `completeEllipticK_zero` : `K 0 = π / 2`.
- `completeEllipticK_pos` : for `m < 1` the integral is positive.
- `completeEllipticK_mono` : for `m₁ ≤ m₂ < 1`, `K m₁ ≤ K m₂`.
- `completeEllipticK_strictMono` : for `m₁ < m₂ < 1`, `K m₁ < K m₂`.
- `pi_div_two_le_completeEllipticK` : for `0 ≤ m < 1`, `π / 2 ≤ K m`.
- `completeEllipticK_le` : for `0 ≤ m < 1`, `K m ≤ π / 2 * (1 - m) ^ (-1/2)`.
- `continuousOn_completeEllipticK` : `K` is continuous on `(-∞, 1)`.
- `continuousAt_completeEllipticK` : `K` is continuous at every `m < 1`.

## iii. Table of contents

- A. Definition and the integrand
- B. Value at zero and positivity
- C. Monotonicity and bounds in the parameter
- D. Continuity on the domain

## iv. References

- M. Abramowitz, I. A. Stegun, Handbook of Mathematical Functions, §17.3 (the parameter
  convention, 17.3.1).
- NIST DLMF §19.7(ii) (the reciprocal-modulus transformation).
- Landau & Lifshitz, Mechanics, 3rd ed., §11, Problem 1 (the pendulum period as `K(k)`, modulus
  convention).

-/

@[expose] public section

open MeasureTheory

namespace Real

/-!

## A. Definition and the integrand

The integral is defined for every real parameter `m`; on the domain `m < 1` the radicand is
positive, so the integrand is continuous and interval integrable.

-/

/-- The complete elliptic integral of the first kind in the parameter convention,
`K(m) = ∫ φ in 0..π/2, (1 - m sin² φ) ^ (-1/2)`. The physics literature often writes `K(k)`
with `m = k²`. The integrand is written as a real power rather than `1 / √(…)` so that
continuity, positivity and monotonicity in `m` come from the `rpow` API (`Continuous.rpow_const`,
`Real.rpow_pos_of_pos`, `Real.rpow_le_rpow_of_nonpos`); the two forms agree by
`Real.sqrt_eq_rpow` and `Real.rpow_neg`. For `m ≥ 1` see the module docstring. -/
@[pp_nodot]
noncomputable def completeEllipticK (m : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..π / 2, (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ))

/-- Unfolding lemma: `completeEllipticK m` is the interval integral of its integrand over
`[0, π/2]`. -/
lemma completeEllipticK_def (m : ℝ) :
    completeEllipticK m = ∫ φ in (0 : ℝ)..π / 2, (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ)) :=
  rfl

/-- For `m < 1` the radicand `1 - m sin² φ` of the integrand of `completeEllipticK m` is
positive at every angle `φ`. -/
lemma completeEllipticK_radicand_pos {m : ℝ} (hm : m < 1) (φ : ℝ) :
    0 < 1 - m * sin φ ^ 2 := by
  nlinarith [sq_nonneg (sin φ), sin_sq_le_one φ,
    mul_nonneg (sub_nonneg.2 hm.le) (sq_nonneg (sin φ))]

/-- For `m < 1` the integrand of `completeEllipticK m` is continuous, the real power being
taken at a positive base. -/
lemma continuous_completeEllipticK_integrand {m : ℝ} (hm : m < 1) :
    Continuous fun φ : ℝ => (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  refine Continuous.rpow_const ?_ fun φ => Or.inl (completeEllipticK_radicand_pos hm φ).ne'
  fun_prop

/-- For `m < 1` the integrand of `completeEllipticK m` is interval integrable on `[0, π/2]`. -/
lemma intervalIntegrable_completeEllipticK_integrand {m : ℝ} (hm : m < 1) :
    IntervalIntegrable (fun φ : ℝ => (1 - m * sin φ ^ 2) ^ (-(1 / 2 : ℝ))) volume 0 (π / 2) :=
  (continuous_completeEllipticK_integrand hm).intervalIntegrable 0 (π / 2)

/-!

## B. Value at zero and positivity

At `m = 0` the integrand is the constant `1` and the integral is elementary; for `m < 1` the
integral is positive, being the integral of a positive continuous function.

-/

/-- `K 0 = π / 2`: at parameter zero the integrand of `completeEllipticK` is the constant `1`. -/
@[simp]
lemma completeEllipticK_zero : completeEllipticK 0 = π / 2 := by
  simp [completeEllipticK]

/-- For `m < 1` the complete elliptic integral `completeEllipticK m` is positive. -/
lemma completeEllipticK_pos {m : ℝ} (hm : m < 1) : 0 < completeEllipticK m := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_completeEllipticK_integrand hm) (fun φ _ => ?_) pi_div_two_pos
  exact rpow_pos_of_pos (completeEllipticK_radicand_pos hm φ) _

/-!

## C. Monotonicity and bounds in the parameter

For fixed `φ` the radicand `1 - m sin² φ` decreases in `m`, so the integrand, a negative power of
the radicand, increases in `m` on the domain; integrating the pointwise inequality over
`[0, π/2]` gives monotonicity of `K`, and since the inequality is strict at `φ = π/2` the
monotonicity is strict. Together with `K 0 = π / 2` this bounds `K` below on `[0, 1)`; bounding
the radicand below by `1 - m` bounds `K` above by `π / 2 * (1 - m) ^ (-1/2)` there.

-/

/-- `completeEllipticK` is monotone on its domain: for `m₁ ≤ m₂ < 1`, `K m₁ ≤ K m₂`. The
integrand is pointwise monotone in the parameter, the radicand being positive for both
parameters. -/
@[gcongr]
lemma completeEllipticK_mono {m₁ m₂ : ℝ} (h12 : m₁ ≤ m₂) (h2 : m₂ < 1) :
    completeEllipticK m₁ ≤ completeEllipticK m₂ := by
  have h1 : m₁ < 1 := h12.trans_lt h2
  refine intervalIntegral.integral_mono_on pi_div_two_pos.le
    (intervalIntegrable_completeEllipticK_integrand h1)
    (intervalIntegrable_completeEllipticK_integrand h2)
    fun φ _ => ?_
  exact rpow_le_rpow_of_nonpos (completeEllipticK_radicand_pos h2 φ)
    (sub_le_sub_left (mul_le_mul_of_nonneg_right h12 (sq_nonneg _)) 1) (by norm_num)

/-- `completeEllipticK` is monotone on its domain `(-∞, 1)`, as a `MonotoneOn` statement. -/
lemma monotoneOn_completeEllipticK : MonotoneOn completeEllipticK (Set.Iio 1) :=
  fun _ _ _ hm₂ h => completeEllipticK_mono h hm₂

/-- `completeEllipticK` is strictly monotone on its domain: for `m₁ < m₂ < 1`, `K m₁ < K m₂`.
The pointwise inequality between the integrands is strict at `φ = π / 2`, where `sin² φ = 1`. -/
@[gcongr]
lemma completeEllipticK_strictMono {m₁ m₂ : ℝ} (h12 : m₁ < m₂) (h2 : m₂ < 1) :
    completeEllipticK m₁ < completeEllipticK m₂ := by
  have h1 : m₁ < 1 := h12.trans h2
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt pi_div_two_pos
    (continuous_completeEllipticK_integrand h1).continuousOn
    (continuous_completeEllipticK_integrand h2).continuousOn
    (fun φ _ => ?_) ⟨π / 2, Set.right_mem_Icc.2 pi_div_two_pos.le, ?_⟩
  · exact rpow_le_rpow_of_nonpos (completeEllipticK_radicand_pos h2 φ)
      (sub_le_sub_left (mul_le_mul_of_nonneg_right h12.le (sq_nonneg _)) 1) (by norm_num)
  · simp only [sin_pi_div_two, one_pow, mul_one]
    exact rpow_lt_rpow_of_neg (by linarith) (by linarith) (by norm_num)

/-- `completeEllipticK` is strictly increasing on `(-∞, 1)`, as a bundled `StrictMonoOn`. -/
lemma strictMonoOn_completeEllipticK : StrictMonoOn completeEllipticK (Set.Iio 1) :=
  fun _ _ _ hm₂ h => completeEllipticK_strictMono h hm₂

/-- For `0 ≤ m < 1` the complete elliptic integral `completeEllipticK m` is at least its value
`π / 2` at `m = 0`. -/
lemma pi_div_two_le_completeEllipticK {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    π / 2 ≤ completeEllipticK m := by
  rw [← completeEllipticK_zero]
  exact completeEllipticK_mono hm0 hm1

/-- For `0 ≤ m < 1` the complete elliptic integral `completeEllipticK m` is at most
`π / 2 * (1 - m) ^ (-1/2)`: the radicand is at least `1 - m`, `sin² φ` being at most `1`, so the
integrand is at most the constant `(1 - m) ^ (-1/2)`. With `pi_div_two_le_completeEllipticK` this
sandwiches `K` on `[0, 1)`; for the pendulum, where `m = sin² (θ₀ / 2)`, it bounds the period by
`T ≤ 2π √(ℓ / g) / cos (θ₀ / 2)`. -/
lemma completeEllipticK_le {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    completeEllipticK m ≤ π / 2 * (1 - m) ^ (-(1 / 2 : ℝ)) := by
  have h : completeEllipticK m ≤ ∫ _ in (0 : ℝ)..π / 2, (1 - m) ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_mono_on pi_div_two_pos.le
      (intervalIntegrable_completeEllipticK_integrand hm1) intervalIntegrable_const
      fun φ _ => ?_
    exact rpow_le_rpow_of_nonpos (by linarith)
      (sub_le_sub_left (mul_le_of_le_one_right hm0 (sin_sq_le_one φ)) 1) (by norm_num)
  rwa [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h

/-!

## D. Continuity on the domain

The integrand is jointly continuous in `(m, φ)` on `(-∞, 1) × ℝ`, where the radicand is
positive, but not on all of `ℝ × ℝ`. Restricting the parameter to the subtype `Set.Iio 1` makes
the joint continuity global, so Mathlib's continuity of a parametric interval integral with
fixed endpoints (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`)
applies and gives continuity of `K` on the domain. Continuity at each point `m < 1` follows,
`(-∞, 1)` being a neighbourhood of `m`.

-/

/-- `completeEllipticK` is continuous on its domain `(-∞, 1)`. -/
lemma continuousOn_completeEllipticK : ContinuousOn completeEllipticK (Set.Iio 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hf : Continuous fun p : Set.Iio (1 : ℝ) × ℝ =>
      (1 - p.1.1 * sin p.2 ^ 2) ^ (-(1 / 2 : ℝ)) := by
    refine Continuous.rpow_const ?_ fun p => Or.inl (completeEllipticK_radicand_pos p.1.2 p.2).ne'
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    -- `f` must be named: higher-order unification cannot recover it from `Continuous f.uncurry`.
    (f := fun (m : Set.Iio (1 : ℝ)) (φ : ℝ) => (1 - m.1 * sin φ ^ 2) ^ (-(1 / 2 : ℝ)))
    hf 0 (π / 2)

/-- `completeEllipticK` is continuous at every point `m < 1` of its domain, `(-∞, 1)` being a
neighbourhood of `m`. -/
lemma continuousAt_completeEllipticK {m : ℝ} (hm : m < 1) : ContinuousAt completeEllipticK m :=
  continuousOn_completeEllipticK.continuousAt (Iio_mem_nhds hm)

/-- `completeEllipticK` is continuous at `m = 0`, an interior point of its domain `(-∞, 1)`. -/
lemma continuousAt_completeEllipticK_zero : ContinuousAt completeEllipticK 0 :=
  continuousAt_completeEllipticK zero_lt_one

end Real
