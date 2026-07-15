/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Data.Nat.Factorial.Basic
/-!

# Temperate growth of an affine resolvent reciprocal

## i. Overview

For `z : ℂ` with `z.im ≠ 0` and `a : ℝ`, the affine function `t ↦ z + a·t` never vanishes.
Consequently, its reciprocal is smooth and globally bounded by `|z.im|⁻¹`, and its iterated
derivatives have the closed form `(-1)ⁿ · n! · aⁿ · (reciprocal)ⁿ⁺¹`.

## ii. Key results

- `resolventRecip_norm_le` : the reciprocal is globally bounded by `|z.im|⁻¹`.
- `iteratedDeriv_resolventRecip` : the closed form
    `iteratedDeriv n (resolventRecip a z) = (-1)ⁿ · n! · aⁿ · (resolventRecip a z)ⁿ⁺¹`.
- `resolventRecip_hasTemperateGrowth` : the reciprocal has temperate growth.

## iii. Table of contents

- A. The affine resolvent reciprocal
- B. Bounded derivatives and temperate growth

## iv. References

-/

@[expose] public section

open scoped ContDiff Nat

namespace Physlib.Distribution

variable {z : ℂ}

/-!
## A. The affine resolvent reciprocal
-/

/-- The single-real-variable reciprocal symbol `t ↦ (z + a·t)⁻¹`. -/
noncomputable def resolventRecip (a : ℝ) (z : ℂ) : ℝ → ℂ := fun t => (z + (a : ℂ) * (t : ℂ))⁻¹

/-- The symbol's denominator has imaginary part exactly `z.im`. -/
lemma resolventRecip_den_im (a t : ℝ) : (z + (a : ℂ) * (t : ℂ)).im = z.im := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_mul, add_zero]

/-- When `z.im ≠ 0` the denominator `z + a·t` never vanishes. -/
lemma resolventRecip_den_ne_zero (hz : z.im ≠ 0) (a t : ℝ) : z + (a : ℂ) * (t : ℂ) ≠ 0 :=
  fun h => hz <| by rw [← resolventRecip_den_im (z := z) a t, h, Complex.zero_im]

/-- `resolventRecip a z` is smooth (`ContDiff ℝ ∞`). -/
lemma resolventRecip_contDiff (hz : z.im ≠ 0) (a : ℝ) : ContDiff ℝ ∞ (resolventRecip a z) :=
  (contDiff_const.add (contDiff_const.mul Complex.ofRealCLM.contDiff)).inv
    (resolventRecip_den_ne_zero hz a)

/-- The derivative of `resolventRecip a z` is `-a · (resolventRecip a z)²`. -/
lemma resolventRecip_hasDerivAt (hz : z.im ≠ 0) (a t : ℝ) :
    HasDerivAt (resolventRecip a z) (-(a : ℂ) * (resolventRecip a z t) ^ 2) t := by
  have haff : HasDerivAt (fun s : ℝ => z + (a : ℂ) * (s : ℂ)) (a : ℂ) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (a : ℂ)).const_add z
  have hcomp : HasDerivAt (resolventRecip a z) (-((z + (a : ℂ) * (t : ℂ)) ^ 2)⁻¹ * (a : ℂ)) t :=
    (hasDerivAt_inv (resolventRecip_den_ne_zero hz a t)).comp t haff
  simpa [resolventRecip, inv_pow, neg_mul, mul_comm] using hcomp

/-!
## B. Bounded derivatives and temperate growth
-/

/-- Closed form for the iterated derivatives of `resolventRecip a z`: the `n`-th derivative is
`(-1)ⁿ · n! · aⁿ · (resolventRecip a z) ^ (n + 1)`. -/
lemma iteratedDeriv_resolventRecip (hz : z.im ≠ 0) (a : ℝ) (n : ℕ) :
    iteratedDeriv n (resolventRecip a z)
      = fun t => (-1) ^ n * (n ! : ℂ) * (a : ℂ) ^ n * resolventRecip a z t ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext t
    have hd := ((resolventRecip_hasDerivAt hz a t).pow (n + 1)).const_mul
      ((-1) ^ n * (n ! : ℂ) * (a : ℂ) ^ n)
    simp only [Pi.pow_apply] at hd
    rw [iteratedDeriv_succ, ih, hd.deriv]
    push_cast [Nat.factorial_succ]
    ring

/-- `resolventRecip a z` maps into the closed ball of radius `|z.im|⁻¹`. -/
lemma resolventRecip_norm_le (hz : z.im ≠ 0) (a t : ℝ) : ‖resolventRecip a z t‖ ≤ |z.im|⁻¹ := by
  rw [resolventRecip, norm_inv]
  exact inv_anti₀ (abs_pos.mpr hz)
    (resolventRecip_den_im (z := z) a t ▸ Complex.abs_im_le_norm (z + (a : ℂ) * (t : ℂ)))

/-- Every iterated derivative of `resolventRecip a z` is globally bounded, explicitly by
`n! · |a|ⁿ · |z.im|⁻¹ ^ (n + 1)`. -/
lemma isBounded_range_iteratedDeriv_resolventRecip (hz : z.im ≠ 0) (a : ℝ) (n : ℕ) :
    Bornology.IsBounded (Set.range (iteratedDeriv n (resolventRecip a z))) := by
  refine isBounded_iff_forall_norm_le.mpr ⟨(n ! : ℝ) * |a| ^ n * |z.im|⁻¹ ^ (n + 1), ?_⟩
  rintro _ ⟨t, rfl⟩
  rw [iteratedDeriv_resolventRecip hz a n]
  have hnorm : ‖(-1 : ℂ) ^ n * (n ! : ℂ) * (a : ℂ) ^ n * resolventRecip a z t ^ (n + 1)‖
      = (n ! : ℝ) * |a| ^ n * ‖resolventRecip a z t‖ ^ (n + 1) := by
    simp only [Complex.norm_mul, norm_pow, norm_neg, norm_one, one_pow, RCLike.norm_natCast,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  gcongr
  exact resolventRecip_norm_le hz a t

/-- `resolventRecip a z` has temperate growth. -/
lemma resolventRecip_hasTemperateGrowth (hz : z.im ≠ 0) (a : ℝ) :
    Function.HasTemperateGrowth (resolventRecip a z) := by
  refine ⟨resolventRecip_contDiff hz a, fun n => ?_⟩
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp (isBounded_range_iteratedDeriv_resolventRecip hz a n)
  refine ⟨0, C, fun t => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, pow_zero, mul_one]
  exact hC _ (Set.mem_range_self t)

end Physlib.Distribution
