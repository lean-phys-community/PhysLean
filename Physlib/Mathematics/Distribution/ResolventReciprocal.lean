/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Data.Nat.Factorial.Basic
/-!

# Temperate growth of the resolvent of a non-real complex number

## i. Overview

For `z : ℂ` with `z.im ≠ 0`, every real number lies in the `ℝ`-resolvent set of `z`, so
Mathlib's algebra resolvent `resolvent (R := ℝ) z = fun t : ℝ ↦ Ring.inverse (↑t - z)` is a
globally defined, smooth map `ℝ → ℂ`. Its derivative comes from the Banach-algebra resolvent
theory, its iterated derivatives have the closed form `(-1)ⁿ · n! · (resolvent z)ⁿ⁺¹`, and it
is globally bounded by `|z.im|⁻¹`; consequently it has temperate growth.

The affine reciprocal `t ↦ (z + a·t)⁻¹` used by the momentum-resolvent development is the
composition of `resolvent (-z)` with scaling by `a`, so its temperate growth follows by
composition.

## ii. Key results

- `mem_resolventSet_of_im_ne_zero` / `resolventSet_eq_univ` : every `t : ℝ` lies in
    `resolventSet ℝ z` when `z.im ≠ 0`, i.e. `t - z` is invertible for all real `t`.
- `hasDerivAt_resolvent` : `resolvent (R := ℝ) z` has derivative `-(resolvent z t)²`,
    from Mathlib's `spectrum.hasDerivAt_resolvent_const_left`.
- `iteratedDeriv_resolvent` : the closed form
    `iteratedDeriv n (resolvent z) = (-1)ⁿ · n! · (resolvent z)ⁿ⁺¹`.
- `norm_resolvent_le` : the global bound `‖resolvent z t‖ ≤ |z.im|⁻¹`.
- `hasTemperateGrowth_resolvent` : `resolvent (R := ℝ) z` has temperate growth.
- `hasTemperateGrowth_affine_inv` : the affine reciprocal `t ↦ (z + a·t)⁻¹` has temperate
    growth, as `resolvent (-z)` composed with scaling.

## iii. Table of contents

- A. The resolvent of a non-real complex number along `ℝ`
- B. The affine reciprocal as a composed resolvent

## iv. References

-/

@[expose] public section

open scoped ContDiff Nat

namespace Physlib.Distribution

variable {z : ℂ}

/-!
## A. The resolvent of a non-real complex number along `ℝ`
-/

/-- Every real number lies in the `ℝ`-resolvent set of a non-real complex number:
`t - z` is invertible for all `t : ℝ`. -/
lemma mem_resolventSet_of_im_ne_zero (hz : z.im ≠ 0) (t : ℝ) : t ∈ resolventSet ℝ z := by
  rw [spectrum.mem_resolventSet_iff, isUnit_iff_ne_zero]
  intro h
  exact hz (by simpa using congrArg Complex.im h)

/-- The `ℝ`-resolvent set of a non-real complex number is all of `ℝ`. -/
lemma resolventSet_eq_univ (hz : z.im ≠ 0) : resolventSet ℝ z = Set.univ :=
  Set.eq_univ_of_forall (mem_resolventSet_of_im_ne_zero hz)

/-- The resolvent of `z : ℂ` along `ℝ` is the concrete reciprocal `t ↦ (t - z)⁻¹`. -/
lemma resolvent_apply (z : ℂ) (t : ℝ) : resolvent z t = ((t : ℂ) - z)⁻¹ := by
  rw [resolvent, Ring.inverse_eq_inv]
  norm_num

/-- The resolvent is globally bounded by `|z.im|⁻¹`: the imaginary part of the denominator
`t - z` is exactly `-z.im`. -/
lemma norm_resolvent_le (hz : z.im ≠ 0) (t : ℝ) : ‖resolvent z t‖ ≤ |z.im|⁻¹ := by
  rw [resolvent_apply, norm_inv]
  refine inv_anti₀ (abs_pos.mpr hz) ?_
  have him : ((t : ℂ) - z).im = -z.im := by simp
  calc |z.im| = |((t : ℂ) - z).im| := by rw [him, abs_neg]
    _ ≤ ‖(t : ℂ) - z‖ := Complex.abs_im_le_norm _

/-- The derivative of the resolvent is `-(resolvent z t)²`, an instance of Mathlib's
Banach-algebra resolvent theory. -/
lemma hasDerivAt_resolvent (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (resolvent z) (-resolvent z t ^ 2) t :=
  spectrum.hasDerivAt_resolvent_const_left (mem_resolventSet_of_im_ne_zero hz t)

/-- The resolvent of a non-real complex number is smooth along `ℝ`. -/
lemma contDiff_resolvent (hz : z.im ≠ 0) : ContDiff ℝ ∞ (resolvent (R := ℝ) z) := by
  have : resolvent (R := ℝ) z = fun t : ℝ ↦ ((t : ℂ) - z)⁻¹ := funext (resolvent_apply z)
  rw [this]
  refine (Complex.ofRealCLM.contDiff.sub contDiff_const).inv fun t ↦ ?_
  have := mem_resolventSet_of_im_ne_zero hz t
  rw [spectrum.mem_resolventSet_iff, isUnit_iff_ne_zero] at this
  simpa using this

/-- Closed form for the iterated derivatives of the resolvent: the `n`-th derivative is
`(-1)ⁿ · n! · (resolvent z)ⁿ⁺¹`. -/
lemma iteratedDeriv_resolvent (hz : z.im ≠ 0) (n : ℕ) :
    iteratedDeriv n (resolvent (R := ℝ) z)
      = fun t ↦ (-1) ^ n * (n ! : ℂ) * resolvent z t ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext t
    have hd := ((hasDerivAt_resolvent hz t).pow (n + 1)).const_mul ((-1) ^ n * (n ! : ℂ))
    simp only [Pi.pow_apply] at hd
    rw [iteratedDeriv_succ, ih, hd.deriv]
    push_cast [Nat.factorial_succ]
    ring

/-- Every iterated derivative of the resolvent is globally bounded, explicitly by
`n! · |z.im|⁻¹ ^ (n + 1)`. -/
lemma isBounded_range_iteratedDeriv_resolvent (hz : z.im ≠ 0) (n : ℕ) :
    Bornology.IsBounded (Set.range (iteratedDeriv n (resolvent (R := ℝ) z))) := by
  refine Bornology.IsBounded.subset (Metric.isBounded_closedBall
    (x := (0 : ℂ)) (r := (n ! : ℝ) * |z.im|⁻¹ ^ (n + 1))) ?_
  rintro _ ⟨t, rfl⟩
  rw [iteratedDeriv_resolvent hz n, Metric.mem_closedBall, dist_zero_right]
  calc ‖(-1 : ℂ) ^ n * (n ! : ℂ) * resolvent z t ^ (n + 1)‖
      = (n ! : ℝ) * ‖resolvent z t‖ ^ (n + 1) := by
        simp [norm_pow]
    _ ≤ (n ! : ℝ) * |z.im|⁻¹ ^ (n + 1) := by
        gcongr
        exact norm_resolvent_le hz t

/-- The resolvent of a non-real complex number has temperate growth along `ℝ`. -/
lemma hasTemperateGrowth_resolvent (hz : z.im ≠ 0) :
    Function.HasTemperateGrowth (resolvent (R := ℝ) z) := by
  refine ⟨contDiff_resolvent hz, fun n ↦ ?_⟩
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le
    (isBounded_range_iteratedDeriv_resolvent hz n)
  refine ⟨0, C, fun t ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, pow_zero, mul_one]
  exact hC _ (Set.mem_range_self t)

/-!
## B. The affine reciprocal as a composed resolvent
-/

/-- The affine reciprocal `t ↦ (z + a·t)⁻¹` is the resolvent of `-z` composed with
scaling by `a`. -/
lemma affine_inv_eq_resolvent_neg_comp (a : ℝ) (z : ℂ) :
    (fun t : ℝ ↦ (z + (a : ℂ) * (t : ℂ))⁻¹)
      = resolvent (R := ℝ) (-z) ∘ ⇑(ContinuousLinearMap.mul ℝ ℝ a) := by
  funext t
  simp only [Function.comp_apply, ContinuousLinearMap.mul_apply', resolvent_apply]
  push_cast
  rw [sub_neg_eq_add, add_comm]

/-- The affine reciprocal `t ↦ (z + a·t)⁻¹` has temperate growth, by composing the
resolvent of `-z` with the scaling map. -/
lemma hasTemperateGrowth_affine_inv (hz : z.im ≠ 0) (a : ℝ) :
    Function.HasTemperateGrowth (fun t : ℝ ↦ (z + (a : ℂ) * (t : ℂ))⁻¹) := by
  rw [affine_inv_eq_resolvent_neg_comp a z]
  exact (hasTemperateGrowth_resolvent (by simpa using hz)).comp
    (ContinuousLinearMap.hasTemperateGrowth _)

end Physlib.Distribution
