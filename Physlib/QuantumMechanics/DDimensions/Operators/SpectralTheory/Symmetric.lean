/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.Basic
/-!

# Spectral theory for symmetric operators

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Numerical range
- B. Regularity domain

## iv. References

-/

@[expose] public section

namespace LinearPMap
namespace IsSymmetric

open InnerProductSpace
open Complex
open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-!
## A. Numerical range
-/

/-- The projection of the numerical range onto the real axis. -/
def realNumericalRange (T : H →ₗ.[ℂ] H) : Set ℝ := re '' (Θ T)

@[inherit_doc realNumericalRange]
local notation "Θᵣₑ" => realNumericalRange

lemma realNumericalRange_eq (T : H →ₗ.[ℂ] H) : Θᵣₑ T = re '' Θ T := rfl

@[simp]
lemma realNumericalRange_neg (T : H →ₗ.[ℂ] H) : Θᵣₑ (-T) = -Θᵣₑ T := by
  ext
  simp [realNumericalRange_eq, neg_eq_iff_eq_neg]

variable {T : H →ₗ.[ℂ] H} (hT : T.IsSymmetric)
include hT

/-- The numerical range of a symmetric operator is contained in the real axis. -/
lemma im_eq_zero_of_mem_numericalRange {z : ℂ} (hz : z ∈ Θ T) : z.im = 0 := by
  obtain ⟨x, hx, hxz⟩ := hz
  simp only [← hT x x] at hxz
  exact conj_eq_iff_im.mp (hxz ▸ isSymmetric_iff_inner_map_self_real.mp hT x)

/-- The numerical range of a symmetric operator is contained in the real axis. -/
lemma numericalRange_subset : Θ T ⊆ ofReal '' univ := by
  intro z hz
  refine ⟨z.re, mem_univ _, ?_⟩
  rw [← re_add_im z]
  simp [hT.im_eq_zero_of_mem_numericalRange hz]

/-- The numerical range of a symmetric operator is equal to its projection onto the real axis. -/
lemma numericalRange_eq : Θ T = ofReal '' Θᵣₑ T := by
  ext z
  constructor
  · intro h
    obtain ⟨r, _, rfl⟩ := hT.numericalRange_subset h
    exact ⟨r, ⟨r, h, rfl⟩, rfl⟩
  · intro ⟨r, ⟨w, hw, hwr⟩, hrz⟩
    obtain ⟨s, _, rfl⟩ := hT.numericalRange_subset hw
    exact hrz ▸ (ofReal_re s ▸ hwr) ▸ hw

/-!
## B. Regularity domain
-/

/-- The regularity domain of a symmetric operator contains all complex numbers with non-zero
  imaginary part. -/
lemma mem_regularityDomain_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z ∈ T.regularityDomain := by
  refine ⟨|z.im|, abs_pos.mpr hz, fun x ↦ ?_⟩
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := norm_eq_sqrt_sq_add_sq z ▸ Real.sq_sqrt (by nlinarith)
  have h' : (⟪T x, x⟫_ℂ).im = 0 := conj_eq_iff_im.mp (isSymmetric_iff_inner_map_self_real.mp hT x)
  refine le_of_le_of_eq (b := ‖T x - z.re • x‖ ^ 2 + z.im ^ 2 * ‖x‖ ^ 2) ?_ ?_
  · simp [mul_pow]
  · simp [norm_sub_sq (𝕜 := ℂ), ← Complex.coe_smul, inner_smul_right, norm_smul, mul_pow,
      add_assoc, add_mul, h, h']

/-- The regularity domain of a symmetric operator contains all complex numbers with non-zero
  imaginary part. -/
lemma compl_ofReal_subset_regularityDomain : (ofReal '' univ)ᶜ ⊆ T.regularityDomain := by
  intro z hz
  refine hT.mem_regularityDomain_of_im_ne_zero ?_
  exact fun h ↦ hz ⟨z.re, mem_univ _, Eq.symm (Complex.ext rfl h)⟩

/-- If `m` is a lower bound on the numerical range then the regularity domain contains `(-∞,m)`. -/
lemma Iio_subset_regularityDomain {m : ℝ} (h : m ∈ lowerBounds (Θᵣₑ T)) :
    ofReal '' Iio m ⊆ T.regularityDomain := by
  intro z ⟨r, hr, hrz⟩
  refine ⟨m - r, sub_pos.mpr hr, fun x ↦ ?_⟩
  rcases eq_zero_or_neZero x with rfl | hx
  · simp
  · obtain ⟨s, hs, hs'⟩ := hT.numericalRange_eq ▸ mem_numericalRange hx.ne
    apply h at hs
    have hsr : r < s := lt_of_lt_of_le hr hs
    refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hx.ne)
    calc
      _ = (m - r) * ‖x‖ ^ 2 := by rw [mul_assoc, pow_two]
      _ ≤ (s - r) * ‖x‖ ^ 2 := by nlinarith
      _ = ‖s * ‖x‖ ^ 2 - r * ‖x‖ ^ 2‖ := by simp [← sub_mul, abs_of_pos, sub_pos, hsr]
      _ = ‖(s : ℂ) * ‖x‖ ^ 2 - r * ‖x‖ ^ 2‖ := by simp [← ofReal_pow, ← ofReal_mul, ← ofReal_sub]
      _ = ‖⟪↑x, T x⟫_ℂ - r * ‖x‖ ^ 2‖ := by simp [hs', mul_comm, hx.ne]
      _ = ‖⟪↑x, T x - z • x⟫_ℂ‖ := by simp [inner_sub_right, inner_smul_right, hrz]
      _ ≤ ‖T x - z • x‖ * ‖x‖ := mul_comm _ ‖x‖ ▸ norm_inner_le_norm _ _

/-- If `m` is an upper bound on the numerical range then the regularity domain contains `(m,∞)`. -/
lemma Ioi_subset_regularityDomain {m : ℝ} (h : m ∈ upperBounds (Θᵣₑ T)) :
    ofReal '' Ioi m ⊆ T.regularityDomain := by
  intro z ⟨r, hr, hrz⟩
  rw [← neg_mem_neg, ← regularityDomain_neg]
  refine hT.neg.Iio_subset_regularityDomain (m := -m) ?_ ?_
  · exact fun _ _ ↦ by simp_all [neg_le.mp, upperBounds]
  · exact ⟨-r, by simp [mem_Ioi.mp hr], by simp [hrz]⟩

end IsSymmetric
end LinearPMap
