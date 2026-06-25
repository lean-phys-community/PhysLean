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

In this module we develop the spectral theory for symmetric operators.

The numerical range of an operator, `Θ T = {⟪x, T x⟫_ℂ | x ∈ T.domain ∧ ‖x‖ = 1}`, is a subset of ℂ.
For symmetric operators the numerical range consists only of real numbers and it is meaningful
to discuss its upper/lower bounds. To facilitate this, we define `LinearPMap.realNumericalRange`
as the projection of `LinearPMap.numericalRange` onto the real axis. For symmetric operators this
simply reinterprets the numerical range as a subset of ℝ.

## ii. Key results

- `realNumericalRange` (`Θᵣₑ`) : The projection of the numerical range onto the real axis.
- `compl_ofReal_subset_regularityDomain` : The regularity domain of a symmetric operator contains
    all complex numbers with non-zero imaginary part.
- `regularityDomain_isConnected_iff` : The regularity domain of a symmetric operator is connected
    if and only if it contains a real number.

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
lemma numericalRange_subset : Θ T ⊆ range ofReal := by
  intro z hz
  use z.re
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

lemma closure_numericalRange_subset : _root_.closure (Θ T) ⊆ range ofReal := by
  refine (closure_mono hT.numericalRange_subset).trans ?_
  have h : range ofReal = im ⁻¹' {0} := by
    ext z
    exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ ofReal_im r, fun hz ↦ ⟨z.re, Eq.symm (Complex.ext rfl hz)⟩⟩
  exact (h ▸ IsClosed.preimage (by fun_prop) (by simp)).closure_subset

/-!
## B. Regularity domain
-/

/-- The regularity domain of a symmetric operator contains all complex numbers with non-zero
  imaginary part. -/
lemma mem_regularityDomain_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z ∈ T.regularityDomain := by
  apply T.compl_closure_numericalRange_subset_regularityDomain
  refine (mem_compl_iff _ _).mpr fun h ↦ hz ?_
  obtain ⟨r, _, rfl⟩ := hT.closure_numericalRange_subset h
  exact ofReal_im r

/-- The regularity domain of a symmetric operator contains all complex numbers with non-zero
  imaginary part. -/
lemma compl_ofReal_subset_regularityDomain : (range ofReal)ᶜ ⊆ T.regularityDomain :=
  fun z hz ↦ hT.mem_regularityDomain_of_im_ne_zero fun h ↦ hz ⟨z.re, Eq.symm (Complex.ext rfl h)⟩

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

/-- The regularity domain of a symmetric operator is connected iff it contains a real number. -/
lemma regularityDomain_isConnected_iff :
    IsConnected T.regularityDomain ↔ (ofReal ⁻¹' T.regularityDomain).Nonempty := by
  rw [T.regularityDomain_isOpen.isConnected_iff_isPathConnected]
  constructor
  · intro h
    obtain ⟨f, hf⟩ : JoinedIn T.regularityDomain (-I) I := by
      refine h.joinedIn (-I) ?_ I ?_
      · exact hT.mem_regularityDomain_of_im_ne_zero (by simp)
      · exact hT.mem_regularityDomain_of_im_ne_zero (by simp)
    obtain ⟨t, ht⟩ : ∃ t, (f t).im = 0 := by
      have hIVT := intermediate_value_Icc (f := fun t ↦ (f t).im) zero_le_one (by fun_prop)
      simp only [Path.source, neg_im, I_im, Path.target] at hIVT
      have h₀ : (0 : ℝ) ∈ Icc (-1) 1 := by simp
      exact ⟨(hIVT h₀).choose, (hIVT h₀).choose_spec.2⟩
    specialize hf t
    rw [← re_add_im (f t), ht] at hf
    exact ⟨(f t).re, by simp_all⟩
  · intro ⟨r, hr⟩
    apply mem_preimage.mp at hr
    refine isPathConnected_iff.mpr ⟨?_, fun z₁ hz₁ z₂ hz₂ ↦ ?_⟩
    · exact ⟨I, hT.mem_regularityDomain_of_im_ne_zero (by simp)⟩
    · have h : ∀ z ∈ T.regularityDomain, JoinedIn T.regularityDomain z r := by
        intro z hz
        by_cases hz_im : z.im = 0
        · rcases eq_or_ne z r with rfl | hzr
          · exact JoinedIn.refl hr
          · let path : Path z r := {
              toFun t := ((z + r) + (z - r) * cexp (Real.pi * t * I)) / 2
              source' := by simp
              target' := by simp [add_comm z r, add_add_sub_cancel]
            }
            refine ⟨path, fun t ↦ ?_⟩
            by_cases! ht : ∃ n : ℤ, n = (t : ℝ)
            · obtain ⟨n, htn⟩ := ht
              obtain ⟨k, hk⟩ := Int.even_or_odd' n
              rcases hk with heven | hodd
              · suffices cexp (Real.pi * t * I) = 1 by simp [path, this, hz]
                exact exp_eq_one_iff.mpr ⟨k, by simp [← htn, heven, mul_comm, ← mul_assoc]⟩
              · suffices cexp (Real.pi * (t - 1) * I) = 1 by
                  rw [mul_sub, sub_mul, mul_one, exp_sub_pi_mul_I, neg_eq_iff_eq_neg] at this
                  simp [path, this, add_comm z r, hr]
                exact exp_eq_one_iff.mpr ⟨k, by simp [← htn, hodd, mul_comm, ← mul_assoc]⟩
            · have hzr' : z.re - r ≠ 0 :=
                  fun h ↦ hzr <| Complex.ext (sub_eq_zero.mp h) (by simp [hz_im])
              refine hT.mem_regularityDomain_of_im_ne_zero ?_
              simp [path, hz_im, exp_im, Real.sin_eq_zero_iff, mul_comm, hzr', ht]
        · refine JoinedIn.of_segment_subset fun w ⟨a, b, _, _, _, hw⟩ ↦ ?_
          rcases eq_zero_or_neZero a with rfl | _
          · simp_all
          · exact hT.mem_regularityDomain_of_im_ne_zero fun _ ↦ hz_im (by simp_all [← hw])
      exact (h z₁ hz₁).trans (h z₂ hz₂).symm

/-- The regularity domain of a lower semibounded symmetric operator is connected. -/
lemma regularityDomain_isConnected_of_bddBelow (h : BddBelow (Θᵣₑ T)) :
    IsConnected T.regularityDomain := by
  obtain ⟨m, hm⟩ := h
  apply hT.regularityDomain_isConnected_iff.mpr
  exact ⟨m - 1, hT.Iio_subset_regularityDomain hm ⟨m - 1, by simp⟩⟩

/-- The regularity domain of an upper semibounded symmetric operator is connected. -/
lemma regularityDomain_isConnected_of_bddAbove (h : BddAbove (Θᵣₑ T)) :
    IsConnected T.regularityDomain := by
  obtain ⟨m, hm⟩ := h
  apply hT.regularityDomain_isConnected_iff.mpr
  exact ⟨m + 1, hT.Ioi_subset_regularityDomain hm ⟨m + 1, by simp⟩⟩

/-!
## C. Point spectrum
-/

/-- Eigenvalues of a symmetric unbounded operator are real. -/
lemma pointSpectrum_real : σᵖ T ⊆ range ofReal := by
  intro z hz
  apply hT.numericalRange_subset
  obtain ⟨x, hx, hx₀⟩ := (Submodule.ne_bot_iff _).mp hz
  suffices z = (‖x‖ ^ 2)⁻¹ * ⟪↑x, T ⟨x, x.2.1⟩⟫_ℂ by
    exact this ▸ mem_numericalRange (T := T) (x := ⟨x, x.2.1⟩) (by simp [hx₀])
  rw [ofReal_inv]
  refine (eq_inv_mul_iff_mul_eq₀ (by simp [hx₀])).mpr (Eq.symm ?_)
  calc
    _ = ⟪↑x, (T - z • 1) x + z • x⟫_ℂ := by simp [sub_apply]
    _ = ⟪x, z • x⟫_ℂ := by simp [← toFun_eq_coe, LinearMap.mem_ker.mp hx]
    _ = ↑(‖x‖ ^ 2) * z := by simp [inner_smul_right, mul_comm]

end IsSymmetric
end LinearPMap
