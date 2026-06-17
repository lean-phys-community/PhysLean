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

## iv. References

-/

@[expose] public section

namespace LinearPMap
namespace IsSymmetric

open Complex
open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

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

end IsSymmetric
end LinearPMap
