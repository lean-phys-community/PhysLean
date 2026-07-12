/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
/-!

# Schwartz submodule

## i. Overview

In this module we define the Schwartz submodule of `SpaceDHilbertSpace`.

## ii. Key results

- `SchwartzSubmodule d`: Submodule of `SpaceDHilbertSpace d` consisting of the L² equivalence
  classes of Schwartz maps `𝓢(Space d, ℂ)`.

## iii. Table of contents

- A. Definitions
- B. Coercions
- D. Misc.

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

noncomputable section

open MeasureTheory
open InnerProductSpace
open SchwartzMap

variable {d : ℕ}

/-!
## A. Definitions
-/

/-- The continuous linear map including Schwartz maps into `SpaceDHilbertSpace d`. -/
def schwartzIncl : 𝓢(Space d, ℂ) →L[ℂ] SpaceDHilbertSpace d := toLpCLM ℂ (E := Space d) ℂ 2

/-- The submodule of `SpaceDHilbertSpace d` corresponding to Schwartz maps. -/
abbrev SchwartzSubmodule (d : ℕ) := (schwartzIncl (d := d)).range

/-- The linear equivalence between the Schwartz maps `𝓢(Space d, ℂ)` and the Schwartz submodule
  of `SpaceDHilbertSpace d`. -/
def schwartzEquiv : 𝓢(Space d, ℂ) ≃ₗ[ℂ] SchwartzSubmodule d :=
  LinearEquiv.ofInjective schwartzIncl.toLinearMap (injective_toLp (E := Space d) 2)

namespace SchwartzSubmodule

variable (f g : 𝓢(Space d, ℂ)) (ψ : SchwartzSubmodule d)

/-!
## B. Coercions
-/

instance : CoeFun (SchwartzSubmodule d) fun _ ↦ Space d → ℂ := ⟨fun ψ ↦ ψ.val⟩

lemma schwartzEquiv_apply_coe : ↑(schwartzEquiv f) = schwartzIncl f := by simp [schwartzEquiv]

lemma schwartzEquiv_coe_ae : schwartzEquiv f =ᵐ[volume] f := coeFn_toLp f 2 volume

lemma schwartzEquiv_symm_coe_ae : schwartzEquiv.symm ψ =ᵐ[volume] ψ := by
  nth_rw 2 [← schwartzEquiv.apply_symm_apply ψ]
  exact (schwartzEquiv_coe_ae _).symm

lemma schwartzEquiv_ae_eq (h : schwartzEquiv f =ᵐ[volume] schwartzEquiv g) : f = g :=
  (EmbeddingLike.apply_eq_iff_eq _).mp (SetLike.coe_eq_coe.mp (ext_iff.mpr h))

/-!
## C. Misc.
-/

@[simp]
lemma zero_eq_top : SchwartzSubmodule 0 = ⊤ := by
  ext ψ
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_top, iff_true]
  let g : 𝓢(Space 0, ℂ) := {
    toFun x := ψ 0
    smooth' := contDiff_const
    decay' k n := by
      refine ⟨‖ψ 0‖, fun x ↦ ?_⟩
      rcases eq_zero_or_pos n with rfl | hn
      · rw [← one_mul ‖ψ 0‖]
        refine mul_le_mul ?_ (by simp) (norm_nonneg _) zero_le_one
        simp [Space.point_dim_zero_eq, zero_pow_le_one]
      · simp [iteratedFDeriv_const_of_ne hn.ne']
  }
  use g
  ext
  filter_upwards [schwartzEquiv_coe_ae g] with x hg
  rw [← schwartzEquiv_apply_coe, hg, Space.point_dim_zero_eq x]
  rfl

lemma dense (d : ℕ) : Dense (SchwartzSubmodule d : Set (SpaceDHilbertSpace d)) :=
  denseRange_toLpCLM ENNReal.top_ne_ofNat.symm

lemma schwartzEquiv_inner :
    ⟪schwartzEquiv f, schwartzEquiv g⟫_ℂ = ∫ x : Space d, starRingEnd ℂ (f x) * g x := by
  apply integral_congr_ae
  filter_upwards [schwartzEquiv_coe_ae f, schwartzEquiv_coe_ae g] with _ hf hg
  simp [hf, hg, mul_comm]

lemma schwartzIncl_ker : schwartzIncl.ker = (⊥ : Submodule ℂ 𝓢(Space d, ℂ)) := by
  ext; simp [← schwartzEquiv_apply_coe]

end SchwartzSubmodule
end
end SpaceDHilbertSpace
end QuantumMechanics
