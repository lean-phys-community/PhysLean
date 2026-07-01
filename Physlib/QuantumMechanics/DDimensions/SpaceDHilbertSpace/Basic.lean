/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Physlib.SpaceAndTime.Space.Module
/-!

# Hilbert spaces for quantum mechanics on `Space d`

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Definition
- B. Dual space
- C. Membership
- D. Construction of elements
- E. Coersions
- F. Misc.

## iv. References

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics

open Function InnerProductSpace MeasureTheory Measure Set

/-!
## A. Definition
-/

/-- The Hilbert space for single-particle quantum mechanics on `Space d` is defined to be
  `L²(Space d, ℂ)`, the space of almost-everywhere equal equivalence classes of square-integrable
  functions from `Space d` to `ℂ`. -/
abbrev SpaceDHilbertSpace (d : ℕ) := Lp (α := Space d) ℂ 2 volume

namespace SpaceDHilbertSpace

variable {d : ℕ} {f g : Space d → ℂ} (ψ φ : SpaceDHilbertSpace d)

/-!
## B. Dual space
-/

/-- The anti-linear equivalence between `SpaceDHilbertSpace d` and its dual.

  This is the map that takes a ket to its corresponding bra and _vice versa_. -/
def toBra : SpaceDHilbertSpace d ≃ₛₗ[starRingEnd ℂ] StrongDual ℂ (SpaceDHilbertSpace d) :=
  toDual ℂ (SpaceDHilbertSpace d)

@[simp]
lemma toBra_apply_apply : toBra ψ φ = ⟪ψ, φ⟫_ℂ := rfl

@[simp]
lemma toBra_symm_apply (f : StrongDual ℂ (SpaceDHilbertSpace d)) : ⟪toBra.symm f, ψ⟫_ℂ = f ψ :=
  toDual_symm_apply

/-!
## C. Membership
-/

/-- The proposition `MemHS f` for a function `f : Space d → ℂ` is defined
  to be true if the function `f` can be lifted to the Hilbert space. -/
def MemHS (f : Space d → ℂ) : Prop := MemLp f 2

lemma aeStronglyMeasurable_of_memHS {f : Space d → ℂ} (h : MemHS f) : AEStronglyMeasurable f :=
  MemLp.aestronglyMeasurable h

/-- A function `f` satisfies `MemHS f` if and only if it is almost everywhere
  strongly measurable and square integrable. -/
lemma memHS_iff {f : Space d → ℂ} : MemHS f ↔
    AEStronglyMeasurable f ∧ Integrable (fun x ↦ ‖f x‖ ^ 2) := by
  rw [MemHS, MemLp, and_congr_right]
  intro h
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (NeZero.ne' 2).symm ENNReal.top_ne_ofNat.symm]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  have h' : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ 2) :=
    AEStronglyMeasurable.pow (AEStronglyMeasurable.norm h) 2
  simp [Integrable, h', HasFiniteIntegral]

@[simp]
lemma zero_memHS : MemHS (d := d) 0 := by
  rw [memHS_iff]
  simp only [Pi.ofNat_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integrable_fun_zero, and_true]
  fun_prop

@[simp]
lemma zero_fun_memHS : MemHS (fun _ : Space d ↦ (0 : ℂ)) := zero_memHS

lemma memHS_add {f g : Space d → ℂ} (hf : MemHS f) (hg : MemHS g) : MemHS (f + g) :=
  MemLp.add hf hg

lemma memHS_const_smul {f : Space d → ℂ} {c : ℂ} (hf : MemHS f) : MemHS (c • f) :=
  MemLp.const_smul hf c

lemma memHS_of_ae {g : Space d → ℂ} (f : Space d → ℂ) (hf : MemHS f) (hfg : f =ᵐ[volume] g) :
    MemHS g := MemLp.ae_eq hfg hf

/-!
## D. Construction of elements
-/

section

lemma aeEqFun_mk_mem_iff (f : Space d → ℂ) (hf : AEStronglyMeasurable f volume) :
    AEEqFun.mk f hf ∈ SpaceDHilbertSpace d ↔ MemHS f := by
  rw [Lp.mem_Lp_iff_memLp]
  exact memLp_congr_ae (AEEqFun.coeFn_mk f hf)

/-- Given a function `f : Space d → ℂ` such that `MemHS f` is true via `hf`,
  `SpaceDHilbertSpace.mk f` is the element of the Hilbert space defined by `f`. -/
def mk {f : Space d → ℂ} (hf : MemHS f) : SpaceDHilbertSpace d :=
  ⟨AEEqFun.mk f hf.1, (aeEqFun_mk_mem_iff f hf.1).mpr hf⟩

lemma coe_hilbertSpace_memHS (f : SpaceDHilbertSpace d) : MemHS (f : Space d → ℂ) := by
  rw [← aeEqFun_mk_mem_iff f (Lp.aestronglyMeasurable f)]
  have hf : f = AEEqFun.mk f (Lp.aestronglyMeasurable f) := (AEEqFun.mk_coeFn _).symm
  exact hf ▸ f.2

lemma mk_surjective (f : SpaceDHilbertSpace d) :
    ∃ (g : Space d → ℂ) (hg : MemHS g), mk hg = f := by
  use f, coe_hilbertSpace_memHS f
  simp [mk]

lemma coe_mk_ae {f : Space d → ℂ} (hf : MemHS f) : (mk hf) =ᵐ[volume] f :=
  AEEqFun.coeFn_mk f hf.1

lemma inner_mk_mk {f g : Space d → ℂ} (hf : MemHS f) (hg : MemHS g) :
    ⟪mk hf, mk hg⟫_ℂ = ∫ x : Space d, starRingEnd ℂ (f x) * g x := by
  apply integral_congr_ae
  filter_upwards [coe_mk_ae hf, coe_mk_ae hg] with x hf hg
  simp [hf, hg, mul_comm]

@[simp]
lemma eLpNorm_mk {f : Space d → ℂ} {hf : MemHS f} : eLpNorm (mk hf) 2 = eLpNorm f 2 :=
  eLpNorm_congr_ae (coe_mk_ae hf)

lemma mem_iff {f : Space d → ℂ} (hf : AEStronglyMeasurable f volume) :
    AEEqFun.mk f hf ∈ SpaceDHilbertSpace d ↔ Integrable (fun x ↦ ‖f x‖ ^ 2) := by
  rw [Lp.mem_Lp_iff_memLp, MemLp, eLpNorm_aeeqFun]
  have h1 := AEEqFun.aestronglyMeasurable (AEEqFun.mk f hf)
  have h2 : AEStronglyMeasurable (fun x ↦ norm (f x) ^ 2) :=
    AEStronglyMeasurable.pow (continuous_norm.comp_aestronglyMeasurable hf) 2
  simp only [h1]
  simp only [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (NeZero.ne' 2).symm
    (ENNReal.top_ne_ofNat).symm, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  simp [h2, Integrable, HasFiniteIntegral]

@[simp]
lemma mk_add {f g : Space d → ℂ} {hf : MemHS f} {hg : MemHS g} :
    mk (memHS_add hf hg) = mk hf + mk hg := rfl

@[simp]
lemma mk_const_smul {f : Space d → ℂ} {c : ℂ} {hf : MemHS f} :
    mk (memHS_const_smul (c := c) hf) = c • mk hf := rfl

lemma mk_eq_iff {f g : Space d → ℂ} {hf : MemHS f} {hg : MemHS g} :
    mk hf = mk hg ↔ f =ᵐ[volume] g := by simp [mk]

lemma ext_iff {f g : SpaceDHilbertSpace d} :
    f = g ↔ (f : Space d → ℂ) =ᵐ[volume] (g : Space d → ℂ) := Lp.ext_iff

end

/-!
## E. Coersion
-/

section

end

/-!
## F. Limits
-/

open Filter

lemma tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq
    {d : ℕ} {α : Type*} {l : Filter α} {ψ : α → SpaceDHilbertSpace d} :
    Tendsto ψ l (nhds 0) ↔ Tendsto (fun a ↦ ∫⁻ x : Space d, ‖ψ a x‖ₑ ^ 2) l (nhds 0) := by
  trans Tendsto (fun a ↦ (∫⁻ x, ‖ψ a x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) l (nhds 0)
  · simp [tendsto_iff_edist_tendsto_0, edist_zero_right, Lp.enorm_def, eLpNorm, eLpNorm']
  constructor <;> intro h
  · apply Tendsto.ennrpow_const 2 at h
    simp_all [← ENNReal.rpow_mul_natCast]
  · apply Tendsto.ennrpow_const 2⁻¹ at h
    simp_all

end SpaceDHilbertSpace
end QuantumMechanics
end
