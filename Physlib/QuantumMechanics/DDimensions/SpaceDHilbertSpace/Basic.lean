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
abbrev SpaceDHilbertSpace (d : ℕ) (μ : Measure (Space d) := volume) := Lp ℂ 2 μ

namespace SpaceDHilbertSpace

variable {d : ℕ} {μ μ' : Measure (Space d)} {f g : Space d → ℂ} (ψ φ : SpaceDHilbertSpace d μ)

variable {ψ φ} in
lemma ext_iff : ψ = φ ↔ ψ =ᵐ[μ] φ := Lp.ext_iff

/-!
## B. Dual space
-/

/-- The anti-linear equivalence between `SpaceDHilbertSpace d μ` and its dual.

  This is the map that takes a ket to its corresponding bra and _vice versa_. -/
def toBra : SpaceDHilbertSpace d μ ≃ₛₗ[starRingEnd ℂ] StrongDual ℂ (SpaceDHilbertSpace d μ) :=
  toDual ℂ (SpaceDHilbertSpace d μ)

@[simp]
lemma toBra_apply_apply : toBra ψ φ = ⟪ψ, φ⟫_ℂ := rfl

@[simp]
lemma toBra_symm_apply (f : StrongDual ℂ (SpaceDHilbertSpace d μ)) : ⟪toBra.symm f, ψ⟫_ℂ = f ψ :=
  toDual_symm_apply

/-!
## C. Membership
-/

/-- The proposition `MemHS f` for a function `f : Space d → ℂ` is defined
  to be true if the function `f` can be lifted to the Hilbert space. -/
def MemHS (f : Space d → ℂ) (μ : Measure (Space d) := volume) : Prop := MemLp f 2 μ

lemma memHS_coe : MemHS ψ μ := Lp.memLp ψ

/-- A function `f` satisfies `MemHS f μ` if and only if it is `μ`-a.e. strongly measurable
  and square integrable. -/
lemma memHS_iff : MemHS f μ ↔ AEStronglyMeasurable f μ ∧ Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
  and_congr_right fun h ↦ (and_iff_right h).symm.trans (memLp_two_iff_integrable_sq_norm h)

lemma mem_iff {f : Space d →ₘ[μ] ℂ} : f ∈ SpaceDHilbertSpace d μ ↔ MemHS f μ := Lp.mem_Lp_iff_memLp

@[simp]
lemma MemHS.zero : MemHS (0 : Space d → ℂ) μ := MemLp.zero

lemma MemHS.neg (hf : MemHS f μ) : MemHS (-f) μ := MemLp.neg hf

lemma MemHS.add (hf : MemHS f μ) (hg : MemHS g μ) : MemHS (f + g) μ := MemLp.add hf hg

lemma MemHS.sub (hf : MemHS f μ) (hg : MemHS g μ) : MemHS (f - g) μ := MemLp.sub hf hg

lemma MemHS.const_smul (c : ℂ) (hf : MemHS f μ) : MemHS (c • f) μ := MemLp.const_smul hf c

lemma MemHS.ae_eq (hfg : f =ᵐ[μ] g) (hf : MemHS f μ) : MemHS g μ := MemLp.ae_eq hfg hf

lemma MemHS.mono_measure (h : μ' ≤ μ) (hf : MemHS f μ) : MemHS f μ' := MemLp.mono_measure h hf

lemma MemHS.restrict (Ω : Set (Space d)) (hf : MemHS f μ) : MemHS f (μ.restrict Ω) :=
  hf.mono_measure restrict_le_self

lemma MemHS.mono_restrict {Ω Ω' : Set (Space d)} (h : Ω' ≤ Ω) (hf : MemHS f (μ.restrict Ω)) :
    MemHS f (μ.restrict Ω') :=
  hf.mono_measure (μ.restrict_mono_set h)

lemma MemHS.indicator {Ω : Set (Space d)} (hΩ : MeasurableSet Ω) (hf : MemHS f μ) :
    MemHS (Ω.indicator f) μ :=
  MemLp.indicator hΩ hf

lemma MemHS.indicator_of_restrict
    {Ω : Set (Space d)} (hΩ : MeasurableSet Ω) (hf : MemHS f (μ.restrict Ω)) :
    MemHS (Ω.indicator f) μ := by
  refine memHS_iff.mpr ⟨(aestronglyMeasurable_indicator_iff hΩ).mpr hf.1, ?_⟩
  refine (IntegrableOn.integrable_indicator (memHS_iff.mp hf).2 hΩ).congr ?_
  filter_upwards with x
  by_cases x ∈ Ω <;> simp_all

/-!
## D. Construction of elements
-/

section

variable (hf : MemHS f μ) (hg : MemHS g μ)

/-- Given a function `f : Space d → ℂ` such that `MemHS f μ` is true via `hf`,
  `mk hf` is the element of the Hilbert space defined by `f`. -/
def mk : SpaceDHilbertSpace d μ :=
  ⟨AEEqFun.mk f hf.1, mem_iff.mpr <| hf.ae_eq (AEEqFun.coeFn_mk f hf.1).symm⟩

@[simp]
lemma mk_neg : mk hf.neg = -mk hf := rfl

@[simp]
lemma mk_add : mk (hf.add hg) = mk hf + mk hg := rfl

@[simp]
lemma mk_sub : mk (hf.sub hg) = mk hf - mk hg := rfl

@[simp]
lemma mk_const_smul (c : ℂ) : mk (hf.const_smul c) = c • mk hf := rfl

lemma coeFn_mk : mk hf =ᵐ[μ] f := AEEqFun.coeFn_mk f hf.1

lemma mk_eq_iff : mk hf = mk hg ↔ f =ᵐ[μ] g := by simp [mk]

lemma mk_surjective : ∃ (f : Space d → ℂ) (hf : MemHS f μ), mk hf = ψ :=
  ⟨ψ, memHS_coe ψ, by simp [mk]⟩

lemma inner_mk_mk : ⟪mk hf, mk hg⟫_ℂ = ∫ x, starRingEnd ℂ (f x) * g x ∂μ := by
  apply integral_congr_ae
  filter_upwards [coeFn_mk hf, coeFn_mk hg]
  simp_all [mul_comm]

end

/-!
## E. Coersions
-/

section

variable (c : ℂ) (ψ φ : SpaceDHilbertSpace d μ)

lemma coeFn_neg : ⇑(-ψ) =ᵐ[μ] -ψ := Lp.coeFn_neg _

lemma coeFn_add : ⇑(ψ.val + φ.val) =ᵐ[μ] ψ + φ := Lp.coeFn_add _ _

lemma coeFn_sub : ⇑(ψ.val - φ.val) =ᵐ[μ] ψ - φ := Lp.coeFn_sub _ _

lemma coeFn_smul : ⇑(c • ψ) =ᵐ[μ] c • ψ := Lp.coeFn_smul _ _

end

/-!
## F. Misc.
-/

open Filter

lemma tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq
    {α : Type*} {l : Filter α} {ψ : α → SpaceDHilbertSpace d μ} :
    Tendsto ψ l (nhds 0) ↔ Tendsto (fun a ↦ ∫⁻ x, ‖ψ a x‖ₑ ^ 2 ∂μ) l (nhds 0) := by
  trans Tendsto (fun a ↦ (∫⁻ x, ‖ψ a x‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)) l (nhds 0)
  · simp [tendsto_iff_edist_tendsto_0, edist_zero_right, Lp.enorm_def, eLpNorm, eLpNorm']
  constructor <;> intro h
  · apply Tendsto.ennrpow_const 2 at h
    simp_all [← ENNReal.rpow_mul_natCast]
  · apply Tendsto.ennrpow_const 2⁻¹ at h
    simp_all

end SpaceDHilbertSpace
end QuantumMechanics
end
