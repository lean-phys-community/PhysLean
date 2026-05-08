/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
/-!

# Multiplication operators on `SpaceDHilbertSpace`

## i. Overview

In this module we introduce unbounded operators defined by multiplication by a function
`f : Space d → ℂ` which is `AEStronglyMeasurable`. The domain is defined to be as large as possible,
namely a vector `ψ ∈ SpaceDHilbertSpace d` is in the domain iff `f • ψ ∈ SpaceDHilbertSpace d`.

## ii. Key results

- `mulUnbounded f hf` : Given a function `f : Space d → ℂ` and a proof `hf`
  of `AEStronglyMeasurable f`, the unbounded operator defined by multiplication by `f`.

Notation:
- `ℳ` for `mulUnbounded`

## iii. Table of contents

- A. Multiplication LinearPMap
  - A.1. Dense domain
  - A.2. Conjugation
- B. Multiplication unbounded operator

## iv. References

See examples 1.3 and 3.8 in
- K. Schmüdgen, (2012). "Unbounded self-adjoint operators on Hilbert space" (Vol. 265). Springer.
  https://doi.org/10.1007/978-94-007-4753-1

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace
noncomputable section

open MeasureTheory
open AEEqFun
open Filter
open ComplexConjugate

variable {d : ℕ}

/-!
## A. Multiplication LinearPMap
-/

/-- The `LinearPMap` which maps `ψ` to `f • ψ` with domain `{ψ | f • ψ ∈ SpaceDHilbertSpace d}`. -/
def mulLPM (f : Space d → ℂ) : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d where
  domain := {
    carrier := {ψ : SpaceDHilbertSpace d | MemHS (f • ψ.val.cast)}
    add_mem' := by
      intro ψ φ hψ hφ
      refine memHS_of_ae _ (memHS_add hψ hφ) ?_
      filter_upwards [coeFn_add ψ.val φ.val] with x h
      simp [mul_add, h]
    zero_mem' := memHS_of_ae 0 zero_memHS (by filter_upwards; simp)
    smul_mem' c ψ hψ := by
      refine memHS_of_ae _ (memHS_const_smul (c := c) hψ) ?_
      filter_upwards [coeFn_smul c ψ.val] with x h
      change _ = (f • (c • ψ.val).cast) x
      simp [h, mul_left_comm]
  }
  toFun := {
    toFun ψ := mk ψ.prop
    map_add' ψ φ := by
      rw [← mk_add, mk_eq_iff]
      filter_upwards [coeFn_add ψ.1.val φ.1.val] with x h
      simp [h, mul_add]
    map_smul' c ψ := by
      rw [← mk_const_smul, mk_eq_iff]
      filter_upwards [coeFn_smul c ψ.1.val] with x h
      change (f • (c • ψ.1.val).cast) x = _
      simp [h, mul_left_comm]
  }

/-!
### A.1. Dense domain
-/

lemma mulLPM_dense_domain {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    Dense ((mulLPM f).domain : Set (SpaceDHilbertSpace d)) := by
  intro ψ
  apply mem_closure_iff_seq_limit.mpr
  obtain ⟨u, hu, hfu⟩ := AEStronglyMeasurable.aemeasurable hf
  let s : ℕ → Set (Space d) := fun n ↦ u ⁻¹' (Metric.closedBall 0 n)
  let φ : ℕ → SpaceDHilbertSpace d := fun n ↦ mk (f := (s n).indicator ψ) <| by
    apply memHS_iff.mpr
    refine ⟨by measurability, by measurability, ?_⟩
    refine HasFiniteIntegral.mono (memHS_iff.mp (coe_hilbertSpace_memHS ψ)).2.2 ?_
    refine Eventually.of_forall (fun x ↦ ?_)
    by_cases hx : x ∈ s n <;> simp [hx]
  have hφ : ∀ n, φ n =ᵐ[volume] (s n).indicator ψ := fun n ↦ coe_mk_ae _
  use φ
  constructor
  · intro n
    apply memHS_iff.mpr
    refine ⟨by measurability, by measurability, ?_⟩
    refine HasFiniteIntegral.mono (memHS_iff.mp (coe_hilbertSpace_memHS (n • φ n))).2.2 ?_
    filter_upwards [hfu, coeFn_smul n (φ n).val, hφ n] with x h₁ h₂ h₃
    by_cases hx : x ∈ s n
    · simp_rw [norm_pow, norm_norm, sq_le_sq, abs_norm]
      calc
        _ = ‖u x‖ * ‖φ n x‖ := by simp [h₁]
        _ ≤ n * ‖φ n x‖ := mul_le_mul_of_nonneg_right (by simp_all [s]) (norm_nonneg _)
        _ = ‖(n • φ n) x‖ := by simp [h₂]
    · simp [h₃, hx]
  · apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
    have h : ∀ n, ∫⁻ x, ‖(φ n - ψ) x‖ₑ ^ 2 = ∫⁻ x, ‖(s n)ᶜ.indicator ψ x‖ₑ ^ 2 := by
      intro n
      refine lintegral_congr_ae ?_
      filter_upwards [coeFn_sub (φ n).val ψ.val, hφ n] with x h₁ h₂
      by_cases hx : x ∈ s n <;> simp [hx, h₁, h₂]
    simp_rw [h]
    rw [← MeasureTheory.lintegral_zero (α := Space d) (μ := volume)]
    refine tendsto_lintegral_of_dominated_convergence' (fun x ↦ ‖ψ x‖ₑ ^ 2) ?_ ?_ ?_ ?_
    · measurability
    · intro n
      filter_upwards with x
      by_cases hx : x ∈ s n <;> simp [hx]
    · have : ∫⁻ x, ‖‖ψ x‖ ^ 2‖ₑ ≠ ⊤ := (memHS_iff.mp (coe_hilbertSpace_memHS ψ)).2.2.ne
      simp_all
    · filter_upwards with x
      rw [← zero_pow two_ne_zero, ← enorm_zero (E := ℂ)]
      refine ENNReal.Tendsto.pow ?_
      refine Tendsto.enorm ?_
      refine tendsto_nhds_of_eventually_eq ?_
      apply eventually_atTop.mpr
      use ⌈‖u x‖⌉.toNat
      intro n hn
      suffices ‖u x‖ ≤ n by simp [s, this]
      calc
        _ ≤ (⌈‖u x‖⌉ : ℝ) := Int.le_ceil _
        _ ≤ ⌈‖u x‖⌉.toNat := Int.cast_le.mpr (Int.self_le_toNat _)
        _ ≤ n := Nat.cast_le.mpr hn

/-!
### A.2. Conjugation
-/

lemma mulLPM_conj_domain {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (mulLPM (conj ∘ f)).domain = (mulLPM f).domain := by
  ext
  simp only [mulLPM, smul_eq_mul, memHS_iff]
  exact and_congr (iff_of_true (by fun_prop) (by fun_prop)) (by simp)

lemma mulLPM_conj_isFormalAdjoint (f : Space d → ℂ) :
    (mulLPM (conj ∘ f)).IsFormalAdjoint (mulLPM f) := by
  intro ψ φ
  refine integral_congr_ae ?_
  filter_upwards [coe_mk_ae φ.prop, coe_mk_ae ψ.prop] with x h₁ h₂
  simp [mulLPM, h₁, h₂, mul_assoc, mul_left_comm]

/-!
## B. Multiplication unbounded operator
-/

open InnerProductSpaceSubmodule in
/-- A LinearPMap with densely-defined formal adjoint is closable. -/
lemma isClosable_of_dense_formalAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {f : E →ₗ.[ℂ] F} (hf : Dense (f.domain : Set E))
    {g : F →ₗ.[ℂ] E} (hg : Dense (g.domain : Set F))
    (hgf : g.IsFormalAdjoint f) :
    f.IsClosable := by
  have hf' : Dense (f.adjoint.domain : Set F) := by
    refine Dense.mono ?_ hg
    rcases eq_or_lt_of_le (hgf.symm.le_adjoint hf) with (rfl | h)
    · rfl
    · exact (LinearPMap.domain_mono h).le
  use f.adjoint.adjoint
  ext
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hf']
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hf]
  rw [mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal]
  rw [Submodule.orthogonal_orthogonal_eq_closure]
  rw [mem_submodule_iff_mem_submoduleToLp]
  rw [submoduleToLp_closure]

/-- The unbounded operator which maps `ψ` to `f • ψ`
  with domain `{ψ | f • ψ ∈ SpaceDHilbertSpace d}`. -/
def mulUnbounded (f : Space d → ℂ) (hf : AEStronglyMeasurable f) :
    UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) where
  toLinearPMap := mulLPM f
  dense_domain := mulLPM_dense_domain hf
  is_closable := by
    refine isClosable_of_dense_formalAdjoint (g := mulLPM (conj ∘ f)) ?_ ?_ ?_
    · exact mulLPM_dense_domain hf
    · exact mulLPM_conj_domain hf ▸ mulLPM_dense_domain hf
    · exact mulLPM_conj_isFormalAdjoint f

@[inherit_doc mulUnbounded]
scoped notation "ℳ" => mulUnbounded

lemma mem_mulUnbounded_domain_iff
    {f : Space d → ℂ} {hf : AEStronglyMeasurable f} {ψ : SpaceDHilbertSpace d} :
    ψ ∈ (ℳ f hf).domain ↔ MemHS (f • ψ.val.cast) := Iff.rfl

lemma mulUnbounded_apply_ae {f : Space d → ℂ} {hf : AEStronglyMeasurable f} (ψ : (ℳ f hf).domain) :
    (ℳ f hf) ψ =ᵐ[volume] f • ψ := coe_mk_ae ψ.prop

end
end SpaceDHilbertSpace
end QuantumMechanics
