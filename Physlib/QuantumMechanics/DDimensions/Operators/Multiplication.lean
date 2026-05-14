/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
import Physlib.Meta.Linters.Sorry
/-!

# Multiplication operators on `SpaceDHilbertSpace`

## i. Overview

In this module we introduce unbounded operators defined by multiplication by a function
`f : Space d → ℂ`. The domain is defined to be as large as possible, namely a vector
`ψ ∈ SpaceDHilbertSpace d` is in the domain iff `f • ψ ∈ SpaceDHilbertSpace d`.

## ii. Key results

- `mulOperator f` : Given a function `f : Space d → ℂ`, the operator defined by `ψ ↦ f • ψ`
  (with maximal domain) with notation `ℳ f`.
- `mulOperator_adjoint_eq_conj` : For a.e. strongly measurable `f`, `(ℳ f)† = ℳ (conj ∘ f)`
- `mulOperator_isUnbounded` : For a.e. strongly measurable `f`, `ℳ f` is an unbounded operator.

## iii. Table of contents

- A. Definition
- B. Dense domain
- C. Adjoint
  - C.1. Self-adjoint
- D. Closable & unbounded

## iv. References

See examples 1.3 and 3.8 in
- K. Schmüdgen, (2012). "Unbounded self-adjoint operators on Hilbert space" (Vol. 265). Springer.
  https://doi.org/10.1007/978-94-007-4753-1

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace
noncomputable section

open LinearPMap
open MeasureTheory
open AEEqFun
open Filter
open ComplexConjugate

variable {d : ℕ}

/-!
## A. Definition
-/

/-- The LinearPMap which maps `ψ` to `f • ψ` with domain `{ψ | f • ψ ∈ SpaceDHilbertSpace d}`. -/
def mulOperator (f : Space d → ℂ) : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d where
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

@[inherit_doc mulOperator]
notation "ℳ" => mulOperator

lemma mem_mulOperator_domain_iff
    {f : Space d → ℂ} {ψ : SpaceDHilbertSpace d} : ψ ∈ (ℳ f).domain ↔ MemHS (f • ψ.val.cast) :=
  Iff.rfl

lemma mulOperator_apply_ae {f : Space d → ℂ} (ψ : (ℳ f).domain) : (ℳ f) ψ =ᵐ[volume] f • ψ :=
  coe_mk_ae ψ.prop

/-!
## B. Dense domain
-/

lemma mulOperator_hasDenseDomain {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (ℳ f).HasDenseDomain := by
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
## C. Adjoint
-/

-- Can the AEStronglyMeasurable hypothesis be removed?
lemma mulOperator_conj_domain {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (ℳ (conj ∘ f)).domain = (ℳ f).domain := by
  ext
  simp only [mulOperator, smul_eq_mul, memHS_iff]
  exact and_congr (iff_of_true (by fun_prop) (by fun_prop)) (by simp)

@[sorryful]
lemma mulOperator_adjoint_eq_conj {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (ℳ f)† = ℳ (conj ∘ f) := by
  refine eq_of_eq_graph ?_
  ext u
  rw [adjoint_graph_eq_graph_adjoint (mulOperator_hasDenseDomain hf), Submodule.mem_adjoint_iff]
  constructor
  · intro h
    let g : Space d → ℂ := fun x ↦ conj (f x) * u.1 x - u.2 x
    have hg : AEStronglyMeasurable g := by measurability
    have h_int : ∀ ψ : (ℳ f).domain, ∫ x, (AEEqFun.mk g hg) x * conj (ψ.val x) = 0 := by
      intro ψ
      have h_int₁ : Integrable fun x ↦ u.1 x * conj (ℳ f ψ x) := L2.integrable_inner (ℳ f ψ) u.1
      have h_int₂ : Integrable fun x ↦ u.2 x * conj (ψ.val x) := L2.integrable_inner ψ.val u.2
      symm
      trans ∫ x, u.1 x * conj (ℳ f ψ x) - u.2 x * conj (ψ.val x)
      · exact (h ψ (ℳ f ψ) (mem_graph (ℳ f) ψ)) ▸ (integral_sub h_int₁ h_int₂).symm
      refine integral_congr_ae ?_
      filter_upwards [mulOperator_apply_ae ψ, AEEqFun.coeFn_mk g hg] with x h₁ h₂
      simp [h₁, h₂, g, sub_mul, mul_assoc, mul_left_comm]
    have hu₂ : u.2 =ᵐ[volume] (conj ∘ f) • u.1 := by
      sorry
    have hu₁ : u.1 ∈ (ℳ (conj ∘ f)).domain :=
      mem_mulOperator_domain_iff.mpr <| memHS_of_ae u.2 (coe_hilbertSpace_memHS u.2) hu₂
    apply (mem_graph_iff _).mpr
    refine ⟨⟨u.1, hu₁⟩, rfl, ?_⟩
    apply ext_iff.mpr
    filter_upwards [mulOperator_apply_ae ⟨u.1, hu₁⟩, hu₂] with x h₁ h₂
    rw [h₁, h₂]
  · intro hu v₁ v₂ hv
    obtain ⟨ψ, hu₁, hu₂⟩ := (mem_graph_iff _).mp hu
    obtain ⟨φ, rfl, rfl⟩ := (mem_graph_iff _).mp hv
    rw [sub_eq_zero]
    refine integral_congr_ae ?_
    filter_upwards [mulOperator_apply_ae ψ, mulOperator_apply_ae φ]
    simp_all [mul_assoc, mul_left_comm]

/-!
### C.1. Self-adjoint
-/

@[sorryful]
lemma mulOperator_isSelfAdjoint_ofReal
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f) (hf' : conj ∘ f = f) :
    IsSelfAdjoint (ℳ f) := by
  apply isSelfAdjoint_def.mpr
  rw [mulOperator_adjoint_eq_conj hf, hf']

/-!
## D. Closable & unbounded
-/

@[sorryful]
lemma mulOperator_isClosable {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (ℳ f).IsClosable := by
  refine isClosable_of_exists_dense_formalAdjoint ?_ ?_
  · exact mulOperator_hasDenseDomain hf
  · refine ⟨ℳ (conj ∘ f), ?_, ?_⟩
    · exact mulOperator_hasDenseDomain (by measurability)
    · rw [← mulOperator_adjoint_eq_conj hf]
      exact adjoint_isFormalAdjoint (mulOperator_hasDenseDomain hf)

@[sorryful]
lemma mulOperator_isUnbounded {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (ℳ f).IsUnbounded :=
  ⟨mulOperator_hasDenseDomain hf, mulOperator_isClosable hf⟩

end
end SpaceDHilbertSpace
end QuantumMechanics
