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
`f : Space d → ℂ`. The domain is defined to be as large as possible, namely a vector
`ψ ∈ SpaceDHilbertSpace d` is in the domain iff `f • ψ ∈ SpaceDHilbertSpace d`.

## ii. Key results

- `mulOperator f` : Given a function `f : Space d → ℂ`, the operator defined by `ψ ↦ f • ψ`
  (with maximal domain) with notation `𝓜 f`.
- `mulOperator_adjoint_eq_conj` : For a.e. strongly measurable `f`, `(𝓜 f)† = 𝓜 (conj ∘ f)`
- `mulOperator_isUnbounded` : For a.e. strongly measurable `f`, `𝓜 f` is an unbounded operator.

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
notation "𝓜" => mulOperator

lemma mem_mulOperator_domain_iff
    {f : Space d → ℂ} {ψ : SpaceDHilbertSpace d} : ψ ∈ (𝓜 f).domain ↔ MemHS (f • ψ.val.cast) :=
  Iff.rfl

lemma mulOperator_apply_ae {f : Space d → ℂ} (ψ : (𝓜 f).domain) : (𝓜 f) ψ =ᵐ[volume] f • ψ :=
  coe_mk_ae ψ.prop

/-!
## B. Dense domain
-/

lemma mulOperator_hasDenseDomain {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (𝓜 f).HasDenseDomain := by
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
    (𝓜 (conj ∘ f)).domain = (𝓜 f).domain := by
  ext
  simp only [mulOperator, smul_eq_mul, memHS_iff]
  exact and_congr (iff_of_true (by fun_prop) (by fun_prop)) (by simp)

private lemma exists_monotone_sets_hasFiniteIntegral
    (f g : Space d → ℂ) (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g) :
    ∃ s : ℕ → Set (Space d), Monotone s ∧ ⋃ n, s n = Set.univ ∧ (∀ n, MeasurableSet (s n))
      ∧ ∀ k, k = 1 ∨ k = 2 →
        ∀ n, HasFiniteIntegral (fun x ↦ ‖f x ^ k * g x‖ ^ 2) (volume.restrict (s n)) := by
  obtain ⟨w₁, hw₁, hw₁'⟩ : AEStronglyMeasurable (fun x ↦ f x * g x) := by measurability
  obtain ⟨w₂, hw₂, hw₂'⟩ : AEStronglyMeasurable (fun x ↦ f x ^ 2 * g x) := by measurability
  let s : ℕ → Set (Space d) :=
    fun n ↦ Metric.closedBall 0 n ∩ (w₁ ⁻¹' Metric.closedBall 0 n ∩ w₂ ⁻¹' Metric.closedBall 0 n)
  refine ⟨s, ?_, ?_, by measurability, ?_⟩
  · exact fun _ _ hmn _ hx ↦
      ⟨ Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hmn) hx.1,
        Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hmn) hx.2.1,
        Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hmn) hx.2.2⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    use max ⌈‖x‖⌉.toNat (max ⌈‖w₁ x‖⌉.toNat ⌈‖w₂ x‖⌉.toNat)
    suffices ∀ r : ℝ, 0 ≤ r → r ≤ ⌈r⌉.toNat by simp [s, this]
    intro r hr
    calc
      r ≤ ⌈r⌉ := Int.le_ceil r
      _ = (⌈r⌉.toNat : ℤ) := by simp [Int.ceil_nonneg hr]
      _ = ⌈r⌉.toNat := AddGroupWithOne.intCast_ofNat _
  · intro k hk n
    refine lt_of_le_of_lt (b := ‖(n : ℝ) ^ 2‖ₑ * volume (s n)) ?_ ?_
    · rw [← setLIntegral_const]
      refine setLIntegral_mono_ae' (by measurability) ?_
      filter_upwards [hw₁', hw₂'] with x h₁ h₂ ⟨h₃, h₃'⟩
      apply enorm_le_iff_norm_le.mpr
      simp_rw [norm_pow, norm_norm, RCLike.norm_natCast]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rcases hk <;> simp_all
    · refine ENNReal.mul_lt_top (by norm_num) ?_
      exact measure_inter_lt_top_of_left_ne_top measure_closedBall_lt_top.ne

open Complex InnerProductSpace in
lemma mulOperator_adjoint_domain_le {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (𝓜 f)†.domain ≤ (𝓜 (conj ∘ f)).domain := by
  intro ψ hψ
  let ξ : SpaceDHilbertSpace d := (𝓜 f)† ⟨ψ, hψ⟩
  obtain ⟨s, hs_mono, hs_univ, hs_meas, hs_int⟩ :=
    exists_monotone_sets_hasFiniteIntegral (conj ∘ f) ψ (by fun_prop) ψ.val.aestronglyMeasurable
  let w : ℕ → Space d → ℂ := fun n ↦ (s n).indicator ((conj ∘ f) • ψ)
  have hw : ∀ n, MemHS (w n) := by
    intro n
    refine memHS_iff.mpr ⟨by measurability, by measurability, ?_⟩
    refine lt_of_eq_of_lt ?_ (hs_int 1 (Or.inl rfl) n)
    trans ∫⁻ x in s n, ‖‖w n x‖ ^ 2‖ₑ
    · exact (setLIntegral_eq_of_support_subset fun x hx ↦ by simp_all [w]).symm
    exact setLIntegral_congr_fun (hs_meas n) fun x hx ↦ by simp [w, hx, mul_pow]
  let φ : ℕ → SpaceDHilbertSpace d := fun n ↦ mk (hw n)
  have hφ : ∀ n, φ n ∈ (𝓜 f).domain := by
    intro n
    apply memHS_iff.mpr ⟨by measurability, by measurability, ?_⟩
    refine lt_of_eq_of_lt ?_ (hs_int 2 (Or.inr rfl) n)
    calc
      _ = ∫⁻ x, ‖‖(f • w n) x‖ ^ 2‖ₑ := by
        refine lintegral_congr_ae ?_
        filter_upwards [coe_mk_ae (hw n)] with _ h
        simp [φ, h]
      _ = ∫⁻ x in s n, ‖‖(f • w n) x‖ ^ 2‖ₑ :=
        (setLIntegral_eq_of_support_subset fun x hx ↦ by simp_all [w]).symm
    exact setLIntegral_congr_fun (hs_meas n) fun x hx ↦ by simp [w, hx, ← mul_assoc, ← pow_two]
  suffices ∀ n, ∫⁻ x in s n, ‖‖f x‖ ^ 2 * ‖ψ x‖ ^ 2‖ₑ ≤ ∫⁻ x, ‖‖ξ x‖ ^ 2‖ₑ by
    apply mem_mulOperator_domain_iff.mpr
    refine memHS_iff.mpr ⟨by measurability, by measurability, ?_⟩
    refine lt_of_le_of_lt ?_ (memHS_iff.mp <| coe_hilbertSpace_memHS ξ).2.2
    trans ⨆ n, ∫⁻ x in s n, ‖‖f x‖ ^ 2 * ‖ψ x‖ ^ 2‖ₑ
    · rw [← setLIntegral_univ, ← hs_univ]
      rw [setLIntegral_iUnion_of_directed _ (directed_of_isDirected_le hs_mono)]
      simp [mul_pow]
    exact iSup_le this
  intro n
  suffices ‖φ n‖ ^ 2 ≤ ‖ξ‖ ^ 2 by
    refine le_of_eq_of_le (b := ∫⁻ x, ‖‖φ n x‖ ^ 2‖ₑ) ?_ <| (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
    · calc
        _ = ∫⁻ x in s n, ‖‖w n x‖ ^ 2‖ₑ :=
          setLIntegral_congr_fun (hs_meas n) fun x hx ↦ by simp [w, hx, mul_pow]
        _ = ∫⁻ x, ‖‖w n x‖ ^ 2‖ₑ :=
          setLIntegral_eq_of_support_subset fun x hx ↦ by simp_all [w]
        _ = ∫⁻ x, ‖‖φ n x‖ ^ 2‖ₑ := by
          refine lintegral_congr_ae ?_
          filter_upwards [coe_mk_ae (hw n)] with x h₁
          simp [φ, h₁]
    · exact (memHS_iff.mp <| coe_hilbertSpace_memHS (φ n)).2.2.ne
    · exact (memHS_iff.mp <| coe_hilbertSpace_memHS ξ).2.2.ne
    · suffices h : ∀ ψ : SpaceDHilbertSpace d, ‖ψ‖ ^ 2 = (∫⁻ x, ‖‖ψ x‖ ^ 2‖ₑ).toReal by
        simp only [← h, this]
      intro ψ
      rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
      simp [← ENNReal.toReal_pow, ← ENNReal.rpow_mul_natCast]
  suffices (‖φ n‖ ^ 2) ^ 2 ≤ (‖ξ‖ * ‖φ n‖) ^ 2 by
    by_cases! h : ‖φ n‖ = 0
    · rw [h, zero_pow two_ne_zero]
      exact pow_two_nonneg _
    · rw [pow_two, mul_pow] at this
      refine (mul_le_mul_iff_left₀ <| sq_pos_iff.mpr h).mp this
  calc
    _ = ‖⟪φ n, φ n⟫_ℂ‖ ^ 2 := by simp
    _ = ‖⟪ψ, 𝓜 f ⟨φ n, hφ n⟩⟫_ℂ‖ ^ 2 := by
      refine congrArg (fun r ↦ ‖r‖ ^ 2) ?_
      refine integral_congr_ae ?_
      filter_upwards [coe_mk_ae (hw n), mulOperator_apply_ae ⟨φ n, hφ n⟩] with x h₁ h₂
      by_cases hx : x ∈ s n
      · simp only [φ, h₁, h₂, inner_self_eq_norm_sq_to_K, coe_algebraMap, RCLike.inner_apply,
          Pi.smul_apply', smul_eq_mul]
        calc
          _ = ofReal (‖f x‖ ^ 2 * ‖ψ x‖ ^ 2) := by simp [w, hx, mul_pow]
          _ = (f x * conj (f x)) * (ψ x * conj (ψ x)) := by
            simp_rw [← normSq_eq_norm_sq, Complex.ofReal_mul, normSq_eq_conj_mul_self, mul_comm]
          _ = f x * w n x * conj (ψ x) := by simp [w, hx, mul_assoc]
      · simp [φ, h₁, h₂, w, hx]
    _ = ‖⟪ξ, φ n⟫_ℂ‖ ^ 2 := by
      rw [(adjoint_isFormalAdjoint (mulOperator_hasDenseDomain hf) ⟨ψ, hψ⟩ ⟨φ n, hφ n⟩).symm]
    _ ≤ (‖ξ‖ * ‖φ n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm ξ (φ n)) 2

lemma mulOperator_adjoint_eq_conj {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (𝓜 f)† = 𝓜 (conj ∘ f) := by
  have hFA : (𝓜 f).IsFormalAdjoint (𝓜 (conj ∘ f)) := by
    intro ψ φ
    refine integral_congr_ae ?_
    filter_upwards [mulOperator_apply_ae ψ, mulOperator_apply_ae φ] with x h₁ h₂
    simp [h₁, h₂, mul_assoc, mul_left_comm]
  refine eq_of_le_of_ge ?_ (hFA.le_adjoint <| mulOperator_hasDenseDomain hf)
  refine ⟨mulOperator_adjoint_domain_le hf, fun ψ ψ' hψ ↦ ?_⟩
  refine adjoint_apply_eq (mulOperator_hasDenseDomain hf) ψ fun φ ↦ ?_
  rw [← inner_conj_symm, hψ, (hFA φ ψ').symm, inner_conj_symm]

/-!
### C.1. Self-adjoint
-/

lemma mulOperator_isSelfAdjoint_ofReal
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f) (hf' : conj ∘ f = f) :
    IsSelfAdjoint (𝓜 f) := by
  apply isSelfAdjoint_def.mpr
  rw [mulOperator_adjoint_eq_conj hf, hf']

/-!
## D. Closable & unbounded
-/

lemma mulOperator_isClosable {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (𝓜 f).IsClosable := by
  refine isClosable_of_exists_dense_formalAdjoint ?_ ?_
  · exact mulOperator_hasDenseDomain hf
  · refine ⟨𝓜 (conj ∘ f), ?_, ?_⟩
    · exact mulOperator_hasDenseDomain (by measurability)
    · rw [← mulOperator_adjoint_eq_conj hf]
      exact adjoint_isFormalAdjoint (mulOperator_hasDenseDomain hf)

lemma mulOperator_isUnbounded {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    (𝓜 f).IsUnbounded :=
  ⟨mulOperator_hasDenseDomain hf, mulOperator_isClosable hf⟩

end
end SpaceDHilbertSpace
end QuantumMechanics
