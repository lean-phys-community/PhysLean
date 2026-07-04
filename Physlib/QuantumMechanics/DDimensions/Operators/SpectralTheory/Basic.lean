/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
/-!

# Spectral theory for closed operators

## i. Overview

In this module we develop the basics for the spectral theory of closed unbounded operators.
This forms the basis for the spectral theory of self-adjoint unbounded operators,
which are of central importance in quantum mechanics.

Definitions for subsets of ℂ associated to an operator `T : H →ₗ.[ℂ] H` vary by author.
Here we adopt those used in
[Konrad Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*][Schmudgen2012],
summarized in the following table:

| Subset of ℂ | abbrev. | `D(T - z)` | `R(T - z)` | `(T - z)⁻¹` |
| :---------- | :-----: | :--------: | :--------: | :---------: |
| Regularity domain | | `= ⊥` | | continuous |
| Resolvent set | `ρ` | `= ⊥` | `= ⊤` | continuous |
| Point spectrum | `σᵖ` | `≠ ⊥` | | |
| Residual spectrum | `σʳ` | `= ⊥` | `≠ ⊤` | continuous |
| Continuous spectrum | `σᶜ` | | not closed | |

## ii. Key results

Definitions (corresponding to an operator `T : H →ₗ.[ℂ] H`)
- `LinearPMap.regularityDomain` : The set of regular points. A complex number `z` is a regular
    point if there exists `c > 0` such that `c * ‖x‖ ≤ ‖T x - z • x‖` for all `x : T.domain`.
- `LinearPMap.deficiencySubspace` : Given a complex number `z`, the closed submodule which
    is orthogonal to the range of `T - z • 1`.
- `LinearPMap.defectNumber` : Given a complex number `z`, the rank of the corresponding
    deficiency subspace as a (possibly infinite) cardinal.
- `LinearPMap.numericalRange` (`Θ`) : The set of complex numbers `⟪x, T x⟫_ℂ` as `x` ranges over
    the unit sphere in `T.domain`.
- `LinearPMap.resolventSet` (`ρ`) : The set of complex numbers `z` for which `T - z • 1`
    has a continuous (equivalently, bounded) inverse with domain all of `H`.
- `LinearPMap.spectrum` (`σ`) : The complement of the resolvent set.
- `LinearPMap.pointSpectrum` (`σᵖ`) : The set of complex numbers `z` for which `T - z • 1`
    fails to be invertible.
- `LinearPMap.residualSpectrum` (`σʳ`) : The set of complex numbers `z` for which `T - z • 1`
    has a continuous (equivalently, bounded) inverse with domain not all of `H`.
- `LinearPMap.continuousSpectrum` (`σᶜ`) : The set of complex numbers `z` for which
    the range of `T - z • 1` is not dense in `H`.

Main results
- `regularityDomain_isOpen` : The regularity domain is an open subset of `ℂ`.
- `closure_range_sub_eq_range_closure_sub` : If `z` is a regular point for a closable operator `T`
    then the closure of `(T - z • 1).range` is `(T.closure - z • 1).range`.
- `defectNumber_const` : The defect number is constant on each connected component
    of the regularity domain.
- `compl_closure_numericalRange_subset_regularityDomain` : The regularity domain contains
    the exterior of the numerical range.
- `numericalRange_convex` : The Toeplitz-Hausdorff theorem — the numerical range is a convex set.
- `resolventSet_isOpen` and `spectrum_isClosed` : The resolvent set is an open subset of ℂ
    and its complement, the spectrum, is closed.
- `IsClosed.spectrum_eq` : For a closed operator the spectrum is the union of the point, residual
    and continuous spectra.

## iii. Table of contents

- A. Regularity domain
- B. Deficiency subspace & defect number
- C. Numerical range
  - C.1. The Toeplitz-Hausdorff theorem
- D. Spectrum of a closed operator
  - D.1. Resolvent set
  - D.2. Spectrum
    - D.2.1. Point spectrum
    - D.2.2. Residual spectrum
    - D.2.3. Continuous spectrum
  - D.3. Spectrum decomposition
- E. Resolvent identities

## iv. References

- [Konrad Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*][Schmudgen2012]

-/

TODO "Move spectral theory definitions and lemmas over to Mathlib equivalents if/when available."

@[expose] public section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable section

open Submodule
open Metric
open InnerProductSpace
open Complex
open ComplexConjugate
open Set
open Pointwise

/-- The resolvent, `(T - z • 1)⁻¹`. -/
abbrev resolvent (T : H →ₗ.[ℂ] H) (z : ℂ) : H →ₗ.[ℂ] H := (T - z • 1).inverse

@[inherit_doc resolvent]
scoped notation "𝑅" => resolvent

/-!
## A. Regularity domain
-/

/-- `IsLowerBound T z c` is the property that `c * ‖x‖ ≤ ‖T x - z • x‖` for all `x : T.domain`. -/
def IsLowerBound (T : H →ₗ.[ℂ] H) (z : ℂ) (c : ℝ) : Prop := ∀ x : T.domain, c * ‖x‖ ≤ ‖T x - z • x‖

lemma isLowerBound_neg {T : H →ₗ.[ℂ] H} {z : ℂ} {c : ℝ} (h : IsLowerBound T z c) :
    IsLowerBound (-T) (-z) c :=
  fun x ↦ by simpa [neg_apply, norm_neg_add] using h x

lemma isLowerBound_of_right_le
    {T : H →ₗ.[ℂ] H} {z : ℂ} {c₁ c₂ : ℝ} (hle : c₁ ≤ c₂) (h : IsLowerBound T z c₂) :
    IsLowerBound T z c₁ :=
  fun x ↦ (mul_le_mul_of_nonneg_right hle (norm_nonneg x)).trans (h x)

lemma isLowerBound_of_left_le
    {T₁ T₂ : H →ₗ.[ℂ] H} (hle : T₁ ≤ T₂) {z : ℂ} {c : ℝ} (h : IsLowerBound T₂ z c) :
    IsLowerBound T₁ z c :=
  fun x ↦ @hle.2 x ⟨x, hle.1 x.2⟩ rfl ▸ h ⟨x, hle.1 x.2⟩

lemma isLowerBound_closure
    {T : H →ₗ.[ℂ] H} {z : ℂ} {c : ℝ} (h : IsLowerBound T z c) : IsLowerBound T.closure z c := by
  by_cases hT : T.IsClosable
  · intro x
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp <|
      hT.graph_closure_eq_closure_graph ▸ T.closure.mem_graph x
    rw [nhds_prod_eq] at hb'
    refine le_of_tendsto_of_tendsto' (hb'.fst.norm.const_mul c)
      ((hb'.snd.sub <| hb'.fst.const_smul z).norm) fun n ↦ ?_
    obtain ⟨y, hy₁, hy₂⟩ := (mem_graph_iff _).mp (hb n)
    exact hy₁ ▸ hy₂ ▸ h y
  · rwa [closure_def' hT]

/-- The regular points for `T`.

  `z : ℂ` is a regular point for `T` iff there exists a constant `c > 0` such that
  `c * ‖x‖ ≤ ‖(T - z • 1) x‖` for all `x ∈ T.domain`. -/
def regularityDomain (T : H →ₗ.[ℂ] H) : Set ℂ := {z : ℂ | ∃ c > 0, IsLowerBound T z c}

@[simp]
lemma regularityDomain_neg (T : H →ₗ.[ℂ] H) : (-T).regularityDomain = -T.regularityDomain := by
  ext z
  constructor
  · exact fun ⟨c, hc, h_bound⟩ ↦ ⟨c, hc, neg_neg T ▸ isLowerBound_neg h_bound⟩
  · exact fun ⟨c, hc, h_bound⟩ ↦ ⟨c, hc, neg_neg z ▸ isLowerBound_neg h_bound⟩

@[simp]
lemma regularityDomain_smul (T : H →ₗ.[ℂ] H) {w : ℂ} (hw : w ≠ 0) :
    (w • T).regularityDomain = w • T.regularityDomain := by
  ext z
  constructor
  · intro ⟨c, hc, h_bound⟩
    refine ⟨w⁻¹ * z, ?_, ?_⟩
    · refine ⟨‖w‖⁻¹ * c, by positivity, fun x ↦ ?_⟩
      rw [mul_assoc]
      apply (inv_mul_le_iff₀ <| norm_pos_iff.mpr hw).mpr
      rw [← norm_smul, smul_sub, smul_smul, mul_inv_cancel_left₀ hw]
      exact h_bound x
    · simp [hw]
  · intro ⟨u, ⟨c, hc, h_bound⟩, huz⟩
    refine ⟨‖w‖ * c, by positivity, fun x ↦ ?_⟩
    rw [mul_assoc]
    apply (le_inv_mul_iff₀ <| norm_pos_iff.mpr hw).mp
    refine le_of_le_of_eq (h_bound x) ?_
    simp [← norm_inv, ← norm_smul, smul_sub, smul_smul, ← huz, hw]

/-- `T ≤ T'` implies `T'.regularityDomain ⊆ T.regularityDomain`. -/
lemma regularityDomain_antitone : Antitone (regularityDomain (H := H)) :=
  fun _ _ hle _ ⟨c, hc, h⟩ ↦ ⟨c, hc, isLowerBound_of_left_le hle h⟩

/-- `z` is a regular point for `T` iff `T - z • 1` has
  a continuous (equivalently, bounded) inverse. -/
lemma mem_regularityDomain_iff {T : H →ₗ.[ℂ] H} {z : ℂ} :
    z ∈ T.regularityDomain ↔ (T - z • 1).toFun.ker = ⊥ ∧ Continuous (𝑅 T z) := by
  constructor
  · intro ⟨c, hc, h_bound⟩
    have h_ker : (T - z • 1).toFun.ker = ⊥ := by
      ext x
      constructor <;> intro
      · have : c * ‖x‖ ≤ 0 → ‖x‖ ≤ 0 := fun h' ↦ nonpos_of_mul_nonpos_right h' hc
        specialize h_bound ⟨x, x.2.1⟩
        simp_all [sub_apply]
      · simp_all
    use h_ker
    apply LinearMap.continuous_iff_bounded.mpr
    refine ⟨c⁻¹, inv_pos.mpr hc, fun ⟨x, hx⟩ ↦ ?_⟩
    rw [inverse_domain] at hx
    obtain ⟨y, hy⟩ := hx
    specialize h_bound ⟨y, y.2.1⟩
    simp_all [le_inv_mul_iff₀, sub_apply, inverse_apply_eq h_ker (y := ⟨x, hx⟩) hy]
  · intro ⟨h_ker, h_cont⟩
    obtain ⟨c, hc, h_bound⟩ := LinearMap.continuous_iff_bounded.mp h_cont
    refine ⟨c⁻¹, inv_pos.mpr hc, fun x ↦ ?_⟩
    apply (inv_mul_le_iff₀ hc).mpr
    have hx : ↑x ∈ (T - z • 1).domain := by simp [sub_domain]
    specialize h_bound ⟨(T - z • 1) ⟨x, hx⟩, by simp [inverse_domain]⟩
    simp only [toFun_eq_coe, inverse_apply_eq h_ker (x := ⟨x, hx⟩), coe_norm] at h_bound
    simp_all [sub_apply]

/-- The regularity domain of `T` contains open balls with radii controlled by the lower bounds. -/
lemma ball_subset_regularityDomain
    {T : H →ₗ.[ℂ] H} {z : ℂ} {c : ℝ} (h : IsLowerBound T z c) : ball z c ⊆ T.regularityDomain := by
  intro z' hzc
  refine ⟨c - ‖z - z'‖, by simp_all [dist_eq, norm_sub_rev], fun x ↦ ?_⟩
  calc
    _ = c * ‖x‖ - ‖(z - z') • x‖ := by simp [sub_mul, norm_smul]
    _ ≤ ‖T x - z • x‖ - ‖(z - z') • x‖ := by linarith [h x]
    _ ≤ ‖T x - z • x + (z - z') • x‖ := norm_sub_le_norm_add _ _
    _ = ‖T x - z' • x‖ := by simp [sub_smul]

/-- The regularity domain is an open set. -/
lemma regularityDomain_isOpen (T : H →ₗ.[ℂ] H) : IsOpen T.regularityDomain :=
  isOpen_iff.mpr fun _ ⟨c, hc, h⟩ ↦ ⟨c, hc, ball_subset_regularityDomain h⟩

/-- `T` and `T.closure` have the same regularity domain. -/
lemma regularityDomain_closure (T : H →ₗ.[ℂ] H) :
    T.closure.regularityDomain = T.regularityDomain :=
  eq_of_le_of_ge (regularityDomain_antitone T.le_closure)
    fun _ ⟨c, hc, h⟩ ↦ ⟨c, hc, isLowerBound_closure h⟩

lemma IsClosable.closure_range_sub_eq_range_closure_sub [CompleteSpace H]
    {T : H →ₗ.[ℂ] H} (hT : T.IsClosable) {z : ℂ} (hz : z ∈ T.regularityDomain) :
    (T - z • 1).toFun.range.closure = (T.closure - z • 1).toFun.range := by
  ext y
  constructor
  · intro hy
    obtain ⟨b, hb, hby⟩ := mem_closure_iff_seq_limit.mp hy
    let x : ℕ → H := fun n ↦ (hb n).choose
    have hx : ∀ n, x n ∈ T.domain := fun n ↦ (hb n).choose.2.1
    have hx' : ∀ n, T ⟨x n, hx n⟩ - z • x n = b n := fun n ↦ (hb n).choose_spec
    have hCS : CauchySeq x := by
      apply Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
      obtain ⟨c, hc, h_bound⟩ := hz
      obtain ⟨N, hN⟩ := cauchySeq_iff'.mp hby.cauchySeq (c * ε) (mul_pos hc hε)
      refine ⟨N, fun n hn ↦ Eq.trans_lt (dist_eq_norm _ _) ((mul_lt_mul_iff_right₀ hc).mp ?_)⟩
      calc
        _ ≤ ‖T (⟨x n, hx n⟩ - ⟨x N, hx N⟩) - z • (x n - x N)‖ := h_bound _
        _ = ‖b n - b N‖ := by rw [← hx', ← hx', map_sub, smul_sub, sub_sub_sub_comm]
        _ = dist (b n) (b N) := (dist_eq_norm _ _).symm
        _ < (c * ε) := hN n hn
    obtain ⟨x₀, hx₀⟩ := CompleteSpace.complete hCS
    suffices (x₀, y + z • x₀) ∈ T.closure.graph by
      obtain ⟨x₀', rfl, _⟩ := (mem_graph_iff _).mp this
      use ⟨x₀', by simp [sub_domain]⟩
      simp_all [sub_apply]
    rw [← hT.graph_closure_eq_closure_graph]
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n ↦ (x n, b n + z • x n), fun n ↦ ?_, ?_⟩
    · exact (mem_graph_iff _).mpr ⟨⟨x n, hx n⟩, by simp [← hx' n]⟩
    · exact Filter.Tendsto.prodMk_nhds hx₀ (hby.add <| Filter.Tendsto.const_smul hx₀ z)
  · intro ⟨⟨x, hx⟩, hxy⟩
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp <|
      hT.graph_closure_eq_closure_graph ▸ T.closure.mem_graph ⟨x, hx.1⟩
    simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff] at hb
    rw [nhds_prod_eq] at hb'
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n ↦ (b n).2 - z • (b n).1, fun n ↦ ?_, hxy ▸ hb'.snd.sub (hb'.fst.const_smul z)⟩
    obtain ⟨u, hu₁, hu₂⟩ := hb n
    use ⟨u, by simp [sub_domain]⟩
    simp [sub_apply, ← hu₁, hu₂]

lemma IsClosed.sub_range_isClosed [CompleteSpace H]
    {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) {z : ℂ} (hz : z ∈ T.regularityDomain) :
    _root_.IsClosed ((T - z • 1).toFun.range : Set H) :=
  (hT.isClosable.isClosed_iff.mp hT ▸
    hT.isClosable.closure_range_sub_eq_range_closure_sub hz) ▸ isClosed_closure

/-- `(T.closure - z • 1).rangeᗮ = (T† - conj z • 1).ker` -/
lemma IsUnbounded.orthogonal_closure_sub_range [CompleteSpace H]
    {T : H →ₗ.[ℂ] H} (hT : T.IsUnbounded) (z : ℂ) :
    (T.closure - z • 1).toFun.rangeᗮ
      = (T† - conj z • 1).toFun.ker.map (T† - conj z • 1).domain.subtype := by
  let S := T.closure - z • 1
  have hS_domain : S.domain = T.closure.domain := by simp [S, sub_domain]
  have hS_dense : S.HasDenseDomain := hT.hasDenseDomain.mono (by simp [hS_domain, T.le_closure.1])
  have hS_adjoint : S† = T† - conj z • 1 := by
    rw [← hT.adjoint_closure_eq_adjoint]
    refine (eq_of_le_of_domain_eq ?_ ?_).symm
    · refine le_of_eq_of_le ?_ (adjoint_sub_le_sub_adjoint T.closure (z • 1) hS_dense)
      rcases eq_zero_or_neZero z with rfl | hz₀
      · simp
      · simp [adjoint_smul _ hz₀.ne]
    · ext x
      simp only [sub_domain, smul_domain, one_domain, le_top, inf_of_le_left]
      constructor <;> intro h
      · apply mem_adjoint_domain_of_exists
        use T.closure† ⟨x, h⟩ - conj z • x
        intro y
        have h_inner : ⟪T.closure† ⟨x, h⟩, y⟫_ℂ = ⟪x, T.closure ⟨y, hS_domain ▸ y.2⟩⟫_ℂ :=
          adjoint_isFormalAdjoint hT.hasDenseDomain.closure ⟨x, h⟩ ⟨y, hS_domain ▸ y.2⟩
        simp [inner_sub_left, h_inner, S, sub_apply, inner_sub_right, inner_smul_left,
          inner_smul_right]
      · apply mem_adjoint_domain_of_exists
        use S† ⟨x, h⟩ + conj z • x
        intro y
        have h_inner : ⟪S† ⟨x, h⟩, y⟫_ℂ = ⟪x, S ⟨y, by simp [hS_domain]⟩⟫_ℂ :=
          adjoint_isFormalAdjoint hS_dense ⟨x, h⟩ ⟨y, by simp [hS_domain]⟩
        simp [inner_add_left, h_inner, S, sub_apply, inner_sub_right, inner_smul_left,
          inner_smul_right]
  exact hS_adjoint ▸ hS_dense.orthogonal_range

/-- `(T† - conj z • 1).kerᗮ = (T.closure - z • 1).range` -/
lemma IsUnbounded.orthogonal_adjoint_sub_ker [CompleteSpace H]
    {T : H →ₗ.[ℂ] H} (hT : T.IsUnbounded) {z : ℂ} (hz : z ∈ T.regularityDomain) :
    ((T† - conj z • 1).toFun.ker.map (T† - conj z • 1).domain.subtype)ᗮ
      = (T.closure - z • 1).toFun.range := by
  have hT' : IsClosable T.closure := hT.isClosable.closureIsClosable
  have hTcl : T.closure.closure = T.closure := hT'.isClosed_iff.mp hT.isClosable.closure_isClosed
  rw [← hTcl, ← hT.orthogonal_closure_sub_range, orthogonal_orthogonal_eq_closure]
  exact hT'.closure_range_sub_eq_range_closure_sub (T.regularityDomain_closure ▸ hz)

/-!
## B. Deficiency subspace & defect number
-/

/-- For a partial linear map `T` and any complex number `z`, the closed submodule which
  is orthogonal to the range of `T - z • 1`.

  `T.defectNumber z` is defined as the rank of this subspace. -/
def deficiencySubspace (T : H →ₗ.[ℂ] H) (z : ℂ) : ClosedSubmodule ℂ H :=
  ⟨(T - z • 1).toFun.rangeᗮ, isClosed_orthogonal _⟩

@[simp]
lemma deficiencySubspace_coe (T : H →ₗ.[ℂ] H) (z : ℂ) :
    T.deficiencySubspace z = (T - z • 1).toFun.rangeᗮ := rfl

/-- The rank of `T.deficiencySubspace z = (T - z • 1).rangeᗮ`. -/
def defectNumber (T : H →ₗ.[ℂ] H) (z : ℂ) : Cardinal := Module.rank ℂ (T.deficiencySubspace z)

lemma defectNumber_eq (T : H →ₗ.[ℂ] H) (z : ℂ) :
    T.defectNumber z = Module.rank ℂ (T.deficiencySubspace z) := rfl

lemma IsClosed.defectNumber_eq_zero_iff [CompleteSpace H]
    {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) {z : ℂ} (hz : z ∈ T.regularityDomain) :
    T.defectNumber z = 0 ↔ (T - z • 1).toFun.range = ⊤ := by
  haveI := hT.sub_range_isClosed hz -- needed for HasOrthogonalProjection
  exact rank_eq_zero.trans orthogonal_eq_bot_iff

/-- `T` and `T.closure` have the same defect number at points in their regularity domain. -/
lemma defectNumber_closure [CompleteSpace H]
    {T : H →ₗ.[ℂ] H} {z : ℂ} (hz : z ∈ T.regularityDomain) :
    T.closure.defectNumber z = T.defectNumber z := by
  by_cases hT : T.IsClosable
  · refine congrArg (fun p : Submodule ℂ H ↦ Module.rank ℂ p) ?_
    simp [← hT.closure_range_sub_eq_range_closure_sub hz]
  · rw [closure_def' hT]

lemma _root_.Submodule.inf_ne_bot_of_rank_lt
    {E F : Submodule ℂ H} [E.HasOrthogonalProjection] (h_rank : Module.rank ℂ E < Module.rank ℂ F) :
    Eᗮ ⊓ F ≠ ⊥ := by
  let Φ : F →L[ℂ] E := E.orthogonalProjectionOnto ∘L F.subtypeL
  have hΦ : ¬(⇑Φ).Injective := fun h' ↦ not_le_of_gt h_rank (Φ.rank_le_of_injective h')
  obtain ⟨x₁, x₂, h, hx⟩ := Function.not_injective_iff.mp hΦ
  let y : H := x₁ - x₂
  have hy : y ≠ 0 := fun h' ↦ hx (SetLike.coe_eq_coe.mp <| sub_eq_zero.mp h')
  have hF : y ∈ F := sub_mem (coe_mem x₁) (coe_mem x₂)
  have hE : y ∈ Eᗮ := orthogonalProjectionOnto_eq_zero_iff.mp
    (_root_.map_sub Φ _ _ ▸ sub_eq_zero.mpr h)
  exact fun hEF ↦ hy ((mem_bot ℂ).mp <| hEF ▸ ⟨hE, hF⟩)

lemma IsClosed.exists_inner_eq_zero_of_defectNumber_lt [CompleteSpace H]
    {T : H →ₗ.[ℂ] H} (hT : T.IsClosed)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ T.regularityDomain) (h : T.defectNumber z₁ < T.defectNumber z₂) :
    ∃ x : T.domain, x ≠ 0 ∧ ⟪T x - z₁ • x, T x - z₂ • x⟫_ℂ = 0 := by
  obtain ⟨y, h_inf, hy⟩ := (Submodule.ne_bot_iff _).mp (inf_ne_bot_of_rank_lt h)
  obtain ⟨hy₁, hy₂⟩ := mem_inf.mp h_inf
  haveI := hT.sub_range_isClosed hz₁ -- needed for `orthogonal_orthogonal`
  simp only [deficiencySubspace_coe, orthogonal_orthogonal] at hy₁ hy₂
  obtain ⟨⟨x, hx⟩, hxy⟩ := hy₁
  refine ⟨⟨x, hx.1⟩, fun h ↦ hy ?_, ?_⟩
  · simp [← hxy, coe_eq_zero.mp, (mk_eq_zero _ _).mp h]
  · apply (mem_orthogonal' _ _).mp at hy₂
    simp [← hy₂ ((T - z₂ • 1) ⟨x, hx.1, by simp⟩) (by simp), sub_apply, ← hxy]

lemma IsClosable.defectNumber_eq_of_mem_ball [CompleteSpace H] {T : H →ₗ.[ℂ] H} (hT : T.IsClosable)
    {z₁ z₂ : ℂ} {c : ℝ} (h : IsLowerBound T z₁ c) (h_ball : z₂ ∈ ball z₁ c) :
    T.defectNumber z₁ = T.defectNumber z₂ := by
  by_cases hz₁ : z₁ ∈ T.regularityDomain
  · have hz₂ : z₂ ∈ T.regularityDomain := ball_subset_regularityDomain h h_ball
    rw [← defectNumber_closure hz₁, ← defectNumber_closure hz₂]
    rw [← regularityDomain_closure] at hz₁ hz₂
    by_contra! hne
    let Tcl : H →ₗ.[ℂ] H := T.closure
    obtain ⟨x, hx, h'⟩ : ∃ x : Tcl.domain, x ≠ 0 ∧ ⟪Tcl x - z₂ • x, Tcl x - z₁ • x⟫_ℂ = 0 := by
      rcases lt_or_gt_of_ne hne with hle | hle
      · simp_rw [inner_eq_zero_symm]
        exact hT.closure_isClosed.exists_inner_eq_zero_of_defectNumber_lt hz₁ hle
      · exact hT.closure_isClosed.exists_inner_eq_zero_of_defectNumber_lt hz₂ hle
    refine not_le (a := ‖z₁ - z₂‖ * ‖x‖).mpr ?_ le_rfl
    refine lt_of_lt_of_le (b := ‖Tcl x - z₁ • x‖) ?_ ?_
    · refine lt_of_lt_of_le ?_ (isLowerBound_closure h x)
      exact (mul_lt_mul_iff_left₀ <| norm_pos_iff.mpr hx).mpr (mem_ball_iff_norm'.mp h_ball)
    · rcases eq_or_ne (Tcl x - z₁ • x) 0 with heq | hne
      · exact heq ▸ norm_zero (E := H) ▸ mul_nonneg (norm_nonneg _) (norm_nonneg x)
      · apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hne)).mp
        trans ‖⟪Tcl x - z₂ • x - (z₁ - z₂) • x, Tcl x - z₁ • x⟫_ℂ‖
        · simp [sub_smul, pow_two]
        rw [inner_sub_left, h', zero_sub, inner_smul_left, norm_neg, norm_mul, norm_conj, mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
  · exact absurd ⟨c, dist_nonneg.trans_lt h_ball, h⟩ hz₁

/-- The defect number is constant on each connected component of the regularity domain. -/
lemma IsClosable.defectNumber_const [CompleteSpace H]
    {T : H →ₗ.[ℂ] H} (hT : T.IsClosable)
    {z₁ z₂ : ℂ} (hz : z₂ ∈ connectedComponentIn T.regularityDomain z₁) :
    T.defectNumber z₁ = T.defectNumber z₂ := by
  by_cases hz₁ : z₁ ∈ T.regularityDomain
  · have h_joined : JoinedIn T.regularityDomain z₁ z₂ := by
      haveI := T.regularityDomain_isOpen.locPathConnectedSpace
      have hz₂ : z₂ ∈ T.regularityDomain := connectedComponentIn_subset _ _ hz
      apply (joinedIn_iff_joined hz₁ hz₂).mpr
      rw [← mem_pathComponent_iff, pathComponent_eq_connectedComponent]
      exact mem_of_mem_image_val (connectedComponentIn_eq_image hz₁ ▸ hz)
    let path : Path z₁ z₂ := h_joined.somePath
    by_contra! hne
    let a : unitInterval := sSup {r | ∀ r' ≤ r, T.defectNumber (path r') = T.defectNumber z₁}
    have ha : ∀ r < a, T.defectNumber (path r) = T.defectNumber z₁ := by
      intro r hr
      obtain ⟨b, hb, hrb⟩ := lt_sSup_iff.mp hr
      exact hb r hrb.le
    let c : ℝ := (h_joined.somePath_mem a).choose
    have hc_pos : 0 < c := (h_joined.somePath_mem a).choose_spec.1
    have hc_bound : IsLowerBound T (path a) c := (h_joined.somePath_mem a).choose_spec.2
    obtain ⟨ε, hε, hε_ball⟩ : ∃ ε > 0, ball a ε ⊆ path ⁻¹' ball (path a) c := by
      apply Metric.mem_nhds_iff.mp
      refine (IsOpen.mem_nhds_iff ?_).mpr ?_
      · exact path.continuous.isOpen_preimage _ isOpen_ball
      · simp [hc_pos]
    obtain ⟨b₁, h₁, h₁'⟩ : ∃ b ∈ ball a ε, T.defectNumber (path b) = T.defectNumber z₁ := by
      rcases le_or_gt ε a with hle | hlt
      · let r : ℝ := a - ε / 2
        have hr : 0 ≤ r := by dsimp [r]; linarith
        have hr' : r < a := sub_lt_self _ (half_pos hε)
        use ⟨r, hr, by linarith [a.2.2]⟩
        exact ⟨by simp [dist, r, abs_div, abs_of_nonneg hε.le, hε], ha _ hr'⟩
      · exact ⟨0, by simp [dist, abs_of_nonneg a.2.1, hlt], by rw [path.source]⟩
    obtain ⟨b₂, h₂, h₂'⟩ : ∃ b ∈ ball a ε, T.defectNumber (path b) ≠ T.defectNumber z₁ := by
      by_cases! h₀ : a < 1
      · by_contra! h'
        let r : unitInterval :=
          ⟨min (a + ε / 2) 1, le_inf_iff.mpr ⟨by linarith [a.2.1], zero_le_one⟩, inf_le_right⟩
        refine not_le_of_gt (a := a) (b := r) ?_ ?_
        · apply (Set.inclusion_lt_inclusion <| Set.subset_univ _).mp
          simp [r, hε, h₀]
        · refine le_sSup_iff.mpr fun _ hub ↦ hub fun b hbr ↦ ?_
          rcases lt_or_ge b a with hlt | hle
          · exact ha b hlt
          · refine h' b ?_
            apply mem_ball.mpr
            calc
              _ = (b : ℝ) - a := by simp [dist, hle]
              _ ≤ r - a := by simp [hbr]
              _ = min (ε / 2) (1 - a) := by simp [r, ← min_sub_sub_right]
              _ < ε := by simp [hε]
      · have : a = 1 := eq_of_le_of_ge a.2.2 h₀
        refine ⟨a, mem_ball_self hε, by rw [this, path.target]; exact hne.symm⟩
    apply h₁' ▸ h₂'
    rw [← defectNumber_eq_of_mem_ball hT hc_bound (hε_ball h₁)]
    rw [← defectNumber_eq_of_mem_ball hT hc_bound (hε_ball h₂)]
  · exact ((mem_empty_iff_false z₂).mp (connectedComponentIn_eq_empty hz₁ ▸ hz)).elim

/-!
## C. Numerical range
-/

/-- The set `{⟪x, T x⟫_ℂ | x ∈ T.domain ∧ ‖x‖ = 1} ⊆ ℂ`. -/
def numericalRange (T : H →ₗ.[ℂ] H) : Set ℂ := (fun x ↦ ⟪↑x, T x⟫_ℂ) '' {x : T.domain | ‖x‖ = 1}

@[inherit_doc numericalRange]
scoped notation "Θ" => numericalRange

lemma numericalRange_eq (T : H →ₗ.[ℂ] H) : Θ T = (fun x ↦ ⟪↑x, T x⟫_ℂ) '' {x | ‖x‖ = 1} := rfl

lemma mem_numericalRange {T : H →ₗ.[ℂ] H} {x : T.domain} (hx : x ≠ 0) :
    (‖x‖ ^ 2)⁻¹ * ⟪↑x, T x⟫_ℂ ∈ Θ T := by
  refine ⟨ofReal ‖x‖⁻¹ • x, ?_, ?_⟩
  · simp [norm_smul, inv_mul_cancel₀, hx]
  · simp [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, pow_two]

lemma numericalRange_nonempty {T : H →ₗ.[ℂ] H} (hT : T.domain ≠ ⊥) : (Θ T).Nonempty := by
  obtain ⟨x, hx, hx'⟩ := exists_mem_ne_zero_of_ne_bot hT
  exact ⟨_, mem_numericalRange (x := ⟨x, hx⟩) (Subtype.coe_ne_coe.mp hx')⟩

@[simp]
lemma numericalRange_neg (T : H →ₗ.[ℂ] H) : Θ (-T) = -Θ T := by
  ext
  simp [numericalRange_eq, neg_eq_iff_eq_neg]

@[simp]
lemma numericalRange_smul (T : H →ₗ.[ℂ] H) (c : ℂ) : Θ (c • T) = c • Θ T := by
  ext
  simp [numericalRange_eq, inner_smul_right, mem_smul_set]

lemma numericalRange_sub_const (T : H →ₗ.[ℂ] H) (c : ℂ) : Θ (T - c • 1) = Θ T - {c} := by
  ext z
  constructor
  · intro ⟨x, hx, hxz⟩
    refine ⟨z + c, ⟨⟨x, x.2.1⟩, hx, ?_⟩, by simp⟩
    simp_all [← hxz, sub_apply, inner_sub_right, inner_smul_right]
  · intro ⟨z', ⟨x, hx, hxz⟩, hcz⟩
    simp only [mem_singleton_iff, exists_eq_left] at hcz
    refine ⟨⟨x, by simp [sub_domain]⟩, hx, ?_⟩
    simp_all [← hcz, ← hxz, sub_apply, inner_sub_right, inner_smul_right]

/-- The regularity domain contains the exterior of the numerical range. -/
lemma compl_closure_numericalRange_subset_regularityDomain (T : H →ₗ.[ℂ] H) :
    (_root_.closure (Θ T))ᶜ ⊆ T.regularityDomain := by
  intro z hz
  by_cases hT : T.domain = ⊥
  · refine ⟨1, zero_lt_one, fun ⟨x, hx⟩ ↦ ?_⟩
    rw [hT] at hx
    simp_all
  · use infDist z (Θ T)
    constructor
    · exact (infDist_pos_iff_notMem_closure <| numericalRange_nonempty hT).mp hz
    · intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · let y : T.domain := ofReal ‖x‖⁻¹ • x
        have hy : ‖y‖ = 1 := by simp [y, norm_smul, inv_mul_cancel₀, hx]
        have hy' : ‖x‖ ^ 2 * ⟪↑y, T y⟫_ℂ = ⟪↑x, T x⟫_ℂ := by
          simp_rw [y, map_smul, SetLike.val_smul, inner_smul_left, inner_smul_right, conj_ofReal,
            ← mul_assoc, pow_two, ← ofReal_mul]
          field_simp
          simp
        apply (mul_le_mul_iff_left₀ <| norm_pos_iff.mpr hx).mp
        rw [mul_assoc, ← pow_two, mul_comm _ ‖x‖]
        calc
          _ ≤ ‖z - ⟪↑y, T y⟫_ℂ‖ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right
            (dist_eq z _ ▸ infDist_le_dist_of_mem ⟨y, hy, rfl⟩) (pow_two_nonneg _)
          _ = ‖⟪↑y, T y⟫_ℂ * ‖x‖ ^ 2 - z * ‖x‖ ^ 2‖ := by simp [norm_sub_rev, ← sub_mul]
          _ = ‖⟪↑x, T x⟫_ℂ - z * ‖x‖ ^ 2‖ := by rw [mul_comm, hy']
          _ = ‖⟪↑x, T x - z • x⟫_ℂ‖ := by simp [inner_sub_right, inner_smul_right]
          _ ≤ ‖x‖ * ‖T x - z • x‖ := norm_inner_le_norm _ _

/-!
### C.1. The Toeplitz-Hausdorff theorem
-/

private lemma exists_phase_add_im_eq_zero (z₁ z₂ : ℂ) :
    ∃ θ : ℝ, (exp (I * θ) * z₁ + exp (-I * θ) * z₂).im = 0 := by
  let g : ℝ → ℝ := fun θ ↦ (exp (I * θ) * z₁ + exp (-I * θ) * z₂).im
  have hg : g Real.pi = -g 0 := by simp [g, mul_comm I, exp_neg, add_comm]
  have hmem : (0 : ℝ) ∈ Set.uIcc (g 0) (g Real.pi) := by
    rw [hg]
    rcases le_total (g 0) 0 with h | h
    exacts [Set.mem_uIcc.mpr (.inl ⟨h, by linarith⟩), Set.mem_uIcc.mpr (.inr ⟨by linarith, h⟩)]
  obtain ⟨θ, -, hθ⟩ := intermediate_value_uIcc (by fun_prop : Continuous g).continuousOn hmem
  exact ⟨θ, hθ⟩

/-- The Toeplitz-Hausdorff theorem. -/
theorem numericalRange_convex (T : H →ₗ.[ℂ] H) : Convex ℝ (Θ T) := by
  intro z₀ hz₀ z₁ hz₁ a b ha hb hab
  rcases eq_or_ne z₁ z₀ with rfl | hz
  · simp [← add_mul, eq_sub_iff_add_eq.mpr hab, hz₁]
  · apply sub_ne_zero.mpr at hz
    obtain ⟨x₀, hx₀, _⟩ := hz₀
    obtain ⟨x₁, hx₁, _⟩ := hz₁
    -- Apply an affine transformation to effectively move the endpoints `z₀` and `z₁` to `0` and `1`
    let S : H →ₗ.[ℂ] H := (z₁ - z₀)⁻¹ • (T - z₀ • 1)
    let y₀ : S.domain := ⟨x₀, by simp [S, sub_domain]⟩
    let y₁ : S.domain := ⟨x₁, by simp [S, sub_domain]⟩
    have hy₀ : ‖y₀‖ = 1 := hx₀
    have hy₁ : ‖y₁‖ = 1 := hx₁
    have h₀ : ⟪↑y₀, S y₀⟫_ℂ = 0 := by simp_all [S, y₀, sub_apply, inner_smul_right, inner_sub_right]
    have h₁ : ⟪↑y₁, S y₁⟫_ℂ = 1 := by simp_all [S, y₁, sub_apply, inner_smul_right, inner_sub_right]
    suffices ofReal '' unitInterval ⊆ Θ S by
      have hba : a = 1 - b := by linarith
      rw [numericalRange_smul, numericalRange_sub_const] at this
      obtain ⟨c, ⟨d, ⟨x, hx, hxd⟩, hdc⟩, hca⟩ := (image_subset_iff.mp this) ⟨hb, by linarith⟩
      simp only [mem_singleton_iff, exists_eq_left] at hca hdc hxd
      simp only [real_smul, smul_eq_mul] at *
      use x, hx
      simp_rw [hxd, hba, ofReal_sub, ofReal_one, ← hca, ← hdc]
      field_simp
      simp [mul_sub, mul_comm]
    -- First pick `θ` so that `y₂ ≔ eⁱᶿy₁` satisfies `⟪y₀, S y₂⟫ + ⟪y₂, S y₀⟫ ∈ ℝ`
    obtain ⟨θ, hθ⟩ := exists_phase_add_im_eq_zero ⟪↑y₀, S y₁⟫_ℂ ⟪↑y₁, S y₀⟫_ℂ
    let y₂ : S.domain := exp (I * θ) • y₁
    have hy₂ : ‖y₂‖ = 1 := by simp [y₂, norm_smul, hy₁]
    have hy_im : (⟪↑y₀, S y₂⟫_ℂ).im = -(⟪↑y₂, S y₀⟫_ℂ).im := by
      apply eq_neg_iff_add_eq_zero.mpr
      simp [← hθ, y₂, map_smul, SetLike.val_smul, inner_smul_left, inner_smul_right, ← exp_conj]
    have h₂ : ⟪↑y₂, S y₂⟫_ℂ = 1 := by
      simp [y₂, map_smul, inner_smul_left, inner_smul_right, h₁, ← exp_conj, ← exp_add]
    -- `f` parametrizes the line connecting `y₀` and `y₂` and never vanishes because `y₀` and `y₂`
    -- are linearly independent (since `y₀ = λy₂` implies `0 = ⟪y₀, S y₀⟫ = |λ|²⟪y₂, S y₂⟫ = |λ|²`).
    let f : ℝ → S.domain := fun r ↦ (1 - r : ℂ) • y₀ + (r : ℂ) • y₂
    have hf : ∀ r, f r ≠ 0 := by
      intro r hr
      rcases eq_or_ne r 0 with rfl | hr'
      · exact (hy₁ ▸ zero_ne_one).symm (norm_eq_zero.mpr (by simp_all [f]))
      · apply (pow_ne_zero 2 hr').symm
        apply ofReal_inj.mp
        calc
          _ = (1 - r) ^ 2 * ⟪↑y₀, S y₀⟫_ℂ := by simp [h₀]
          _ = ⟪↑((1 - r : ℂ) • y₀), S ((1 - r : ℂ) • y₀)⟫_ℂ := by
            simp [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, pow_two]
          _ = ⟪↑(-(r • y₂)), S (-(r • y₂))⟫_ℂ := by simp [eq_neg_iff_add_eq_zero.mpr hr]
        simp [map_neg, ← Complex.coe_smul, map_smul, inner_smul_left, inner_smul_right, pow_two, h₂]
    -- `g r = ⟪f r, S (f r)⟫_ℂ / ‖f r‖²` is real (by def of `θ`) and clearly in `Θ S`.
    -- `g 0 = 0`, `g 1 = 1` and continuity ensure that all of `[0,1]` is also in `Θ S`.
    let g : ℝ → ℝ := fun t ↦ (t ^ 2 + (1 - t) * t * (⟪↑y₀, S y₂⟫_ℂ + ⟪↑y₂, S y₀⟫_ℂ).re) / ‖f t‖ ^ 2
    have hg₀ : g 0 = 0 := by simp [g]
    have hg₁ : g 1 = 1 := by simp [g, f, coe_norm y₂ ▸ hy₂]
    have hg_cont : Continuous g := Continuous.div₀ (by fun_prop) (by fun_prop) (by simp [hf])
    intro c ⟨t, ht, htc⟩
    obtain ⟨r, hr, hrt⟩ := (hg₀ ▸ hg₁ ▸ intermediate_value_Icc zero_le_one hg_cont.continuousOn) ht
    rw [← htc, ← hrt]
    refine ⟨‖f r‖⁻¹ • f r, ?_, ?_⟩
    · simp only [mem_setOf_eq, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hf r))
    · have hf_sq : ofReal (‖f r‖ ^ 2) ≠ 0 := by simp [hf]
      simp_rw [← Complex.coe_smul, map_smul, SetLike.val_smul, inner_smul_left,inner_smul_right,
        ← mul_assoc, conj_ofReal, ← pow_two, ← ofReal_pow, inv_pow, ofReal_inv]
      apply (inv_mul_eq_iff_eq_mul₀ hf_sq).mpr
      simp_rw [g, ofReal_div, mul_div_cancel₀ _ hf_sq, add_comm (r ^ 2)]
      simp only [f, map_add, map_smul, coe_add, inner_add_left, inner_add_right,
        SetLike.val_smul, inner_smul_left, inner_smul_right, h₀, h₂]
      nth_rw 1 [← re_add_im ⟪↑y₀, S y₂⟫_ℂ, ← re_add_im ⟪↑y₂, S y₀⟫_ℂ]
      simp only [hy_im, mul_add, RingHom.map_sub, RingHom.map_one, conj_ofReal, mul_zero,
        zero_add, ofReal_neg, neg_mul, mul_neg, mul_one, add_re, ofReal_add, ofReal_mul,
        ofReal_sub, ofReal_one, ofReal_pow]
      ring

/-!
## D. Spectrum of a closed operator
-/

/-!
### D.1. Resolvent set
-/

/-- The resolvent set, `ρ`, of a partial linear map.

  A complex number `z` is in `ρ T` iff the linear map `T - z • 1` from `T.domain` to `H`
  is a bijection with continuous (equivalently, bounded) inverse. -/
def resolventSet (T : H →ₗ.[ℂ] H) : Set ℂ :=
  {z : ℂ | (T - z • 1).toFun.ker = ⊥ ∧ (T - z • 1).toFun.range = ⊤ ∧ Continuous (𝑅 T z)}

@[inherit_doc resolventSet]
scoped notation "ρ" => resolventSet

lemma resolventSet_eq (T : H →ₗ.[ℂ] H) :
    ρ T = {z | (T - z • 1).toFun.ker = ⊥ ∧ (T - z • 1).toFun.range = ⊤ ∧ Continuous (𝑅 T z)} :=
  rfl

lemma mem_resolventSet_iff {T : H →ₗ.[ℂ] H} {z : ℂ} :
    z ∈ ρ T ↔ (T - z • 1).toFun.ker = ⊥ ∧ (T - z • 1).toFun.range = ⊤ ∧ Continuous (𝑅 T z) :=
  Iff.rfl

/-- If an operator is not closed then its resolvent set is empty. -/
lemma resolventSet_eq_empty [CompleteSpace H] {T : H →ₗ.[ℂ] H} (h : ¬T.IsClosed) : ρ T = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun z ⟨h_ker, h_range, h_cont⟩ ↦ ?_
  suffices (T - z • 1).IsClosed by
    have hTz : T - z • 1 + z • 1 = T :=
      eq_of_le_of_domain_eq (sub_add_le_cancel _ _) (by simp [add_domain, sub_domain])
    exact h <| hTz ▸ this.add_continuous (Continuous.const_smul (by fun_prop) _) (by simp)
  apply (inverse_closed_iff h_ker).mp
  apply (isClosed_iff_isClosed_domain_of_continuous h_cont).mpr
  simp [inverse_domain, h_range]

lemma resolventSet_subset_regularityDomain (T : H →ₗ.[ℂ] H) : ρ T ⊆ T.regularityDomain :=
  fun _ ⟨h_ker, _, h_cont⟩ ↦ mem_regularityDomain_iff.mpr ⟨h_ker, h_cont⟩

/-- For a closed operator the continuity of the resolvent is redundant
  in the definition of the resolvent set. -/
lemma IsClosed.resolventSet_eq [CompleteSpace H] {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
    ρ T = {z : ℂ | (T - z • 1).toFun.ker = ⊥ ∧ (T - z • 1).toFun.range = ⊤} := by
  ext z
  rw [mem_resolventSet_iff, mem_setOf_eq, and_congr_right_iff, and_iff_left_iff_imp]
  intro h_ker h_range
  refine continuous_of_isClosed_domain ?_ ?_
  · apply (inverse_closed_iff h_ker).mpr
    exact hT.sub_continuous (Continuous.const_smul (by fun_prop) _) (by simp)
  · simp [inverse_domain, h_range]

/-- For a closed operator the resolvent set consists of those regular points for which
  the defect number is zero. -/
lemma IsClosed.resolventSet_eq' [CompleteSpace H] {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
    ρ T = T.regularityDomain ∩ T.defectNumber ⁻¹' {0} := by
  ext z
  refine ⟨fun hρ ↦ ?_, fun ⟨h_reg, h_defect⟩ ↦ ?_⟩
  · have hz : z ∈ T.regularityDomain := T.resolventSet_subset_regularityDomain hρ
    exact ⟨hz, (hT.defectNumber_eq_zero_iff hz).mpr hρ.2.1⟩
  · obtain ⟨h_ker, h_cont⟩ := mem_regularityDomain_iff.mp h_reg
    exact ⟨h_ker, (hT.defectNumber_eq_zero_iff h_reg).mp h_defect, h_cont⟩

/-- The resolvent set is an open subset of ℂ. -/
lemma resolventSet_isOpen [CompleteSpace H] (T : H →ₗ.[ℂ] H) : IsOpen (ρ T) := by
  by_cases hT : T.IsClosed
  · rw [hT.resolventSet_eq']
    apply isOpen_iff_forall_mem_open.mpr
    intro z₁ hz₁
    refine ⟨connectedComponentIn T.regularityDomain z₁, fun z₂ hz₂ ↦ ⟨?_, ?_⟩, ?_, ?_⟩
    · exact connectedComponentIn_subset _ _ hz₂
    · simp_all [hT.isClosable.defectNumber_const hz₂]
    · exact T.regularityDomain_isOpen.connectedComponentIn
    · exact mem_connectedComponentIn hz₁.1
  · simp [resolventSet_eq_empty hT]

/-!
### D.2. Spectrum
-/

/-- The spectrum, `σ`, of a partial linear map.

  `σ T` is the complement of `ρ T`. A complex number `z` is in `σ T` iff the linear map `T - z • 1`
  from `T.domain` to `H` fails to be bijective or `(T - z • 1)⁻¹` is not continuous
  (equivalently, is not bounded). -/
def spectrum (T : H →ₗ.[ℂ] H) : Set ℂ := (ρ T)ᶜ

@[inherit_doc spectrum]
scoped notation "σ" => spectrum

lemma spectrum_eq (T : H →ₗ.[ℂ] H) : σ T = (ρ T)ᶜ := rfl

lemma mem_spectrum_iff {T : H →ₗ.[ℂ] H} {z : ℂ} :
    z ∈ σ T ↔ (T - z • 1).toFun.ker ≠ ⊥ ∨ (T - z • 1).toFun.range ≠ ⊤ ∨ ¬Continuous (𝑅 T z) := by
  simp only [spectrum_eq, mem_compl_iff, mem_resolventSet_iff, not_and_or, ne_eq]

/-- If an operator is not closed then its spectrum is all of ℂ. -/
lemma spectrum_eq_univ [CompleteSpace H] {T : H →ₗ.[ℂ] H} (h : ¬T.IsClosed) : σ T = univ :=
  compl_empty ▸ compl_inj_iff.mpr (resolventSet_eq_empty h)

/-- The spectrum is a closed subset of ℂ. -/
lemma spectrum_isClosed [CompleteSpace H] (T : H →ₗ.[ℂ] H) : _root_.IsClosed (σ T) :=
  T.resolventSet_isOpen.isClosed_compl

/-!
#### D.2.1. Point spectrum
-/

/-- The point spectrum, `σᵖ`, of a partial linear map.

  A complex number `z` is in `σᵖ T` iff `T - z • 1` is not injective. -/
def pointSpectrum (T : H →ₗ.[ℂ] H) : Set ℂ := {z : ℂ | (T - z • 1).toFun.ker ≠ ⊥}

@[inherit_doc pointSpectrum]
scoped notation "σᵖ" => pointSpectrum

lemma pointSpectrum_eq (T : H →ₗ.[ℂ] H) : σᵖ T = {z | (T - z • 1).toFun.ker ≠ ⊥} := rfl

lemma mem_pointSpectrum_iff {T : H →ₗ.[ℂ] H} {z : ℂ} : z ∈ σᵖ T ↔ (T - z • 1).toFun.ker ≠ ⊥ :=
  Iff.rfl

lemma pointSpectrum_subset_spectrum (T : H →ₗ.[ℂ] H) : σᵖ T ⊆ σ T :=
  fun _ h ↦ mem_spectrum_iff.mpr (Or.inl h)

/-!
#### D.2.2. Residual spectrum
-/

/-- The residual spectrum, `σʳ`, of a partial linear map.

  A complex number `z` is in `σʳ T` iff `T - z • 1` is injective but not surjective
  and `(T - z • 1)⁻¹` is continuous (equivalently, bounded). -/
def residualSpectrum (T : H →ₗ.[ℂ] H) : Set ℂ :=
  {z : ℂ | (T - z • 1).toFun.ker = ⊥ ∧ (T - z • 1).toFun.range ≠ ⊤ ∧ Continuous (𝑅 T z)}

@[inherit_doc residualSpectrum]
scoped notation "σʳ" => residualSpectrum

lemma residualSpectrum_eq (T : H →ₗ.[ℂ] H) :
    σʳ T = {z | (T - z • 1).toFun.ker = ⊥ ∧ (T - z • 1).toFun.range ≠ ⊤ ∧ Continuous (𝑅 T z)} :=
  rfl

lemma mem_residualSpectrum_iff {T : H →ₗ.[ℂ] H} {z : ℂ} :
    z ∈ σʳ T ↔ (T - z • 1).toFun.ker = ⊥ ∧ (T - z • 1).toFun.range ≠ ⊤ ∧ Continuous (𝑅 T z) :=
  Iff.rfl

lemma residualSpectrum_subset_spectrum (T : H →ₗ.[ℂ] H) : σʳ T ⊆ σ T :=
  fun _ ⟨_, h, _⟩ ↦ mem_spectrum_iff.mpr (Or.inr <| Or.inl h)

lemma residualSpectrum_subset_regularityDomain (T : H →ₗ.[ℂ] H) : σʳ T ⊆ T.regularityDomain :=
  fun _ hz ↦ mem_regularityDomain_iff.mpr ⟨hz.1, hz.2.2⟩

/-!
#### D.2.3. Continuous spectrum
-/

/-- The continuous spectrum, `σᶜ`, of a partial linear map.

  A complex number `z` is in `σᶜ T` iff the range of `T - z • 1` is not closed. -/
def continuousSpectrum (T : H →ₗ.[ℂ] H) : Set ℂ :=
  {z : ℂ | ¬_root_.IsClosed ((T - z • 1).toFun.range : Set H)}

@[inherit_doc continuousSpectrum]
scoped notation "σᶜ" => continuousSpectrum

lemma continuousSpectrum_eq (T : H →ₗ.[ℂ] H) :
    σᶜ T = {z | ¬_root_.IsClosed ((T - z • 1).toFun.range : Set H)} := rfl

lemma mem_continuousSpectrum_iff {T : H →ₗ.[ℂ] H} {z : ℂ} :
    z ∈ σᶜ T ↔ ¬_root_.IsClosed ((T - z • 1).toFun.range : Set H) := Iff.rfl

lemma continuousSpectrum_subset_spectrum (T : H →ₗ.[ℂ] H) : σᶜ T ⊆ σ T :=
  fun _ h ⟨_, h_range, _⟩ ↦ h (by simp [h_range])

/-!
### D.3. Spectrum decomposition
-/

lemma IsClosed.spectrum_eq [CompleteSpace H] {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
    σ T = σᵖ T ∪ σʳ T ∪ σᶜ T := by
  refine Subset.antisymm ?_ ?_
  · intro z hσ
    apply mem_spectrum_iff.mp at hσ
    rcases eq_or_ne (T - z • 1).toFun.ker ⊥ with h_ker | h_ker
    · by_cases h_cont : Continuous (𝑅 T z)
      · left; right; exact ⟨h_ker, (hσ.neg_resolve_left h_ker).neg_resolve_right h_cont, h_cont⟩
      · right
        rw [mem_continuousSpectrum_iff, ← inverse_domain]
        refine fun h ↦ h_cont ?_
        refine continuous_of_isClosed_domain ?_ h
        apply (inverse_closed_iff h_ker).mpr
        exact hT.sub_continuous (Continuous.const_smul (by fun_prop) _) le_top
    · left; left; exact h_ker
  · refine union_subset ?_ T.continuousSpectrum_subset_spectrum
    exact union_subset T.pointSpectrum_subset_spectrum T.residualSpectrum_subset_spectrum

lemma pointSpectrum_inter_residualSpectrum (T : H →ₗ.[ℂ] H) : σᵖ T ∩ σʳ T = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ ⟨h, h'⟩ ↦ h h'.1

/-!
## E. Resolvent identities
-/

lemma resolvent_sub
    {T₁ T₂ : H →ₗ.[ℂ] H} (hT : T₂.domain ≤ T₁.domain) {z : ℂ} (hz₁ : z ∈ ρ T₁) (hz₂ : z ∈ ρ T₂) :
    𝑅 T₁ z - 𝑅 T₂ z = 𝑅 T₁ z * (T₂ - T₁) * 𝑅 T₂ z := by
  symm
  calc
    _ = 𝑅 T₁ z ∘ᵣ ((T₂ - z • 1 - (T₁ - z • 1)) ∘ᵣ 𝑅 T₂ z) := by
      rw [mul_assoc]
      congr 2
      exact (eq_of_le_of_domain_eq (sub_sub_sub_le_cancel_right _ _ _) (by simp [sub_domain])).symm
    _ = 𝑅 T₁ z ∘ᵣ ((T₂ - z • 1) ∘ᵣ 𝑅 T₂ z - (T₁ - z • 1) ∘ᵣ 𝑅 T₂ z) := by
      congr
      exact sub_compRestricted _ _ _
    _ = 𝑅 T₁ z ∘ᵣ (1 - (T₁ - z • 1) ∘ᵣ 𝑅 T₂ z) := by
      congr
      rw [compRestricted_inverse_eq hz₂.1, inverse_domain, hz₂.2.1]
      simp [eq_of_le_of_domain_eq domRestrict_le]
    _ = 𝑅 T₁ z - 𝑅 T₁ z ∘ᵣ ((T₁ - z • 1) ∘ᵣ 𝑅 T₂ z) := by
      nth_rw 2 [← mul_one (𝑅 T₁ z)]
      refine (eq_of_le_of_domain_eq (compRestricted_sub_ge _ _ _) ?_).symm
      simp [sub_domain, compRestricted_domain, inverse_domain, hz₁.2]
    _ = 𝑅 T₁ z - (domRestrict 1 T₁.domain) ∘ᵣ 𝑅 T₂ z := by
      simp [← compRestricted_assoc, inverse_compRestricted_eq hz₁.1, sub_domain]
    _ = 𝑅 T₁ z - 𝑅 T₂ z := by
      ext x
      · suffices 𝑅 T₂ z ⟨x, by simp [inverse_domain, hz₂.2]⟩ ∈ T₁.domain by
          simp [sub_domain, mem_compRestricted_domain_iff, inverse_domain, hz₁.2, hz₂.2, this]
        have hR₂ : (𝑅 T₂ z).toFun.range = T₂.domain := by simp [inverse_range hz₂.1, sub_domain]
        exact hT (hR₂ ▸ mem_range_self _)
      · rfl

lemma resolvent_sub' {T : H →ₗ.[ℂ] H} (z₁ z₂ : ℂ) (hz₁ : z₁ ∈ ρ T) (hz₂ : z₂ ∈ ρ T) :
    𝑅 T z₁ - 𝑅 T z₂ = (z₁ - z₂) • (𝑅 T z₁ * 𝑅 T z₂) := by
  rcases eq_or_ne z₁ z₂ with rfl | hz
  · ext
    · simp [sub_domain, inverse_domain, hz₁.2, mul_def, compRestricted_domain]
    · simp [sub_apply]
  · let S := T + (z₁ - z₂) • 1
    have h_domain : S.domain = T.domain := by simp [S, add_domain]
    have hST : S - z₁ • 1 = T - z₂ • 1 := by
      ext
      · simp [sub_domain, h_domain]
      · simp [S, sub_apply, add_apply, sub_smul, add_sub_assoc, ← sub_eq_add_neg]
    have hR : 𝑅 T z₂ = 𝑅 S z₁ := by simp [resolvent, hST]
    have hz₁' : z₁ ∈ ρ S := ⟨hST ▸ hz₂.1, hST ▸ hz₂.2.1, hR ▸ hz₂.2.2⟩
    suffices (S - T) ∘ᵣ 𝑅 S z₁ = (z₁ - z₂) • 𝑅 S z₁ by
      rw [hR, resolvent_sub h_domain.le hz₁ hz₁']
      simp only [mul_def, compRestricted_assoc, this, compRestricted_smul (sub_ne_zero.mpr hz)]
    calc
      _ = ((z₁ - z₂) • domRestrict 1 (S - z₁ • 1).domain) ∘ᵣ 𝑅 S z₁ := by
        congr
        ext
        · simp [h_domain, sub_domain]
        · simp only [sub_apply, add_apply, add_sub_cancel_left, S]
          rfl
      _ = (z₁ - z₂) • (domRestrict 1 (S - z₁ • 1).domain ∘ᵣ 𝑅 S z₁) := smul_compRestricted _ _ _
      _ = (z₁ - z₂) • 𝑅 S z₁ := by
        congr
        ext
        · simp [mem_compRestricted_domain_iff, ← inverse_range hz₁'.1]
        · rfl

end

end LinearPMap
