/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Mathematics.InnerProductSpace.Submodule
/-!

# Unbounded operators

-/

@[expose] public section

namespace LinearPMap

open Submodule
open InnerProductSpace
open InnerProductSpaceSubmodule
open Complex ComplexConjugate

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {T T₁ T₂ : H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'}

/-!
## A. Definitions
-/

/-- A LinearPMap `U` has dense domain iff `U.domain` is dense in `H`. -/
def HasDenseDomain (U : H →ₗ.[ℂ] H') : Prop := Dense (U.domain : Set H)

lemma hasDenseDomain_def : U.HasDenseDomain ↔ Dense (U.domain : Set H) := Iff.rfl

/-- A LinearPMap is an unbounded operator iff it has dense domain and is closable. -/
def IsUnbounded (U : H →ₗ.[ℂ] H') : Prop := U.HasDenseDomain ∧ U.IsClosable

lemma isUnbounded_def : U.IsUnbounded ↔ U.HasDenseDomain ∧ U.IsClosable := Iff.rfl

/-- A LinearPMap `U` is symmetric iff `⟪U x, y⟫_ℂ = ⟪x, U y⟫_ℂ` for all `x y : U.domain`. -/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop := T.IsFormalAdjoint T

lemma isSymmetric_def : T.IsSymmetric ↔ T.IsFormalAdjoint T := Iff.rfl

/-- A LinearPMap is essentially self-adjoint iff its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint [CompleteSpace H] (T : H →ₗ.[ℂ] H) : Prop := IsSelfAdjoint T.closure

lemma isEssentiallySelfAdjoint_def [CompleteSpace H] :
    T.IsEssentiallySelfAdjoint ↔ IsSelfAdjoint T.closure := Iff.rfl

/-!
## B. Dense domain
-/

lemma HasDenseDomain.isUnbounded_iff_isClosable (h : U.HasDenseDomain) :
    U.IsUnbounded ↔ U.IsClosable :=
  and_iff_right h

lemma HasDenseDomain.closure (h : U.HasDenseDomain) : U.closure.HasDenseDomain :=
  h.mono U.le_closure.1

lemma HasDenseDomain.neg (h : U.HasDenseDomain) : (-U).HasDenseDomain := h

lemma HasDenseDomain.smul (h : U.HasDenseDomain) (c : ℂ) : (c • U).HasDenseDomain := h

lemma HasDenseDomain.add_of_le (h₁ : U₁.HasDenseDomain) (h_le : U₁.domain ≤ U₂.domain) :
    (U₁ + U₂).HasDenseDomain :=
  h₁.mono (by simp [h_le, add_domain])

lemma HasDenseDomain.sub_of_le (h₁ : U₁.HasDenseDomain) (h_le : U₁.domain ≤ U₂.domain) :
    (U₁ - U₂).HasDenseDomain :=
  h₁.mono (by simp [h_le, sub_domain])

/-!
## C. Closability
-/

lemma IsClosable.isClosed_iff (h : U.IsClosable) : U.IsClosed ↔ U.closure = U := by
  constructor <;> intro h'
  · exact eq_of_eq_graph (h.graph_closure_eq_closure_graph ▸ h'.submodule_topologicalClosure_eq)
  · exact h' ▸ h.closure_isClosed

/-- A LinearPMap with densely-defined formal adjoint is closable. -/
lemma isClosable_of_exists_dense_formalAdjoint [CompleteSpace H] [CompleteSpace H']
    (h : U.HasDenseDomain) (h_fadj : ∃ U' : H' →ₗ.[ℂ] H, U'.HasDenseDomain ∧ U'.IsFormalAdjoint U) :
    U.IsClosable := by
  have h_adj : U†.HasDenseDomain := by
    obtain ⟨U', hU', hU''⟩ := h_fadj
    refine Dense.mono ?_ hU'
    rcases eq_or_lt_of_le (hU''.symm.le_adjoint h) with (rfl | h_lt)
    · rfl
    · exact (domain_mono h_lt).le
  use U††
  ext
  rw [adjoint_graph_eq_graph_adjoint h_adj, adjoint_graph_eq_graph_adjoint h,
    mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    orthogonal_orthogonal_eq_closure, mem_submodule_iff_mem_submoduleToLp, submoduleToLp_closure]

/-- A zero LinearPMap (any domain) is closable. -/
lemma isClosable_of_zero (h_zero : ⇑U = 0) : U.IsClosable := by
  use U.graph.topologicalClosure.toLinearPMap
  refine (toLinearPMap_graph_eq _ fun x hx hx₁ ↦ ?_).symm
  obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
  have hbn : ∀ n, (b n).snd = 0 := fun n ↦ by specialize hb n; simp_all
  rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at hb'
  simp_all

lemma IsClosable.smul (h : U.IsClosable) (c : ℂ) : (c • U).IsClosable := by
  rcases eq_zero_or_neZero c with (rfl | hc)
  · exact isClosable_of_zero (by simp)
  · use (c • U).graph.topologicalClosure.toLinearPMap
    refine (toLinearPMap_graph_eq _ fun x hx hx₁ ↦ ?_).symm
    rw [← smul_zero c, ← inv_smul_eq_iff₀ hc.ne]
    refine graph_fst_eq_zero_snd U.closure ?_ rfl
    rw [← h.graph_closure_eq_closure_graph]
    apply mem_closure_iff_seq_limit.mpr
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
    use fun n ↦ ((b n).fst, c⁻¹ • (b n).snd)
    rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at *
    refine ⟨fun n ↦ ?_, hx₁ ▸ hb'.1, hb'.2.const_smul c⁻¹⟩
    obtain ⟨u, hu, hu'⟩ := hb n
    simp only [coe_toAddSubmonoid, SetLike.mem_coe, mem_graph_iff, Subtype.exists, ← hu']
    exact ⟨u.1, u.1.2, rfl, ((inv_smul_eq_iff₀ hc.ne).mpr hu).symm⟩

lemma neg_eq_neg_one_smul (U : H →ₗ.[ℂ] H') : -U = (-1 : ℂ) • U := ext (by simp) (by simp)

lemma IsClosable.neg (h : U.IsClosable) : (-U).IsClosable := neg_eq_neg_one_smul U ▸ h.smul _

/-!
## D. Adjoints
-/

/-- The adjoint of a zero LinearPMap (any domain) is zero (domain `⊤`).  -/
lemma adjoint_of_zero [CompleteSpace H] (h_zero : ⇑U = 0) : U† = 0 := by
  refine dExt ?_ fun x y hxy ↦ ?_
  · ext
    simp only [zero_domain, mem_top, iff_true]
    apply (mem_adjoint_domain_iff _ _).mpr
    exact continuous_of_const (by simp [h_zero])
  · by_cases h : U.HasDenseDomain
    · exact adjoint_apply_eq h x (by simp [h_zero])
    · exact adjoint_apply_of_not_dense h x

lemma adjoint_smul [CompleteSpace H] (U : H →ₗ.[ℂ] H') {c : ℂ} (hc : c ≠ 0) :
    (c • U)† = conj c • U† := by
  refine dExt ?_ fun x y hxy ↦ ?_
  · ext x
    change Continuous (fun w ↦ ⟪x, c • U w⟫_ℂ) ↔ Continuous (fun w ↦ ⟪x, U w⟫_ℂ)
    exact Iff.trans (by simp [inner_smul_right]) (continuous_const_smul_iff₀ hc)
  · by_cases h : U.HasDenseDomain
    · refine adjoint_apply_eq (smul_domain c U ▸ h) x fun w ↦ ?_
      simp [inner_smul_left, inner_smul_right, adjoint_isFormalAdjoint h y w, hxy]
    · simp [adjoint_apply_of_not_dense h y, adjoint_apply_of_not_dense (smul_domain c U ▸ h) x]

lemma adjoint_neg [CompleteSpace H] (U : H →ₗ.[ℂ] H') : (-U)† = -U† := by
  simp [neg_eq_neg_one_smul, adjoint_smul]

lemma adjoint_antitone [CompleteSpace H]
    (h₁₂ : U₁.HasDenseDomain ∨ ¬U₂.HasDenseDomain) (h_le : U₁ ≤ U₂) : U₂† ≤ U₁† := by
  have h_agree : ∀ w : U₁.domain, U₁ w = U₂ ⟨w, h_le.1 w.2⟩ := fun w ↦ @h_le.2 w ⟨w, h_le.1 w.2⟩ rfl
  constructor
  · intro v
    let f₁ : U₁.domain → ℂ := fun w ↦ ⟪v, U₁ w⟫_ℂ
    let f₂ : U₂.domain → ℂ := fun w ↦ ⟪v, U₂ w⟫_ℂ
    change Continuous f₂ → Continuous f₁
    suffices f₁ = fun w : U₁.domain ↦ f₂ ⟨w, h_le.1 w.2⟩ by rw [this]; fun_prop
    simp [f₁, f₂, h_agree]
  · intro u v huv
    rcases h₁₂ with (h₁ | h₂)
    · have h₂ : U₂.HasDenseDomain := h₁.mono h_le.1
      refine (adjoint_apply_eq h₁ v fun w ↦ ?_).symm
      rw [adjoint_isFormalAdjoint h₂ u ⟨w, h_le.1 w.2⟩, h_agree, huv]
    · have h₁ : ¬U₁.HasDenseDomain := fun h ↦ h₂ (h.mono h_le.1)
      rw [adjoint_apply_of_not_dense h₁ v, adjoint_apply_of_not_dense h₂ u]

end LinearPMap
