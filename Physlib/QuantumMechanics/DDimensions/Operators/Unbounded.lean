/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.Mathematics.InnerProductSpace.Submodule
/-!

# Unbounded operators

## i. Overview

In this module we define unbounded operators between Hilbert spaces.

## ii. Key results

Definitions:
- `UnboundedOperator`: Densely defined, closable unbounded operator between Hilbert spaces.
- `partialOrder`: Poset structure for unbounded operators.
- `ofSymmetric`: Construction of an unbounded operator from a symmetric `LinearPMap`.
- `IsGeneralizedEigenvector`: The notion of eigenvectors/values for linear functionals.

(In)equalities:
- `le_closure`: `U ≤ U.closure`
- `adjoint_adjoint_eq_closure`: `U†† = U.closure`
- `adjoint_ge_adjoint_of_le`: `U₁ ≤ U₂ → U₂† ≤ U₁†`
- `closure_mono`: `U₁ ≤ U₂ → U₁.closure ≤ U₂.closure`
- `isSymmetric_iff_le_adjoint`: `IsSymmetric T ↔ T ≤ T†`

## iii. Table of contents

- A. Definition
- B. Basic identities
- C. Instances
  - C.1. Partial order
  - C.2. Zero
  - C.3. AddZeroClass
  - C.4. DistribSMul
- D. Closure
- E. Adjoint
- F. Symmetric operators
- G. Self-adjoint operators
- H. Generalized eigenvectors

## iv. References

- M. Reed & B. Simon, (1972). "Methods of modern mathematical physics: Vol. 1. Functional analysis".
  Academic Press. https://doi.org/10.1016/B978-0-12-585001-8.X5001-6
- K. Schmüdgen, (2012). "Unbounded self-adjoint operators on Hilbert space" (Vol. 265). Springer.
  https://doi.org/10.1007/978-94-007-4753-1

-/

@[expose] public section

namespace QuantumMechanics

open LinearPMap Submodule
open InnerProductSpace InnerProductSpaceSubmodule

/-!
## A. Definition
-/

/-- An `UnboundedOperator` is a linear map from a submodule of `H` to `H'`,
  assumed to be both densely defined and closable. -/
structure UnboundedOperator
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H' : Type*) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    extends LinearPMap ℂ H H' where
  /-- The domain of an unbounded operator is dense in `H`. -/
  dense_domain : Dense (domain : Set H)
  /-- An unbounded operator is closable. -/
  is_closable : toLinearPMap.IsClosable

namespace UnboundedOperator

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

@[ext]
lemma ext {U₁ U₂ : UnboundedOperator H H'} (h : U₁.toLinearPMap = U₂.toLinearPMap) :
    U₁ = U₂ := by
  cases U₁
  simp_all

instance : CoeFun (UnboundedOperator H H') (fun U ↦ U.domain → H') :=
  ⟨fun U ↦ U.toLinearPMap.toFun'⟩

/-!
## B. Basic identities
-/

section
open Complex

lemma inner_map_polarization {T : UnboundedOperator H H} (x y : T.domain) :
    ⟪T x, ↑y⟫_ℂ = (⟪T (x + y), ↑(x + y)⟫_ℂ - ⟪T (x - y), ↑(x - y)⟫_ℂ
    - I * ⟪T (x + I • y), ↑(x + I • y)⟫_ℂ + I * ⟪T (x - I • y), ↑(x - I • y)⟫_ℂ) / 4 := by
  simp only [LinearPMap.map_add, coe_add, inner_add_right, inner_add_left, LinearPMap.map_sub,
    AddSubgroupClass.coe_sub, inner_sub_right, inner_sub_left, LinearPMap.map_smul,
    SetLike.val_smul, inner_smul_left, conj_I, inner_smul_right]
  grind [I_sq]

lemma inner_map_polarization' {T : UnboundedOperator H H} (x y : T.domain) :
    ⟪↑x, T y⟫_ℂ = (⟪↑(x + y), T (x + y)⟫_ℂ - ⟪↑(x - y), T (x - y)⟫_ℂ
    - I * ⟪↑(x + I • y), T (x + I • y)⟫_ℂ + I * ⟪↑(x - I • y), T (x - I • y)⟫_ℂ) / 4 := by
  simp only [coe_add, LinearPMap.map_add, inner_add_right, inner_add_left, AddSubgroupClass.coe_sub,
    LinearPMap.map_sub, inner_sub_right, inner_sub_left, SetLike.val_smul, LinearPMap.map_smul,
    inner_smul_left, conj_I, inner_smul_right]
  grind [I_sq]

end

/-!
## C. Instances
-/

section

open Classical

/-!
### C.1. Partial order

Unbounded operators inherit the structure of a poset from `LinearPMap`,
but *not* that of a `SemilatticeInf` because `U₁.domain ⊓ U₂.domain` may not be dense.
-/

instance : PartialOrder (UnboundedOperator H H') where
  le U₁ U₂ := U₁.toLinearPMap ≤ U₂.toLinearPMap
  le_refl _ := le_refl _
  le_trans _ _ _ h₁₂ h₂₃ := le_trans h₁₂ h₂₃
  le_antisymm _ _ h h' := ext <| le_antisymm h h'

/-!
### C.2. Zero
-/

-- A zero LinearPMap (any domain) is closable
lemma isClosable_of_zero {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {f : LinearPMap ℂ E F} (hf : f.toFun' = 0) :
    f.IsClosable := by
  use f.graph.topologicalClosure.toLinearPMap
  refine Eq.symm <| toLinearPMap_graph_eq f.graph.topologicalClosure fun x hx _ ↦ ?_
  obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp hx
  have (n : ℕ) : (b n).2 = 0 := by specialize hb n; simp_all
  rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at hb'
  simp_all

instance : Zero (UnboundedOperator H H') := ⟨0, by simp, isClosable_of_zero rfl⟩

@[simp]
lemma zero_toLinearPMap : (0 : UnboundedOperator H H').toLinearPMap = 0 := rfl

instance : Inhabited (UnboundedOperator H H') := ⟨instZero.zero⟩

/-!
### C.3. AddZeroClass

In defining addition for unbounded operators we use two junk values.
- If `U₁.domain ∩ U₂.domain` is not dense, then `U₁ + U₂ = 0` (domain `⊤`)
- If `U₁.domain ∩ U₂.domain` is dense but `U₁.toLinearPMap + U₂.toLinearPMap` is not closable,
  then `U₁ + U₂ = 0` with domain `U₁.domain ∩ U₂.domain`.
This ensures that distributivity, `c • (U₁ + U₂) = c • U₁ + c • U₂`, holds for `(c : ℂ) = 0`.
-/

noncomputable instance : Add (UnboundedOperator H H') where
  add U₁ U₂ :=
    if hD : Dense (U₁.domain ⊓ U₂.domain : Set H) then
      if hC : (U₁.toLinearPMap + U₂.toLinearPMap).IsClosable then
        ⟨U₁.toLinearPMap + U₂.toLinearPMap, hD, hC⟩
      else ⟨⟨U₁.domain ⊓ U₂.domain, 0⟩, hD, isClosable_of_zero rfl⟩
    else 0

/-- The domain of `U₁ + U₂` is `D(U₁) ∩ D(U₂)` when it is dense. -/
lemma add_domain_of_dense {U₁ U₂ : UnboundedOperator H H'}
    (hD : Dense (U₁.domain ⊓ U₂.domain : Set H)) : (U₁ + U₂).domain = U₁.domain ⊓ U₂.domain := by
  rw [HAdd.hAdd, instHAdd, Add.add, instAdd]
  by_cases hC : (U₁.toLinearPMap + U₂.toLinearPMap).IsClosable
  · simp only [hD, hC, ↓reduceDIte, LinearPMap.add_domain]
  · simp only [hD, hC, ↓reduceDIte]

/-- The junk value for `U₁ + U₂` has domain all of `H` when `D(U₁) ∩ D(U₂)` is not dense. -/
lemma add_domain_of_not_dense {U₁ U₂ : UnboundedOperator H H'}
    (hD : ¬Dense (U₁.domain ⊓ U₂.domain : Set H)) : (U₁ + U₂).domain = ⊤ := by
  rw [HAdd.hAdd, instHAdd, Add.add, instAdd]
  simp only [hD, ↓reduceDIte, zero_toLinearPMap, zero_domain]

lemma mem_domain_of_dense {U₁ U₂ : UnboundedOperator H H'}
    (hD : Dense (U₁.domain ⊓ U₂.domain : Set H)) (ψ : (U₁ + U₂).domain) :
    ↑ψ ∈ U₁.domain ∧ ↑ψ ∈ U₂.domain :=
  mem_inf.mp <| (add_domain_of_dense hD) ▸ ψ.2

/-- `U₁ + U₂` is the unbounded operator corresponding to `U₁.toLinearPMap + U₂.toLinearPMap`,
  provided it is both densely defined and closable. -/
lemma add_toLinearPMap_of_dense_closable {U₁ U₂ : UnboundedOperator H H'}
    (hD : Dense (U₁.domain ⊓ U₂.domain : Set H))
    (hC : (U₁.toLinearPMap + U₂.toLinearPMap).IsClosable) :
    (U₁ + U₂).toLinearPMap = U₁.toLinearPMap + U₂.toLinearPMap := by
  rw [HAdd.hAdd, instHAdd, Add.add, instAdd]
  simp only [hD, hC, ↓reduceDIte]

/-- The junk value for `U₁ + U₂` when `D(U₁) ∩ D(U₂)` is dense and `U₁ + U₂` is not closable. -/
lemma add_toLinearPMap_of_dense_not_closable {U₁ U₂ : UnboundedOperator H H'}
    (hD : Dense (U₁.domain ⊓ U₂.domain : Set H))
    (hC : ¬(U₁.toLinearPMap + U₂.toLinearPMap).IsClosable) :
    (U₁ + U₂).toLinearPMap = ⟨U₁.domain ⊓ U₂.domain, 0⟩ := by
  rw [HAdd.hAdd, instHAdd, Add.add, instAdd]
  simp only [hD, hC, ↓reduceDIte]

/-- The junk value for `U₁ + U₂` when `D(U₁) ∩ D(U₂)` is not dense. -/
lemma add_toLinearPMap_of_not_dense {U₁ U₂ : UnboundedOperator H H'}
    (hD : ¬Dense (U₁.domain ⊓ U₂.domain : Set H)) : (U₁ + U₂).toLinearPMap = 0 := by
  rw [HAdd.hAdd, instHAdd, Add.add, instAdd]
  simp only [hD, ↓reduceDIte, zero_toLinearPMap]

/-- `(U₁ + U₂)ψ = U₁ψ + U₂ψ` provided `U₁ + U₂` is not given by a junk value. -/
lemma add_apply_of_dense_closable {U₁ U₂ : UnboundedOperator H H'}
    (hD : Dense (U₁.domain ⊓ U₂.domain : Set H))
    (hC : (U₁.toLinearPMap + U₂.toLinearPMap).IsClosable) (ψ : (U₁ + U₂).domain) :
    (U₁ + U₂) ψ = U₁ ⟨ψ, (mem_domain_of_dense hD ψ).1⟩ + U₂ ⟨ψ, (mem_domain_of_dense hD ψ).2⟩ := by
  obtain ⟨_, hb⟩ := LinearPMap.dExt_iff.mp <| add_toLinearPMap_of_dense_closable hD hC
  simp only [Subtype.forall] at hb
  specialize hb ψ ψ.2 ψ (mem_domain_of_dense hD ψ) rfl
  simp_all [LinearPMap.add_apply]

noncomputable instance : AddZeroClass (UnboundedOperator H H') where
  zero_add U := by
    apply UnboundedOperator.ext
    rw [← zero_add U.toLinearPMap]
    exact add_toLinearPMap_of_dense_closable (by simp [U.dense_domain]) (by simp [U.is_closable])
  add_zero U := by
    apply UnboundedOperator.ext
    rw [← add_zero U.toLinearPMap]
    exact add_toLinearPMap_of_dense_closable (by simp [U.dense_domain]) (by simp [U.is_closable])

/-- Addition of unbounded operators is associative when neither of the intermediate additions,
  `U₁ + U₂` and `U₂ + U₃`, is given by a junk value. -/
lemma add_assoc {U₁ U₂ U₃ : UnboundedOperator H H'}
    (hD₁₂ : Dense (U₁.domain ⊓ U₂.domain : Set H)) (hC₁₂ : (U₁.1 + U₂.1).IsClosable)
    (hD₂₃ : Dense (U₂.domain ⊓ U₃.domain : Set H)) (hC₂₃ : (U₂.1 + U₃.1).IsClosable) :
    U₁ + U₂ + U₃ = U₁ + (U₂ + U₃) := by
  apply UnboundedOperator.ext
  by_cases hD : Dense (U₁.domain ⊓ U₂.domain ⊓ U₃.domain : Set H)
  · have hD' : Dense (U₁.domain ⊓ (U₂.domain ⊓ U₃.domain) : Set H) := by grind
    have hD₁₂' : (U₁ + U₂).domain = U₁.domain ⊓ U₂.domain := add_domain_of_dense hD₁₂
    have hD₂₃' : (U₂ + U₃).domain = U₂.domain ⊓ U₃.domain := add_domain_of_dense hD₂₃
    have h₁₂ : (U₁ + U₂).1 = U₁.1 + U₂.1 := add_toLinearPMap_of_dense_closable hD₁₂ hC₁₂
    have h₂₃ : (U₂ + U₃).1 = U₂.1 + U₃.1 := add_toLinearPMap_of_dense_closable hD₂₃ hC₂₃
    by_cases hC : (U₁.1 + U₂.1 + U₃.1).IsClosable
    · -- No junk values anywhere: addition is associative
      have hC' : (U₁.1 + (U₂.1 + U₃.1)).IsClosable := by grind
      rw [add_toLinearPMap_of_dense_closable (by simp_all) (h₁₂ ▸ hC), h₁₂,
        add_toLinearPMap_of_dense_closable (by simp_all) (h₂₃ ▸ hC'), h₂₃]
      grind
    · -- D(U₁) ∩ D(U₂) ∩ D(U₃) is dense but neither side is closable:
      -- both sides are the junk zero operator with domain D(U₁) ∩ D(U₂) ∩ D(U₃)
      have hC' : ¬(U₁.1 + (U₂.1 + U₃.1)).IsClosable := by grind
      rw [add_toLinearPMap_of_dense_not_closable (by simp_all) (h₁₂ ▸ hC), hD₁₂',
        add_toLinearPMap_of_dense_not_closable (by simp_all) (h₂₃ ▸ hC'), hD₂₃']
      grind
  · -- D(U₁) ∩ D(U₂) ∩ D(U₃) is not dense: both sides are the junk zero operator with domain ⊤
    have hD' : ¬Dense (U₁.domain ⊓ (U₂.domain ⊓ U₃.domain) : Set H) := by grind
    have hD₁₂' : ¬Dense ((U₁ + U₂).domain ⊓ U₃.domain : Set H) := add_domain_of_dense hD₁₂ ▸ hD
    have hD₂₃' : ¬Dense (U₁.domain ⊓ (U₂ + U₃).domain : Set H) := add_domain_of_dense hD₂₃ ▸ hD'
    rw [add_toLinearPMap_of_not_dense hD₁₂', add_toLinearPMap_of_not_dense hD₂₃']

/-!
### C.4. DistribSMul

Scalar multiplication by complex numbers is inherited from `LinearPMap`. Note that `(c : ℂ) • U` has
the same domain as `U` for all constants; in particular, `(0 : ℂ) • U ≤ 0` with equality if and only
if `U.domain = ⊤`.
-/

lemma smul_mem_graph_of_mem_smul_graph {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {f : LinearPMap ℂ E F} {c : ℂ} (hc : c ≠ 0)
    {x : E × F} (h : x ∈ (c • f).graph.topologicalClosure) :
    (x.fst, c⁻¹ • x.snd) ∈ f.graph.topologicalClosure := by
  obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp h
  apply mem_closure_iff_seq_limit.mpr
  use fun n ↦ ((b n).fst, c⁻¹ • (b n).snd)
  rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at *
  refine ⟨?_, ⟨hb'.1, ?_⟩⟩
  · have {y : f.domain} {z : F} : c • f y = z ↔ f y = c⁻¹ • z := by aesop
    simp_all
  · rw [nhds_smul₀ (inv_ne_zero hc), ← Pi.smul_def, Filter.smul_tendsto_smul_iff₀ (inv_ne_zero hc)]
    exact hb'.2

lemma smul_isClosable_of_isClosable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {f : LinearPMap ℂ E F} (hf : f.IsClosable)
    (c : ℂ) : (c • f).IsClosable := by
  rcases eq_zero_or_neZero c with (rfl | hc)
  · exact isClosable_of_zero (by simp)
  · use (c • f).graph.topologicalClosure.toLinearPMap
    refine Eq.symm <| toLinearPMap_graph_eq _ (fun x hx hx1 ↦ ?_)
    suffices c⁻¹ • x.snd = 0 by aesop
    have hx := smul_mem_graph_of_mem_smul_graph hc.ne hx
    rw [IsClosable.graph_closure_eq_closure_graph hf, hx1] at hx
    exact graph_fst_eq_zero_snd f.closure hx rfl

noncomputable instance : SMul ℂ (UnboundedOperator H H') where
  smul c U := ⟨c • U.toLinearPMap, U.dense_domain, smul_isClosable_of_isClosable U.is_closable c⟩

variable (U : UnboundedOperator H H')

@[simp]
lemma smul_domain (c : ℂ) : (c • U).domain = U.domain := rfl

@[simp]
lemma smul_toLinearPMap (c : ℂ) : (c • U).toLinearPMap = c • U.toLinearPMap := rfl

lemma zero_smul_le_zero : (0 : ℂ) • U ≤ 0 := ⟨by simp, by simp⟩

noncomputable instance : DistribSMul ℂ (UnboundedOperator H H') where
  smul_zero _ := ext <| by ext <;> simp
  smul_add c U₁ U₂ := by
    apply UnboundedOperator.ext
    by_cases hD : Dense (U₁.domain ⊓ U₂.domain : Set H)
    · have hD' : Dense ((c • U₁).domain ⊓ (c • U₂).domain : Set H) := by grind
      by_cases hC : (U₁.1 + U₂.1).IsClosable
      · -- No junk values: smul distributes as it does for `LinearPMap`
        have h : c • (U₁.1 + U₂.1) = c • U₁.1 + c • U₂.1 := by
          ext
          · simp [LinearPMap.add_domain]
          · simp [LinearPMap.add_apply]
        have hC' : ((c • U₁).1 + (c • U₂).1).IsClosable := by
          simp [← h, smul_isClosable_of_isClosable hC]
        simp only [h, smul_toLinearPMap, add_toLinearPMap_of_dense_closable hD hC,
          add_toLinearPMap_of_dense_closable hD' hC']
      · -- `D(U₁) ∩ D(U₂)` is dense and `U₁ + U₂` is not closable:
        -- both sides are the zero operator on `D(U₁) ∩ D(U₂)`.
        -- `c = 0` must be treated separately because in this case the RHS side *is* closable.
        rw [smul_toLinearPMap, add_toLinearPMap_of_dense_not_closable hD hC]
        rcases eq_zero_or_neZero c with (rfl | hc)
        · have hC' : (((0 : ℂ) • U₁).1 + ((0 : ℂ) • U₂).1).IsClosable :=
            isClosable_of_zero (by ext; simp [LinearPMap.add_apply])
          rw [add_toLinearPMap_of_dense_closable hD' hC']
          ext
          · simp [LinearPMap.add_domain]
          · simp [LinearPMap.add_apply]
        · have h : U₁.1 + U₂.1 = c⁻¹ • (c • U₁.1 + c • U₂.1) := by
            ext
            · simp [LinearPMap.add_domain]
            · simp [LinearPMap.add_apply, smul_smul, inv_mul_cancel₀ hc.ne]
          have hC' := fun h' ↦ hC (h ▸ smul_isClosable_of_isClosable h' c⁻¹)
          rw [add_toLinearPMap_of_dense_not_closable hD' hC']
          ext <;> simp
    · -- `D(U₁) ∩ D(U₂)` is not dense: both sides are the junk zero operator with domain `⊤`
      have hD' : ¬Dense ((c • U₁).domain ⊓ (c • U₂).domain : Set H) := by grind
      rw [smul_toLinearPMap, add_toLinearPMap_of_not_dense hD, add_toLinearPMap_of_not_dense hD']
      ext <;> simp

end

/-!
## D. Closure
-/

section

variable (U : UnboundedOperator H H')

/-- The closure of an unbounded operator. -/
noncomputable def closure : UnboundedOperator H H' where
  toLinearPMap := U.toLinearPMap.closure
  dense_domain := Dense.mono (HasCore.le_domain (closureHasCore U.toLinearPMap)) U.dense_domain
  is_closable := IsClosed.isClosable (IsClosable.closure_isClosed U.is_closable)

@[simp]
lemma closure_toLinearPMap : U.closure.toLinearPMap = U.toLinearPMap.closure := rfl

lemma le_closure : U ≤ U.closure := LinearPMap.le_closure U.toLinearPMap

/-- An unbounded operator is closed iff the graph of its defining LinearPMap is closed. -/
def IsClosed : Prop := U.toLinearPMap.IsClosed

lemma closure_isClosed : U.closure.IsClosed := IsClosable.closure_isClosed U.is_closable

lemma isClosed_def : IsClosed U ↔ U.closure = U := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ closure_isClosed U⟩
  rw [UnboundedOperator.ext_iff, closure_toLinearPMap]
  apply eq_of_eq_graph
  rw [← IsClosable.graph_closure_eq_closure_graph U.is_closable]
  exact IsClosed.submodule_topologicalClosure_eq h

end

/-!
## E. Adjoint
-/

section

variable (U : UnboundedOperator H H')

/-- The adjoint of a densely defined, closable `LinearPMap` is densely defined. -/
lemma adjoint_dense_of_isClosable {f : LinearPMap ℂ H H'} (h_dense : Dense (f.domain : Set H))
    (h_closable : f.IsClosable) : Dense (f†.domain : Set H') := by
  by_contra hd
  have : ∃ x ∈ f†.domainᗮ, x ≠ 0 := by
    apply not_forall.mp at hd
    rcases hd with ⟨y, hy⟩
    have hnetop : f†.domainᗮᗮ ≠ ⊤ := by
      rw [orthogonal_orthogonal_eq_closure]
      exact Ne.symm (ne_of_mem_of_not_mem' trivial hy)
    have hnebot : f†.domainᗮ ≠ ⊥ := by
      by_contra
      apply hnetop
      rwa [orthogonal_eq_top_iff]
    exact exists_mem_ne_zero_of_ne_bot hnebot
  rcases this with ⟨x, hx, hx'⟩
  apply hx'
  apply graph_fst_eq_zero_snd f.closure _ rfl
  rw [← IsClosable.graph_closure_eq_closure_graph h_closable,
    mem_submodule_closure_iff_mem_submoduleToLp_closure,
    ← orthogonal_orthogonal_eq_closure,
    ← mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    ← LinearPMap.adjoint_graph_eq_graph_adjoint h_dense,
    mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]
  rintro ⟨y, Uy⟩ hy
  simp only [neg_zero, WithLp.prod_inner_apply, inner_zero_right, add_zero]
  exact hx y (mem_domain_of_mem_graph hy)

/-- The adjoint of an unbounded operator, denoted as `U†`. -/
noncomputable def adjoint : UnboundedOperator H' H where
  toLinearPMap := U.toLinearPMap.adjoint
  dense_domain := adjoint_dense_of_isClosable U.dense_domain U.is_closable
  is_closable := IsClosed.isClosable (adjoint_isClosed U.dense_domain)

@[inherit_doc]
scoped postfix:1024 "†" => UnboundedOperator.adjoint

@[simp]
lemma adjoint_toLinearPMap : U†.toLinearPMap = U.toLinearPMap† := rfl

lemma adjoint_isClosed : U†.IsClosed := LinearPMap.adjoint_isClosed U.dense_domain

lemma adjoint_closure_eq_adjoint : U†.closure = U† := (isClosed_def U†).mp <| adjoint_isClosed U

lemma closure_adjoint_eq_adjoint : U.closure† = U† := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.closure.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]
  ext
  rw [mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal,
    orthogonal_closure, mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal]

lemma adjoint_adjoint_eq_closure : U†† = U.closure := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U†.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]
  ext
  rw [mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal,
    orthogonal_orthogonal_eq_closure, mem_submodule_closure_iff_mem_submoduleToLp_closure]

lemma le_adjoint_adjoint : U ≤ U†† := adjoint_adjoint_eq_closure U ▸ le_closure U

lemma isClosed_iff : IsClosed U ↔ U†† = U := adjoint_adjoint_eq_closure U ▸ isClosed_def U

lemma adjoint_ge_adjoint_of_le {U₁ U₂ : UnboundedOperator H H'} (h : U₁ ≤ U₂) : U₂† ≤ U₁† := by
  obtain ⟨h_domain, h_agree⟩ := h
  simp only [Subtype.forall] at h_agree
  have heq (x : U₁.domain) (v : U₂†.domain) : ⟪U₂† v, x⟫_ℂ = ⟪(v : H'), U₁ x⟫_ℂ := by
    have hx₂ : ↑x ∈ U₂.domain := h_domain <| coe_mem x
    have h : U₁ x = U₂ ⟨x, hx₂⟩ := h_agree x x.2 x hx₂ rfl
    exact h ▸ adjoint_isFormalAdjoint U₂.dense_domain v ⟨x, hx₂⟩
  constructor
  · intro v hv
    apply mem_adjoint_domain_of_exists v
    use U₂† ⟨v, hv⟩
    exact fun x ↦ heq x ⟨v, hv⟩
  · exact fun u v huv ↦ (adjoint_apply_eq U₁.dense_domain v <| fun x ↦ huv ▸ heq x u).symm

lemma closure_mono {U₁ U₂ : UnboundedOperator H H'} (h : U₁ ≤ U₂) : U₁.closure ≤ U₂.closure := by
  repeat rw [← adjoint_adjoint_eq_closure]
  exact adjoint_ge_adjoint_of_le <| adjoint_ge_adjoint_of_le h

end

/-!
## F. Symmetric operators
-/

section

variable
  {E : Submodule ℂ H} (hE : Dense (E : Set H))
  {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric)
  (T : UnboundedOperator H H)

/-- An `UnboundedOperator` constructed from a symmetric linear map on a dense submodule `E`. -/
def ofSymmetric : UnboundedOperator H H where
  toLinearPMap := LinearPMap.mk E (E.subtype ∘ₗ f)
  dense_domain := hE
  is_closable := by
    refine isClosable_iff_exists_closed_extension.mpr ?_
    use (LinearPMap.mk E (E.subtype ∘ₗ f))†
    exact ⟨LinearPMap.adjoint_isClosed hE, IsFormalAdjoint.le_adjoint hE hf⟩

@[simp]
lemma ofSymmetric_apply (ψ : E) : (ofSymmetric hE hf) ψ = E.subtype (f ψ) := rfl

-- Note that cannot simply co-opt `LinearMap.IsSymmetric` because
-- the domain and codomain of `T` need not be the same.
/-- `T` is symmetric if `⟪T x, y⟫ = ⟪x, T y⟫` for all `x,y ∈ T.domain`. -/
def IsSymmetric : Prop := ∀ x y : T.domain, ⟪T x, y⟫_ℂ = ⟪(x : H), T y⟫_ℂ

lemma isSymmetric_iff_inner_map_self_real :
    IsSymmetric T ↔ ∀ x : T.domain, (starRingEnd ℂ) ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  simp only [inner_conj_symm]
  refine ⟨fun hT x ↦ (hT x x).symm, fun h x y ↦ ?_⟩
  rw [inner_map_polarization, inner_map_polarization']
  rw [h (x + y), h (x - y), h (x + Complex.I • y), h (x - Complex.I • y)]

lemma isSymmetric_iff_le_adjoint : IsSymmetric T ↔ T ≤ T† := by
  refine ⟨fun hT ↦ IsFormalAdjoint.le_adjoint T.dense_domain <| IsFormalAdjoint.symm hT, ?_⟩
  intro h x y
  obtain ⟨h_domain, h_agree⟩ := h
  simp only [Subtype.forall] at h_agree
  have hy : ↑y ∈ T†.domain := h_domain <| coe_mem y
  have heq := (IsFormalAdjoint.symm <| adjoint_isFormalAdjoint T.dense_domain) x ⟨y, hy⟩
  exact (h_agree y y.2 y hy rfl) ▸ heq

end

/-!
## G. Self-adjoint operators
-/

section

variable (T : UnboundedOperator H H)

noncomputable instance instStar : Star (UnboundedOperator H H) := ⟨adjoint⟩

lemma isSelfAdjoint_def : IsSelfAdjoint T ↔ T† = T := Iff.rfl

lemma isSelfAdjoint_iff : IsSelfAdjoint T ↔ IsSelfAdjoint T.toLinearPMap := by
  rw [isSelfAdjoint_def, LinearPMap.isSelfAdjoint_def, ← adjoint_toLinearPMap,
    UnboundedOperator.ext_iff]

lemma isClosed_of_isSelfAdjoint {T : UnboundedOperator H H} (hT : IsSelfAdjoint T) : IsClosed T :=
  hT ▸ adjoint_isClosed T

lemma isSymmetric_of_isSelfAdjoint {T : UnboundedOperator H H} (hT : IsSelfAdjoint T) :
    IsSymmetric T := by
  rw [isSymmetric_iff_le_adjoint]
  exact ge_of_eq hT

/-- `T` is essentially self-adjoint if its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint : Prop := IsSelfAdjoint T.closure

lemma isEssentiallySelfAdjoint_def : IsEssentiallySelfAdjoint T ↔ T† = T.closure := by
  rw [IsEssentiallySelfAdjoint, isSelfAdjoint_def, closure_adjoint_eq_adjoint]

lemma isSelfAdjoint_isEssentiallySelfAdjoint {T : UnboundedOperator H H} (hT : IsSelfAdjoint T) :
    IsEssentiallySelfAdjoint T := by
  rw [isEssentiallySelfAdjoint_def]
  nth_rw 2 [← hT]
  exact Eq.symm <| adjoint_closure_eq_adjoint T

end

/-!
## H. Generalized eigenvectors
-/

section

variable
  {E : Submodule ℂ H} (hE : Dense (E : Set H))
  {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric)
  (T : UnboundedOperator H H)

/-- A map `F : D(T) →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `T`
  if there is an eigenvalue `c` such that for all `ψ ∈ D(T)`, `F (T ψ) = c ⬝ F ψ`. -/
def IsGeneralizedEigenvector (F : T.domain →L[ℂ] ℂ) (c : ℂ) : Prop :=
  ∀ ψ : T.domain, ∃ ψ' : T.domain, ψ' = T ψ ∧ F ψ' = c • F ψ

lemma isGeneralizedEigenvector_ofSymmetric_iff (F : E →L[ℂ] ℂ) (c : ℂ) :
    IsGeneralizedEigenvector (ofSymmetric hE hf) F c ↔ ∀ ψ : E, F (f ψ) = c • F ψ := by
  constructor <;> intro h ψ
  · obtain ⟨ψ', hψ', hψ''⟩ := h ψ
    exact (SetLike.coe_eq_coe.mp hψ') ▸ hψ''
  · use f ψ
    exact ⟨by simp, h ψ⟩

end

end UnboundedOperator
end QuantumMechanics
