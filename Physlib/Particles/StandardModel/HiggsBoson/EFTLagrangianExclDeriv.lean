/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Dual.Basis
public import Physlib.Mathematics.ConjModule
public import Physlib.Mathematics.SymmetricAlgebra.OfSymmetric
public import Physlib.Particles.StandardModel.HiggsBoson.Basic

/-!
# The non-derivative Higgs EFT Lagrangian space

## i. Overview

A Higgs effective Lagrangian, with derivative terms excluded, is a sum of products of the
components of the Higgs doublet and of its conjugate. Selecting a component is applying a linear
functional, so each factor in such a product is drawn from `Module.Dual ℂ HiggsVec` or from
`Module.Dual ℂ (ConjModule HiggsVec)`. Since the Higgs is a boson these factors commute among
themselves, which makes the free commutative algebra on that pair of duals the natural home for
the whole Lagrangian. That algebra,

`SymmetricAlgebra ℂ (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec))`,

is defined here as `EFTLagrangianExclDeriv`.

Each product of generators is recorded by its field content, the multiset of component labels it
uses. The main construction of the file is `coeff s`, the linear map keeping only the part of a
Lagrangian with field content `s`. We show it is idempotent, so it is a projection, and that
everything it produces is a multiple of a single monomial, so it projects onto a line.
-/

@[expose] public section

namespace StandardModel.HiggsField

noncomputable section

open Module

/-!

## A. The Higgs EFT Lagrangian space

-/

/-! ### A.1. The carrier -/

/-- The type corresponding to a non-derivative term of the Higgs effective Lagrangian: the
symmetric algebra on the Higgs covectors and conjugate-Higgs covectors. -/
abbrev EFTLagrangianExclDeriv : Type :=
  SymmetricAlgebra ℂ (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec))

/-! ### A.2. The field specification -/

/-- The specification of the field components appearing in a non-derivative Higgs term: the two
components `φ α` of the Higgs doublet and the two components `barφ α` of its conjugate. -/
inductive FieldSpecification
  | φ (α : Fin 2)
  | barφ (α : Fin 2)
deriving DecidableEq, Fintype, Repr

namespace FieldSpecification

/-- The equivalence between `FieldSpecification` and `Fin 2 ⊕ Fin 2` sending `φ α` to the left
and `barφ α` to the right component. -/
def toSumFin : FieldSpecification ≃ Fin 2 ⊕ Fin 2 where
  toFun
    | .φ α => Sum.inl α
    | .barφ α => Sum.inr α
  invFun
    | Sum.inl α => .φ α
    | Sum.inr α => .barφ α
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-! ### A.3. The generator basis -/

/-- The basis of the module underlying `EFTLagrangianExclDeriv`, indexed by `FieldSpecification`:
`φ α` corresponds to the dual basis of the Higgs doublet and `barφ α` to the dual basis of its
conjugate. -/
def moduleBasis : Basis FieldSpecification ℂ
    (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec)) :=
  (HiggsVec.orthonormBasis.toBasis.dualBasis.prod
    (Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis).reindex toSumFin.symm

@[simp]
lemma moduleBasis_apply_φ (α : Fin 2) :
    moduleBasis (.φ α) = (HiggsVec.orthonormBasis.toBasis.dualBasis α, 0) := by
  simp [moduleBasis, toSumFin]

@[simp]
lemma moduleBasis_apply_barφ (α : Fin 2) :
    moduleBasis (.barφ α) =
      (0, (Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis α) := by
  simp [moduleBasis, toSumFin]

/-! ### A.4. Algebra generators -/

/-- The image of a field specification in `EFTLagrangianExclDeriv`, as the symmetric-algebra
generator of the corresponding basis vector. Denoted `[f]ₛ`. -/
def toEFTLagrangianExclDeriv (f : FieldSpecification) : EFTLagrangianExclDeriv :=
  SymmetricAlgebra.ι ℂ
    (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec)) (moduleBasis f)

@[inherit_doc toEFTLagrangianExclDeriv]
scoped notation "[" f "]ₛ" => toEFTLagrangianExclDeriv f

lemma toEFTLagrangianExclDeriv_φ (α : Fin 2) :
    [φ α]ₛ = SymmetricAlgebra.ι ℂ
      (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec))
      (HiggsVec.orthonormBasis.toBasis.dualBasis α, 0) := by
  rw [toEFTLagrangianExclDeriv, moduleBasis_apply_φ]

lemma toEFTLagrangianExclDeriv_barφ (α : Fin 2) :
    [barφ α]ₛ = SymmetricAlgebra.ι ℂ
      (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec))
      (0, (Basis.conj HiggsVec.orthonormBasis.toBasis).dualBasis α) := by
  rw [toEFTLagrangianExclDeriv, moduleBasis_apply_barφ]

end FieldSpecification

namespace EFTLagrangianExclDeriv

open FieldSpecification

/-!

## B. Higgs monomials

-/

/-! ### B.1. Monomials from a list -/

/-- The term in the Higgs effective Lagrangian given by the product of the field labels in `l`. -/
def termOfList (l : List FieldSpecification) : EFTLagrangianExclDeriv :=
  (l.map toEFTLagrangianExclDeriv).prod

@[simp]
lemma termOfList_nil : termOfList [] = 1 := by
  simp [termOfList]

lemma termOfList_cons (f : FieldSpecification) (l : List FieldSpecification) :
    termOfList (f :: l) = [f]ₛ * termOfList l := by
  simp [termOfList]

lemma termOfList_singleton (f : FieldSpecification) : termOfList [f] = [f]ₛ := by
  simp [termOfList_cons]

lemma termOfList_append (l₁ l₂ : List FieldSpecification) :
    termOfList (l₁ ++ l₂) = termOfList l₁ * termOfList l₂ := by
  simp [termOfList]

/-! ### B.2. Permutation invariance -/

/-- Permuting bosonic field labels leaves their monomial unchanged. -/
lemma termOfList_eq_of_perm {l₁ l₂ : List FieldSpecification} (h : l₁.Perm l₂) :
    termOfList l₁ = termOfList l₂ :=
  (h.map toEFTLagrangianExclDeriv).prod_eq

lemma termOfList_eq_ιMulti (l : List FieldSpecification) :
    termOfList l = SymmetricAlgebra.ιMulti ℂ
      (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec)) l.length
      (fun i => moduleBasis (l.get i)) := by
  induction l with
  | nil => simp
  | cons f l h =>
      simp [termOfList_cons, h]
      rfl

lemma termOfList_ofFn {n : ℕ} (g : Fin n → FieldSpecification) :
    termOfList (List.ofFn g) = SymmetricAlgebra.ιMulti ℂ
      (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec)) n
      (fun i => moduleBasis (g i)) := by
  rw [SymmetricAlgebra.ιMulti_apply, termOfList, List.map_ofFn, List.prod_ofFn]
  rfl

/-! ### B.3. Monomials from a tuple -/

/-- The term in the Higgs effective Lagrangian given by the product of the field labels in the
finite tuple `g`. -/
def termOfTuple {n : ℕ} (g : Fin n → FieldSpecification) : EFTLagrangianExclDeriv :=
  termOfList (List.ofFn g)

lemma termOfTuple_eq_ιMulti {n : ℕ} (g : Fin n → FieldSpecification) :
    termOfTuple g = SymmetricAlgebra.ιMulti ℂ
      (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec)) n
      (fun i => moduleBasis (g i)) := by
  rw [termOfTuple, termOfList_ofFn]

/-- Permuting a bosonic field tuple leaves its monomial unchanged. -/
lemma termOfTuple_comp_perm {n : ℕ} (g : Fin n → FieldSpecification) (e : Equiv.Perm (Fin n)) :
    termOfTuple (g ∘ e) = termOfTuple g := by
  rw [termOfTuple_eq_ιMulti, termOfTuple_eq_ιMulti]
  simpa [Function.comp_apply] using
    (SymmetricAlgebra.ιMulti ℂ
      (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec)) n).map_perm e
      (fun i => moduleBasis (g i))

/-!

## C. The field-content projection

We cannot define a basis on `EFTLagrangianExclDeriv` without choosing an ordering on the field
specification. Instead, given a multiset of field specifications, we define a linear map
projecting onto the span of the monomials with that field content. That span is one-dimensional,
which is the sense in which this projection plays the role of a coefficient.

-/

/-! ### C.1. The symmetric coordinate rule -/

/-- The symmetric multilinear rule underlying `coeff s`: a tuple of vectors is sent to
`termOfTuple g` weighted by the product of the `g`-coordinates of the vectors, summed over the
tuples `g` of fields with field content `s`. -/
def coeffOfVectorTuple (s : Multiset FieldSpecification) (n : ℕ) :
    SymmetricMap ℂ (Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec))
      EFTLagrangianExclDeriv (Fin n) where
  toMultilinearMap :=
    ∑ g : Fin n → FieldSpecification,
      if Multiset.ofList (List.ofFn g) = s then
        (LinearMap.toSpanSingleton ℂ EFTLagrangianExclDeriv (termOfTuple g)).compMultilinearMap
          ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
            fun i => moduleBasis.coord (g i))
      else 0
  map_perm' := by
    intro v e
    simp only [MultilinearMap.toFun_eq_coe, sum_apply]
    -- Name the summand family, and the reindexing `g ↦ g ∘ e.symm` of the index set.
    let F : (Fin n → FieldSpecification) →
        MultilinearMap ℂ
          (fun _ : Fin n => Module.Dual ℂ HiggsVec × Module.Dual ℂ (ConjModule HiggsVec))
          EFTLagrangianExclDeriv :=
      fun g =>
        if Multiset.ofList (List.ofFn g) = s then
          (LinearMap.toSpanSingleton ℂ EFTLagrangianExclDeriv (termOfTuple g)).compMultilinearMap
            ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
              fun i => moduleBasis.coord (g i))
        else 0
    let p : (Fin n → FieldSpecification) → (Fin n → FieldSpecification) :=
      fun g => g ∘ e.symm
    have hp : Function.Bijective p := by
      constructor
      · intro g h hgh
        funext i
        simpa [p, Function.comp_apply] using congrFun hgh (e i)
      · intro g
        refine ⟨g ∘ e, ?_⟩
        funext i
        simp [p, Function.comp_apply]
    change (∑ g, F g (fun i => v (e i))) = ∑ g, F g v
    calc
      _ = ∑ g, F (p g) v := by
        apply Finset.sum_congr rfl
        intro g _
        simp only [F, p]
        -- Reindexing the tuple by a permutation preserves its field content.
        have hms : Multiset.ofList (List.ofFn (g ∘ e.symm)) =
            Multiset.ofList (List.ofFn g) :=
          Multiset.coe_eq_coe.mpr (Equiv.Perm.ofFn_comp_perm e.symm g)
        rw [hms]
        split_ifs with h
        · simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
            MultilinearMap.mkPiAlgebra_apply, LinearMap.toSpanSingleton_apply,
            Function.comp_apply]
          -- The coordinate product is a finite product, so it is permutation invariant.
          have hprod : ∏ i, moduleBasis.coord (g i) (v (e i)) =
              ∏ i, moduleBasis.coord (g (e.symm i)) (v i) := by
            simpa using
              Equiv.prod_comp e (fun i => moduleBasis.coord (g (e.symm i)) (v i))
          rw [hprod, termOfTuple_comp_perm g e.symm]
        · simp
      _ = _ := hp.sum_comp (fun g => F g v)

/-! ### C.2. The projection and its value on monomials -/

/-- The projection of a non-derivative Higgs term onto the span of the monomials with field
content `s`. -/
def coeff (s : Multiset FieldSpecification) :
    EFTLagrangianExclDeriv →ₗ[ℂ] EFTLagrangianExclDeriv :=
  SymmetricAlgebra.liftSymmetric (coeffOfVectorTuple s)

/-- A monomial is preserved by the projection onto its own field content and killed by every
other. In particular the surviving monomial appears with coefficient one, with no factorial or
divided-power normalization, and this holds also when field labels repeat. -/
lemma coeff_apply_termOfList (s : Multiset FieldSpecification) (l : List FieldSpecification) :
    coeff s (termOfList l) = if Multiset.ofList l = s then termOfList l else 0 := by
  have hterm : termOfTuple l.get = termOfList l := by
    rw [termOfTuple, List.ofFn_get]
  rw [coeff, termOfList_eq_ιMulti, SymmetricAlgebra.liftSymmetric_apply_ιMulti]
  change (coeffOfVectorTuple s l.length).toMultilinearMap
    (fun i => moduleBasis (l.get i)) = _
  simp only [coeffOfVectorTuple, sum_apply]
  refine (Finset.sum_eq_single l.get ?_ ?_).trans ?_
  · intro g _ hg
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
    split_ifs with h
    · simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, LinearMap.toSpanSingleton_apply]
      -- Coordinate orthogonality kills every tuple other than the matching one.
      have hzero : ∏ k, moduleBasis.coord (g k) (moduleBasis (l.get k)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by
          rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hi])
      rw [hzero, zero_smul]
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h
  · rw [List.ofFn_get]
    split_ifs with h
    · simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, LinearMap.toSpanSingleton_apply, hterm]
      have hprod : ∏ i, moduleBasis.coord (l.get i) (moduleBasis (l.get i)) = 1 := by
        simp
      rw [hprod, one_smul]
      exact termOfList_eq_ιMulti l
    · simp

/-!

## D. Properties of the projection

-/

/-! ### D.1. Monomials span the space -/

/-- Every element of `EFTLagrangianExclDeriv` is a linear combination of Higgs monomials. -/
lemma mem_termOfList_span (V : EFTLagrangianExclDeriv) :
    V ∈ Submodule.span ℂ (Set.range termOfList) := by
  induction V using SymmetricAlgebra.induction with
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], termOfList_nil⟩)
  | ι v =>
      rw [← Basis.sum_repr moduleBasis v, map_sum]
      refine Submodule.sum_mem _ fun f _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨[f], by rw [termOfList_singleton]; rfl⟩)
  | mul a b ha hb =>
      induction ha using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨l₁, rfl⟩ := hx
          induction hb using Submodule.span_induction with
          | mem y hy =>
              obtain ⟨l₂, rfl⟩ := hy
              exact Submodule.subset_span ⟨l₁ ++ l₂, termOfList_append l₁ l₂⟩
          | zero => simp
          | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
          | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
      | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  | add a b ha hb => exact add_mem ha hb

/-! ### D.2. Idempotence -/

/-- `coeff s` is idempotent, and is therefore genuinely a projection on the whole algebra. -/
@[simp]
lemma coeff_coeff_self {s : Multiset FieldSpecification} (V : EFTLagrangianExclDeriv) :
    coeff s (coeff s V) = coeff s V := by
  have hV := mem_termOfList_span V
  induction hV using Submodule.span_induction with
  | mem W hW =>
      obtain ⟨l, rfl⟩ := hW
      rw [coeff_apply_termOfList]
      split_ifs with h
      · rw [coeff_apply_termOfList, if_pos h]
      · rw [map_zero]
  | zero => rw [map_zero, map_zero]
  | add W X _ _ hW hX => rw [map_add, map_add, hW, hX]
  | smul c W _ hW => rw [map_smul, map_smul, hW]

/-! ### D.3. One-dimensionality of the image -/

/-- The image of `coeff s` is the line spanned by the monomial with field content `s`: every
projected term is a scalar multiple of a single monomial. Since permutations act without a sign,
the choice of ordering `l` of the content is immaterial. -/
lemma coeff_eq_termOfList {s : Multiset FieldSpecification} (V : EFTLagrangianExclDeriv)
    {l : List FieldSpecification} (hl : Multiset.ofList l = s) :
    ∃ c : ℂ, coeff s V = c • termOfList l := by
  have hV := mem_termOfList_span V
  induction hV using Submodule.span_induction with
  | mem W hW =>
      obtain ⟨l', rfl⟩ := hW
      rw [coeff_apply_termOfList]
      split_ifs with h
      · refine ⟨1, ?_⟩
        rw [one_smul]
        exact termOfList_eq_of_perm (Multiset.coe_eq_coe.mp (h.trans hl.symm))
      · exact ⟨0, by rw [zero_smul]⟩
  | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
  | add W X _ _ hW hX =>
      obtain ⟨c₁, hc₁⟩ := hW
      obtain ⟨c₂, hc₂⟩ := hX
      exact ⟨c₁ + c₂, by rw [map_add, hc₁, hc₂, add_smul]⟩
  | smul a W _ hW =>
      obtain ⟨c, hc⟩ := hW
      exact ⟨a * c, by rw [map_smul, hc, smul_smul]⟩

end EFTLagrangianExclDeriv

end

end StandardModel.HiggsField
