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

end EFTLagrangianExclDeriv

end

end StandardModel.HiggsField
