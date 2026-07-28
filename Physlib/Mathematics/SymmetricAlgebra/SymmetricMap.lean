/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George McNinch, Nathaneal Sajan
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Symmetric multilinear maps

This module provides a temporary compatibility layer for symmetric multilinear maps.

The declarations follow the root-level names selected by George McNinch in Mathlib PR #41426. This
module should be removed in favor of the Mathlib implementation once that API is available upstream.

## Main definitions

* `SymmetricMap` is a multilinear map invariant under permutations of its arguments.
* `SymmetricMap.compLinearMap` precomposes every argument with a linear map.
* `LinearMap.compSymmetricMap` postcomposes with a linear map.
* `mkPiAlgebra` is the symmetric multilinear product map into a commutative algebra.

-/

@[expose] public section

universe u u' u₁ v w w'

/-!

## A. Symmetric multilinear maps

-/

/-- A symmetric `R`-multilinear map from `ι → M` to `N` is a multilinear map whose value is
unchanged by permutations of its arguments. -/
structure SymmetricMap
    (R : Type u) (M : Type v) (N : Type w) (ι : Type u')
    [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    extends MultilinearMap R (fun _ : ι => M) N where
  /-- Permuting the arguments does not change the value of the map. -/
  map_perm' (v : ι → M) (e : Equiv.Perm ι) :
    toFun (fun i => v (e i)) = toFun v

namespace SymmetricMap

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {P : Type w'} [AddCommMonoid P] [Module R P]
variable {ι : Type u'}

/-!

### A.1. Coercions and extensionality

-/

instance : FunLike (SymmetricMap R M N ι) (ι → M) N where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr

lemma coe_injective :
    Function.Injective ((↑) : SymmetricMap R M N ι → (ι → M) → N) :=
  DFunLike.coe_injective

/-- Two symmetric multilinear maps are equal when they agree on every input. -/
@[ext]
lemma ext {f g : SymmetricMap R M N ι} (h : ∀ v, f v = g v) : f = g :=
  DFunLike.ext f g h

attribute [coe] SymmetricMap.toMultilinearMap

instance : Coe (SymmetricMap R M N ι) (MultilinearMap R (fun _ : ι => M) N) :=
  ⟨fun f => f.toMultilinearMap⟩

@[simp, norm_cast]
lemma coe_coe (f : SymmetricMap R M N ι) :
    ⇑(f : MultilinearMap R (fun _ : ι => M) N) = f :=
  rfl

/-- Permuting the arguments of a symmetric multilinear map does not change its value. -/
@[simp]
lemma map_perm (f : SymmetricMap R M N ι) (e : Equiv.Perm ι) (v : ι → M) :
    f (fun i => v (e i)) = f v :=
  f.map_perm' v e

/-!

### A.2. Additive and module structure

-/

instance : Add (SymmetricMap R M N ι) where
  add f g := ⟨f.1 + g.1, fun _ _ => by simp⟩

@[simp]
lemma add_coe (f g : SymmetricMap R M N ι) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
lemma toMultilinearMap_add (f g : SymmetricMap R M N ι) :
    (f + g).toMultilinearMap = f.toMultilinearMap + g.toMultilinearMap :=
  rfl

instance : Zero (SymmetricMap R M N ι) where
  zero := ⟨0, fun _ _ => rfl⟩

@[simp]
lemma zero_coe : ⇑(0 : SymmetricMap R M N ι) = 0 :=
  rfl

@[simp, norm_cast]
lemma toMultilinearMap_zero :
    (0 : SymmetricMap R M N ι).toMultilinearMap = 0 :=
  rfl

section ScalarAction

variable {S : Type u₁} [Monoid S]
variable [DistribMulAction S N] [SMulCommClass R S N]

instance : SMul S (SymmetricMap R M N ι) where
  smul c f := ⟨c • f.1, fun _ _ => by simp⟩

@[simp]
lemma smul_coe (c : S) (f : SymmetricMap R M N ι) : ⇑(c • f) = c • ⇑f :=
  rfl

@[simp, norm_cast]
lemma toMultilinearMap_smul (c : S) (f : SymmetricMap R M N ι) :
    (c • f).toMultilinearMap = c • f.toMultilinearMap :=
  rfl

end ScalarAction

instance : AddCommMonoid (SymmetricMap R M N ι) := fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => smul_coe _ _

section DistribMulAction

variable {S : Type u₁} [Monoid S]
variable [DistribMulAction S N] [SMulCommClass R S N]

instance : DistribMulAction S (SymmetricMap R M N ι) where
  one_smul _ := ext fun _ => one_smul S _
  mul_smul c d _ := ext fun _ => mul_smul c d _
  smul_zero c := ext fun _ => smul_zero c
  smul_add c _ _ := ext fun _ => smul_add c _ _

end DistribMulAction

section Module

variable {S : Type u₁} [Semiring S]
variable [Module S N] [SMulCommClass R S N]

instance : Module S (SymmetricMap R M N ι) where
  add_smul c d _ := ext fun _ => add_smul c d _
  zero_smul _ := ext fun _ => zero_smul S _

end Module

/-!

### A.3. Composition

-/

/-- Precompose every argument of a symmetric multilinear map with the same linear map. -/
def compLinearMap (f : SymmetricMap R N P ι) (g : M →ₗ[R] N) : SymmetricMap R M P ι :=
  ⟨f.1.compLinearMap fun _ => g, fun v e => f.map_perm e (g ∘ v)⟩

@[simp]
lemma compLinearMap_apply (f : SymmetricMap R N P ι) (g : M →ₗ[R] N) (v : ι → M) :
    f.compLinearMap g v = f (g ∘ v) :=
  rfl

end SymmetricMap

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {P : Type w'} [AddCommMonoid P] [Module R P]
variable {ι : Type u'}

/-- Postcompose a symmetric multilinear map with a linear map. -/
def compSymmetricMap (f : N →ₗ[R] P) (g : SymmetricMap R M N ι) : SymmetricMap R M P ι :=
  ⟨f.compMultilinearMap g, fun v e => f.congr_arg (g.map_perm e v)⟩

@[simp]
lemma compSymmetricMap_apply (f : N →ₗ[R] P) (g : SymmetricMap R M N ι) (v : ι → M) :
    f.compSymmetricMap g v = f (g v) :=
  rfl

end LinearMap

/-!

### A.4. Products in commutative algebras

-/

section Product

variable (R : Type u) [CommSemiring R]
variable (ι : Type u')
variable (A : Type w) [CommSemiring A] [Algebra R A]

/-- The symmetric multilinear map into a commutative algebra that sends a finite family to the
product of its entries. -/
def mkPiAlgebra [Fintype ι] : SymmetricMap R A A ι :=
  ⟨MultilinearMap.mkPiAlgebra R ι A, fun v e => Equiv.prod_comp e v⟩

@[simp]
lemma mkPiAlgebra_apply [Fintype ι] (v : ι → A) :
    mkPiAlgebra R ι A v = ∏ i, v i :=
  rfl

end Product
