/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded
/-!

# Dirac fermions

In this file we define Dirac fermions.
This corresponds to a combination of two Weyl fermions (ψ^α, χ_{dot α})
That is a LeftHandedWeyl and a DualRightHandedWeyl.

## References

- arXiv:0812.1594 page 197.

-/

@[expose] public section

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

/-- A Dirac fermion, consisting of a left handed Weyl fermion and a dual
  right handed Weyl fermion. -/
structure Dirac where
  /-- The left handed component of the Dirac fermion. -/
  left : LeftHandedWeyl
  /-- The right handed component of the Dirac fermion. -/
  dualRight : DualRightHandedWeyl

namespace Dirac

/-!

## The underlying module structure

We inherit the module structure on dirac fermions
from the module structure on left handed and dual right handed Weyl fermions.

-/

/-- The decomposition of a Dirac fermion into its left handed and
  dual right handed components. -/
def decomposeEquiv : Dirac ≃ LeftHandedWeyl × DualRightHandedWeyl where
  toFun d := (d.left, d.dualRight)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup Dirac := Equiv.addCommGroup decomposeEquiv

instance : Module ℂ Dirac := Equiv.module ℂ decomposeEquiv

@[simp]
lemma left_add (d₁ d₂ : Dirac) : (d₁ + d₂).left = d₁.left + d₂.left := rfl

@[simp]
lemma dualRight_add (d₁ d₂ : Dirac) : (d₁ + d₂).dualRight = d₁.dualRight + d₂.dualRight := rfl

@[simp]
lemma left_smul (c : ℂ) (d : Dirac) : (c • d).left = c • d.left := rfl

@[simp]
lemma dualRight_smul (c : ℂ) (d : Dirac) : (c • d).dualRight = c • d.dualRight := rfl

/-- The linear equivalence between `Dirac` and `LeftHandedWeyl × DualRightHandedWeyl`. -/
def decomposeLinEquiv : Dirac ≃ₗ[ℂ] LeftHandedWeyl × DualRightHandedWeyl where
  toEquiv := decomposeEquiv
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-!

## The chiral basis

-/

open Module

/-- The chiral basis of the Dirac fermions. -/
def chiralBasis : Basis (Fin 4) ℂ Dirac :=
  ((LeftHandedWeyl.basis.prod DualRightHandedWeyl.basis).reindex finSumFinEquiv).map
  decomposeLinEquiv.symm

lemma chiralBasis_cast_add (i : Fin 2) : chiralBasis (Fin.castAdd 2 i) =
    ⟨LeftHandedWeyl.basis i, 0⟩ := by
  fin_cases i
  all_goals
    simp only [chiralBasis, Nat.reduceAdd, Basis.map_apply, Basis.coe_reindex,
    Function.comp_apply, Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr]
    rfl

lemma chiralBasis_nat_add (i : Fin 2) : chiralBasis (Fin.natAdd 2 i) =
    ⟨0, DualRightHandedWeyl.basis i⟩ := by
  fin_cases i
  all_goals
    simp only [chiralBasis, Nat.reduceAdd, Basis.map_apply, Basis.coe_reindex,
    Function.comp_apply, Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr]
    rfl

/-!

## The representation of the Lorentz group

-/

/-- The representation of `SL(2, ℂ)` on Dirac fermions. -/
def rep : Representation ℂ SL(2,ℂ) Dirac where
  toFun g := decomposeLinEquiv.symm ∘ₗ
    (((LeftHandedWeyl.rep).prod (DualRightHandedWeyl.rep)) g) ∘ₗ
    decomposeLinEquiv
  map_one' := by
    ext1 i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp

lemma rep_apply_mk (g : SL(2,ℂ)) (ψ : LeftHandedWeyl) (χ : DualRightHandedWeyl) :
    rep g ⟨ψ, χ⟩ = ⟨LeftHandedWeyl.rep g ψ, DualRightHandedWeyl.rep g χ⟩ := rfl

/-- The equivalence between the representation on `Dirac` and the representation
  on `LeftHandedWeyl × DualRightHandedWeyl`. -/
def decomposeRepEquiv : rep.Equiv ((LeftHandedWeyl.rep).prod (DualRightHandedWeyl.rep))  where
  toLinearEquiv := decomposeLinEquiv
  isIntertwining' g := by
    ext1 x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Representation.prod_apply_apply]
    rfl

end Dirac

end
end Fermion
