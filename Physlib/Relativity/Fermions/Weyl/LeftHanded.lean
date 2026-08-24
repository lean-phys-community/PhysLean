/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Physlib.Meta.TODO.Basic
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Meta.Informal.Basic
public import Physlib.Meta.TODO.Basic
/-!

## Left handed Weyl fermions


In this file we define Left handed Weyl fermions.
These sit in the fundamental representation of `SL(2,ℂ)`,
and we consider them to have up indices `ψ^α` with `α = 1,2`.

-/

@[expose] public section

namespace Fermion
noncomputable section

section LeftHanded

/-- The module in which left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure LeftHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace LeftHandedWeyl
open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## Underlying module structure

-/

/-- The equivalence between `LeftHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : LeftHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid LeftHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup LeftHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ LeftHandedWeyl := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `LeftHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : LeftHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `LeftHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : LeftHandedWeyl) := toFin2ℂEquiv ψ

lemma toFin2ℂ_eq_val (ψ : LeftHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl

/-!

## Basis

-/

/-- The standard basis on left-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ LeftHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ LeftHandedWeyl.toFin2ℂFun)

lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, Equiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk,
    Equiv.addEquiv_symm_apply]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : LeftHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

/-!

## Representation

-/

/-- The vector space ℂ^2 carrying the fundamental representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^a. -/
def rep : Representation ℂ SL(2,ℂ) LeftHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : LeftHandedWeyl) =>
      LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    simp only [SpecialLinearGroup.coe_mul]
    ext1 x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply,
      mulVec_mulVec]

lemma rep_apply (M : SL(2,ℂ)) (ψ : LeftHandedWeyl) : rep M ψ = ⟨M.1 *ᵥ ψ.1⟩ := rfl

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : LeftHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, M.1 i j * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, M.1 j i • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) : (LinearMap.toMatrix basis basis) (rep M) = M.1 := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1 *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = M.1 j i := by
  fin_cases j <;> simp [rep_apply_basis]

end LeftHandedWeyl

end LeftHanded

end
end Fermion
