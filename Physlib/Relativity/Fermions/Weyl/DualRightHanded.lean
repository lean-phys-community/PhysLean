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

## Dual right handed Weyl fermions


In this file we define dual right handed Weyl fermions.
These sit in the dual-conjugate representation of `SL(2,ℂ)`,
and we consider them to have down indices `ψ_\dot α}` with `α = 1,2`.

-/

@[expose] public section

namespace Fermion
noncomputable section

/-- The module in which dual-right handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure DualRightHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace DualRightHandedWeyl
open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## Underlying module structure

-/

/-- The equivalence between `DualRightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : DualRightHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid DualRightHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup DualRightHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ DualRightHandedWeyl := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `DualRightHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : DualRightHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `DualRightHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : DualRightHandedWeyl) := toFin2ℂEquiv ψ

lemma toFin2ℂ_eq_val (ψ : DualRightHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl

/-!

## Basis

-/


/-- The standard basis on dual-right-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ DualRightHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ DualRightHandedWeyl.toFin2ℂFun)


lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, Equiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk,
    Equiv.addEquiv_symm_apply]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : DualRightHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

/-!

## Representation

-/


/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)^†.
    In index notation this corresponds to a Weyl fermion with index `ψ_{dot a}`. -/
def rep : Representation ℂ SL(2,ℂ) DualRightHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : DualRightHandedWeyl) =>
      DualRightHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹).conjTranspose *ᵥ ψ.toFin2ℂ),
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
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact conjTranspose_mul _ _

lemma rep_apply (M : SL(2,ℂ)) (ψ : DualRightHandedWeyl) :
    rep M ψ = ⟨(M.1⁻¹).conjTranspose *ᵥ ψ.1⟩ := rfl

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : DualRightHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, (M.1⁻¹).conjTranspose i j * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, (M.1⁻¹).conjTranspose j i • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) :
    (LinearMap.toMatrix basis basis) (rep M) = (M.1⁻¹).conjTranspose := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change ((M.1⁻¹).conjTranspose *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = star (M.1⁻¹ i j) := by
  fin_cases j <;> simp [rep_apply_basis]

end DualRightHandedWeyl
end
end Fermion
