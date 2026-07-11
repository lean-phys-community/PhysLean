/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Modules
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Meta.Informal.Basic
public import Physlib.Meta.TODO.Basic
/-!

# Weyl fermions

A good reference for the material in this file is:
https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## Left-handed Weyl fermions

-/

namespace LeftHandedWeyl

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


/-!

## Dual Left-handed Weyl fermions

-/

namespace DualLeftHandedWeyl

/-- The standard basis on dual-left-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ DualLeftHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ DualLeftHandedWeyl.toFin2ℂFun)

lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, Equiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk,
    Equiv.addEquiv_symm_apply]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : DualLeftHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ. In index notation corresponds to a left-handed Weyl fermion with indices ψ_a. -/
def rep : Representation ℂ SL(2,ℂ) DualLeftHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : DualLeftHandedWeyl) =>
      DualLeftHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ ψ.toFin2ℂ),
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
    exact transpose_mul _ _

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : DualLeftHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, M.1⁻¹ j i * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, M.1⁻¹ i j • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) : (LinearMap.toMatrix basis basis) (rep M) = (M.1⁻¹)ᵀ := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change ((M.1⁻¹)ᵀ *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = M.1⁻¹ i j := by
  fin_cases j <;> simp [rep_apply_basis]

end DualLeftHandedWeyl

/-!

## Right-handed Weyl fermions

-/

namespace RightHandedWeyl

/-- The standard basis on right-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ RightHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ RightHandedWeyl.toFin2ℂFun)

lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, Equiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk,
    Equiv.addEquiv_symm_apply]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : RightHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

/-- The vector space ℂ^2 carrying the conjugate representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^{dot a}. -/
def rep : Representation ℂ SL(2,ℂ) RightHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : RightHandedWeyl) =>
      RightHandedWeyl.toFin2ℂEquiv.symm (M.1.map star *ᵥ ψ.toFin2ℂ),
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
    simp only [SpecialLinearGroup.coe_mul, RCLike.star_def, Matrix.map_mul, LinearMap.coe_mk,
      AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec]

lemma rep_apply (M : SL(2,ℂ)) (ψ : RightHandedWeyl) : rep M ψ = ⟨M.1.map star *ᵥ ψ.1⟩ := rfl

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : RightHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, M.1.map star i j * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, M.1.map star j i • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) : (LinearMap.toMatrix basis basis) (rep M) = M.1.map star := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1.map star *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = star (M.1 j i) := by
  fin_cases j <;> simp [rep_apply_basis]

end RightHandedWeyl

/-!

## Dual Right-handed Weyl fermions

-/

namespace DualRightHandedWeyl

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

/-!

## Duals of Weyl fermions

The dual of `LeftHandedWeyl` is `DualLeftHandedWeyl`, and the dual of `RightHandedWeyl` is
`DualRightHandedWeyl`.

-/

/-- The morphism between the representation `leftHanded` and the representation
  `dualLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def LeftHandedWeyl.dual : LeftHandedWeyl.rep.IntertwiningMap DualLeftHandedWeyl.rep where
  toFun := fun ψ => DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ)
  map_add' := by
    intro ψ ψ'
    simp only [mulVec_add, LinearEquiv.map_add]
  map_smul' := by
    intro a ψ
    simp only [mulVec_smul, LinearEquiv.map_smul]
    rfl
  isIntertwining' := by
    intro M
    refine LinearMap.ext (fun ψ => ?_)
    change DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ M.1 *ᵥ ψ.val) =
      DualLeftHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ !![0, 1; -1, 0] *ᵥ ψ.val)
    apply congrArg
    rw [mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp

lemma LeftHandedWeyl.dual_hom_apply (ψ : LeftHandedWeyl) :
    LeftHandedWeyl.dual ψ =
    DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The morphism from `dualLeftHanded` to
  `leftHanded` defined by multiplying an element of
  DualLeftHandedWeyl by the matrix `εₐ₁ₐ₂ = !![0, -1; 1, 0]`. -/
def DualLeftHandedWeyl.dual : DualLeftHandedWeyl.rep.IntertwiningMap LeftHandedWeyl.rep where
  toFun := fun ψ =>
      LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ)
  map_add' := by
    intro ψ ψ'
    simp only [map_add]
    rw [mulVec_add, LinearEquiv.map_add]
  map_smul' := by
    intro a ψ
    simp only [LinearEquiv.map_smul]
    rw [mulVec_smul, LinearEquiv.map_smul]
    rfl
  isIntertwining' := by
    intro M
    refine LinearMap.ext (fun ψ => ?_)
    change LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ (M.1⁻¹)ᵀ *ᵥ ψ.val) =
      LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ !![0, -1; 1, 0] *ᵥ ψ.val)
    rw [EquivLike.apply_eq_iff_eq, mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe,
      eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp

lemma DualLeftHandedWeyl.dual_hom_apply (ψ : DualLeftHandedWeyl) :
    DualLeftHandedWeyl.dual ψ =
    LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The equivalence between the representation `leftHanded` and the representation
  `dualLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def LeftHandedWeyl.dualEquiv : LeftHandedWeyl.rep.Equiv DualLeftHandedWeyl.rep := by
  refine Representation.Equiv.mk'  LeftHandedWeyl.dual DualLeftHandedWeyl.dual ?_ ?_
  · intro x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      Representation.IntertwiningMap.coe_toLinearMap]
    rw [DualLeftHandedWeyl.dual_hom_apply, LeftHandedWeyl.dual_hom_apply]
    rw [DualLeftHandedWeyl.toFin2ℂ, LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, -1; (1 : ℂ), 0] * !![0, 1; -1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl
  · intro ψ
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      Representation.IntertwiningMap.coe_toLinearMap]
    rw [DualLeftHandedWeyl.dual_hom_apply, LeftHandedWeyl.dual_hom_apply, LeftHandedWeyl.toFin2ℂ,
      LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, (1 : ℂ); -1, 0] * !![0, -1; 1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl

/-- `leftHandedDualEquiv` acting on an element `ψ : leftHanded` corresponds
  to multiplying `ψ` by the matrix `!![0, 1; -1, 0]`. -/
lemma LeftHandedWeyl.dualEquiv_hom_hom_apply (ψ : LeftHandedWeyl) :
    LeftHandedWeyl.dualEquiv ψ =
    DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The inverse of `leftHandedDualEquiv` acting on an element`ψ : dualLeftHanded` corresponds
  to multiplying `ψ` by the matrix `!![0, -1; 1, 0]`. -/
lemma LeftHandedWeyl.dualEquiv_inv_hom_apply (ψ : DualLeftHandedWeyl) :
    LeftHandedWeyl.dualEquiv.symm ψ =
    LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The linear equivalence between `rightHandedWeyl` and `DualRightHandedWeyl` given by multiplying
an element of `rightHandedWeyl` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`.
-/
informal_definition RightHandedWeyl.dualEquiv where
  deps := [``RightHandedWeyl, ``DualRightHandedWeyl]
  tag := "6VZR4"

/-- The linear equivalence `rightHandedWeylDualEquiv` is equivariant with respect to the action of
`SL(2,C)` on `rightHandedWeyl` and `DualRightHandedWeyl`.
-/
informal_lemma RightHandedWeyl.dualEquiv_equivariant where
  deps := [``RightHandedWeyl.dualEquiv]
  tag := "6VZSG"

end

end Fermion
