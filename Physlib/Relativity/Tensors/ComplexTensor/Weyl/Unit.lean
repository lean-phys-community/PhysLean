/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Two
public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Contraction
/-!

# Units of Weyl fermions

We define the units for Weyl fermions, often denoted `δ` in the literature.

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-- The left-alt-left unit `δᵃₐ` as an element of `(leftHanded ⊗ altLeftHanded).V`. -/
def leftAltLeftUnitVal : (LeftHandedModule ⊗[ℂ] AltLeftHandedModule) :=
  leftAltLeftToMatrix.symm 1

/-- Expansion of `leftAltLeftUnitVal` into the basis. -/
lemma leftAltLeftUnitVal_expand_tmul : leftAltLeftUnitVal =
    leftBasis 0 ⊗ₜ[ℂ] altLeftBasis 0 + leftBasis 1 ⊗ₜ[ℂ] altLeftBasis 1 := by
  simp only [leftAltLeftUnitVal, Fin.isValue]
  erw [leftAltLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The left-alt-left unit `δᵃₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ altLeftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def leftAltLeftUnit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (leftHandedRep.tprod altLeftHandedRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • leftAltLeftUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • leftAltLeftUnitVal =
      (TensorProduct.map (leftHandedRep M) (altLeftHandedRep M)) (x • leftAltLeftUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [leftAltLeftUnitVal]
    rw [leftAltLeftToMatrix_ρ_symm]
    apply congrArg
    simp

lemma leftAltLeftUnit_apply_one : leftAltLeftUnit (1 : ℂ) = leftAltLeftUnitVal := by
  change (1 : ℂ) • leftAltLeftUnitVal = leftAltLeftUnitVal
  simp only [one_smul]

/-- The alt-left-left unit `δₐᵃ` as an element of `(altLeftHanded ⊗ leftHanded).V`. -/
def altLeftLeftUnitVal : (AltLeftHandedModule ⊗[ℂ] LeftHandedModule) :=
  altLeftLeftToMatrix.symm 1

/-- Expansion of `altLeftLeftUnitVal` into the basis. -/
lemma altLeftLeftUnitVal_expand_tmul : altLeftLeftUnitVal =
    altLeftBasis 0 ⊗ₜ[ℂ] leftBasis 0 + altLeftBasis 1 ⊗ₜ[ℂ] leftBasis 1 := by
  simp only [altLeftLeftUnitVal, Fin.isValue]
  rw [altLeftLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The alt-left-left unit `δₐᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ leftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def altLeftLeftUnit :
    (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (altLeftHandedRep.tprod leftHandedRep) where
  toFun := fun a =>
      let a' : ℂ := a
      a' • altLeftLeftUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • altLeftLeftUnitVal =
      (TensorProduct.map (altLeftHandedRep M) (leftHandedRep M)) (x • altLeftLeftUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [altLeftLeftUnitVal]
    rw [altLeftLeftToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, ← transpose_mul, SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq,
      one_ne_zero, not_false_eq_true, mul_nonsing_inv, transpose_one]

/-- Applying the morphism `altLeftLeftUnit` to `1` returns `altLeftLeftUnitVal`. -/
lemma altLeftLeftUnit_apply_one : altLeftLeftUnit (1 : ℂ) = altLeftLeftUnitVal := by
  change (1 : ℂ) • altLeftLeftUnitVal = altLeftLeftUnitVal
  simp only [one_smul]

/-- The right-alt-right unit `δ^{dot a}_{dot a}` as an element of
  `(rightHanded ⊗ altRightHanded).V`. -/
def rightAltRightUnitVal : RightHandedModule ⊗[ℂ] AltRightHandedModule :=
  rightAltRightToMatrix.symm 1

/-- Expansion of `rightAltRightUnitVal` into the basis. -/
lemma rightAltRightUnitVal_expand_tmul : rightAltRightUnitVal =
    rightBasis 0 ⊗ₜ[ℂ] altRightBasis 0 + rightBasis 1 ⊗ₜ[ℂ] altRightBasis 1 := by
  simp only [rightAltRightUnitVal, Fin.isValue]
  rw [rightAltRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The right-alt-right unit `δ^{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ altRightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def rightAltRightUnit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (rightHandedRep.tprod altRightHandedRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • rightAltRightUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • rightAltRightUnitVal =
      (TensorProduct.map (rightHandedRep M) (altRightHandedRep M)) (x • rightAltRightUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [rightAltRightUnitVal]
    rw [rightAltRightToMatrix_ρ_symm]
    apply congrArg
    simp only [RCLike.star_def, mul_one]
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp only [transpose_mul, transpose_transpose]
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma rightAltRightUnit_apply_one : rightAltRightUnit (1 : ℂ) = rightAltRightUnitVal := by
  change (1 : ℂ) • rightAltRightUnitVal = rightAltRightUnitVal
  simp only [one_smul]

/-- The alt-right-right unit `δ_{dot a}^{dot a}` as an element of
  `(rightHanded ⊗ altRightHanded).V`. -/
def altRightRightUnitVal : (AltRightHandedModule ⊗[ℂ] RightHandedModule) :=
  altRightRightToMatrix.symm 1

/-- Expansion of `altRightRightUnitVal` into the basis. -/
lemma altRightRightUnitVal_expand_tmul : altRightRightUnitVal =
    altRightBasis 0 ⊗ₜ[ℂ] rightBasis 0 + altRightBasis 1 ⊗ₜ[ℂ] rightBasis 1 := by
  simp only [altRightRightUnitVal, Fin.isValue]
  rw [altRightRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The alt-right-right unit `δ_{dot a}^{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ rightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def altRightRightUnit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (altRightHandedRep.tprod rightHandedRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • altRightRightUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • altRightRightUnitVal =
      (TensorProduct.map (altRightHandedRep M) (rightHandedRep M)) (x • altRightRightUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [altRightRightUnitVal]
    rw [altRightRightToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, RCLike.star_def]
    symm
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma altRightRightUnit_apply_one : altRightRightUnit (1 : ℂ) = altRightRightUnitVal := by
  change (1 : ℂ) • altRightRightUnitVal = altRightRightUnitVal
  simp only [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `altLeftLeftUnit` does nothing. -/
lemma contr_altLeftLeftUnit (x : LeftHandedModule) :
    (TensorProduct.lid ℂ _ <|
    leftAltContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (altLeftLeftUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span leftBasis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, leftAltContraction_basis,
    altLeftLeftUnit_apply_one, altLeftLeftUnitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `leftAltLeftUnit` does nothing. -/
lemma contr_leftAltLeftUnit (x : AltLeftHandedModule) :
    (TensorProduct.lid ℂ _ <|
    altLeftContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (leftAltLeftUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span altLeftBasis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, altLeftContraction_basis,
    leftAltLeftUnit_apply_one, leftAltLeftUnitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `altRightRightUnit` does nothing. -/
lemma contr_altRightRightUnit (x : RightHandedModule) :
    (TensorProduct.lid ℂ _ <|
    rightAltContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (altRightRightUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span rightBasis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, rightAltContraction_basis,
    altRightRightUnit_apply_one, altRightRightUnitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `rightAltRightUnit` does nothing. -/
lemma contr_rightAltRightUnit (x : AltRightHandedModule) :
    (TensorProduct.lid ℂ _ <|
    altRightContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (rightAltRightUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span altRightBasis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, altRightContraction_basis,
    rightAltRightUnit_apply_one, rightAltRightUnitVal_expand_tmul, add_tmul, tmul_add]

/-!

## Symmetry properties of the units

-/
open CategoryTheory

lemma altLeftLeftUnit_symm :
    altLeftLeftUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
    (TensorProduct.comm ℂ _ _ (leftAltLeftUnit (1 : ℂ))) := by
  rw [altLeftLeftUnit_apply_one, altLeftLeftUnitVal_expand_tmul]
  rw [leftAltLeftUnit_apply_one, leftAltLeftUnitVal_expand_tmul]
  rfl

lemma leftAltLeftUnit_symm :
    leftAltLeftUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (altLeftLeftUnit (1 : ℂ))) := by
  rw [altLeftLeftUnit_apply_one, altLeftLeftUnitVal_expand_tmul]
  rw [leftAltLeftUnit_apply_one, leftAltLeftUnitVal_expand_tmul]
  rfl

lemma altRightRightUnit_symm :
    altRightRightUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (rightAltRightUnit (1 : ℂ))) := by
  rw [altRightRightUnit_apply_one, altRightRightUnitVal_expand_tmul]
  rw [rightAltRightUnit_apply_one, rightAltRightUnitVal_expand_tmul]
  rfl

lemma rightAltRightUnit_symm :
    rightAltRightUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (altRightRightUnit (1 : ℂ))) := by
  rw [altRightRightUnit_apply_one, altRightRightUnitVal_expand_tmul]
  rw [rightAltRightUnit_apply_one, rightAltRightUnitVal_expand_tmul]
  rfl

end
end Fermion
