/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Unit
/-!

# Metrics of Weyl fermions

We define the metrics for Weyl fermions, often denoted `ε` in the literature.
These allow us to go from left-handed to alt-left-handed Weyl fermions and back,
and from right-handed to alt-right-handed Weyl fermions and back.

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-- The raw `2x2` matrix corresponding to the metric for fermions. -/
def metricRaw : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- Multiplying an element of `SL(2, ℂ)` on the left with the metric `𝓔` is equivalent
  to multiplying the inverse-transpose of that element on the right with the metric. -/
lemma comm_metricRaw (M : SL(2,ℂ)) : M.1 * metricRaw = metricRaw * (M.1⁻¹)ᵀ := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
  simp only [Fin.isValue, mul_zero, mul_neg, mul_one, zero_add, add_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, zero_smul, tail_cons, one_smul,
    empty_vecMul, neg_smul, neg_cons, neg_neg, neg_empty, empty_mul, Equiv.symm_apply_apply]

lemma metricRaw_comm (M : SL(2,ℂ)) : metricRaw * M.1 = (M.1⁻¹)ᵀ * metricRaw := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
  simp only [Fin.isValue, zero_mul, one_mul, zero_add, neg_mul, add_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_zero,
    mul_one, smul_empty, tail_cons, neg_smul, mul_neg, neg_cons, neg_neg, neg_zero, neg_empty,
    empty_vecMul, add_cons, empty_add_empty, empty_mul, Equiv.symm_apply_apply]

lemma star_comm_metricRaw (M : SL(2,ℂ)) : M.1.map star * metricRaw = metricRaw * ((M.1)⁻¹)ᴴ := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
  simp

lemma metricRaw_comm_star (M : SL(2,ℂ)) : metricRaw * M.1.map star = ((M.1)⁻¹)ᴴ * metricRaw := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
  simp

/-- The metric `εᵃᵃ` as an element of `(leftHanded ⊗ leftHanded).V`. -/
def leftMetricVal : LeftHandedModule ⊗[ℂ] LeftHandedModule :=
  leftLeftToMatrix.symm (- metricRaw)

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of `leftMetricVal` into the left basis. -/
lemma leftMetricVal_expand_tmul : leftMetricVal =
    - leftBasis 0 ⊗ₜ[ℂ] leftBasis 1 + leftBasis 1 ⊗ₜ[ℂ] leftBasis 0 := by
  simp only [leftMetricVal, Fin.isValue]
  rw [leftLeftToMatrix_symm_expand_tmul]
  simp only [metricRaw, neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, neg_zero, zero_smul, zero_add,
    neg_neg, one_smul, add_zero]
  module

lemma leftMetricVal_expand_tmul' : leftMetricVal = leftBasis 1 ⊗ₜ[ℂ] leftBasis 0
    - leftBasis 0 ⊗ₜ[ℂ] leftBasis 1 := by rw [leftMetricVal_expand_tmul]; abel

/-- The metric `εᵃᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ leftHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def leftMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (leftHandedRep.tprod leftHandedRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • leftMetricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • leftMetricVal =
      (TensorProduct.map (leftHandedRep M) (leftHandedRep M)) (x • leftMetricVal)
    simp only [map_smul]
    apply congrArg
    simp only [leftMetricVal, map_neg, neg_inj]
    rw [leftLeftToMatrix_ρ_symm]
    apply congrArg
    rw [comm_metricRaw, mul_assoc, ← @transpose_mul]
    simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
      not_false_eq_true, mul_nonsing_inv, transpose_one, mul_one]

lemma leftMetric_apply_one : leftMetric (1 : ℂ) = leftMetricVal := by
  change (1 : ℂ) • leftMetricVal = leftMetricVal
  simp only [one_smul]

/-- The metric `εₐₐ` as an element of `(altLeftHanded ⊗ altLeftHanded).V`. -/
def altLeftMetricVal : (AltLeftHandedModule ⊗[ℂ] AltLeftHandedModule) :=
  altLeftaltLeftToMatrix.symm metricRaw

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of `altLeftMetricVal` into the left basis. -/
lemma altLeftMetricVal_expand_tmul : altLeftMetricVal =
    altLeftBasis 0 ⊗ₜ[ℂ] altLeftBasis 1 - altLeftBasis 1 ⊗ₜ[ℂ] altLeftBasis 0 := by
  simp only [altLeftMetricVal, Fin.isValue]
  rw [altLeftaltLeftToMatrix_symm_expand_tmul]
  simp only [metricRaw, of_apply, cons_val', empty_val', cons_val_fin_one, Fin.sum_univ_two,
    Fin.isValue, cons_val_zero, cons_val_one, zero_smul, one_smul, zero_add, add_zero]
  module

/-- The metric `εₐₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ altLeftHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def altLeftMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (altLeftHandedRep.tprod altLeftHandedRep) where
    toFun := fun a =>
      let a' : ℂ := a
      a' • altLeftMetricVal
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • altLeftMetricVal =
        (TensorProduct.map (altLeftHandedRep M) (altLeftHandedRep M)) (x • altLeftMetricVal)
      simp only [map_smul]
      apply congrArg
      simp only [altLeftMetricVal]
      rw [altLeftaltLeftToMatrix_ρ_symm]
      apply congrArg
      rw [← metricRaw_comm, mul_assoc]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, mul_nonsing_inv, mul_one]

lemma altLeftMetric_apply_one : altLeftMetric (1 : ℂ) = altLeftMetricVal := by
  change (1 : ℂ) • altLeftMetricVal = altLeftMetricVal
  simp only [one_smul]

/-- The metric `ε^{dot a}^{dot a}` as an element of `(rightHanded ⊗ rightHanded).V`. -/
def rightMetricVal : (RightHandedModule ⊗[ℂ] RightHandedModule) :=
  rightRightToMatrix.symm (- metricRaw)

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of `rightMetricVal` into the left basis. -/
lemma rightMetricVal_expand_tmul : rightMetricVal =
    - rightBasis 0 ⊗ₜ[ℂ] rightBasis 1 + rightBasis 1 ⊗ₜ[ℂ] rightBasis 0 := by
  simp only [rightMetricVal, Fin.isValue]
  rw [rightRightToMatrix_symm_expand_tmul]
  simp only [metricRaw, neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, neg_zero, zero_smul, zero_add,
    neg_neg, one_smul, add_zero]
  module

lemma rightMetricVal_expand_tmul' : rightMetricVal = rightBasis 1 ⊗ₜ[ℂ] rightBasis 0
    - rightBasis 0 ⊗ₜ[ℂ] rightBasis 1 := by rw [rightMetricVal_expand_tmul]; abel

/-- The metric `ε^{dot a}^{dot a}` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ rightHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def rightMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (rightHandedRep.tprod rightHandedRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • rightMetricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • rightMetricVal =
      (TensorProduct.map (rightHandedRep M) (rightHandedRep M)) (x • rightMetricVal)
    simp only [map_smul]
    apply congrArg
    simp only [rightMetricVal, map_neg, neg_inj]
    trans rightRightToMatrix.symm ((M.1).map star * metricRaw * ((M.1).map star)ᵀ)
    · apply congrArg
      rw [star_comm_metricRaw, mul_assoc]
      have h1 : ((M.1)⁻¹ᴴ * ((M.1).map star)ᵀ) = 1 := by
        trans (M.1)⁻¹ᴴ * ((M.1))ᴴ
        · rfl
        rw [← @conjTranspose_mul]
        simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
          not_false_eq_true, mul_nonsing_inv, conjTranspose_one]
      rw [h1]
      simp
    · rw [← rightRightToMatrix_ρ_symm metricRaw M]

lemma rightMetric_apply_one : rightMetric (1 : ℂ) = rightMetricVal := by
  change (1 : ℂ) • rightMetricVal = rightMetricVal
  simp only [one_smul]

/-- The metric `ε_{dot a}_{dot a}` as an element of `(altRightHanded ⊗ altRightHanded).V`. -/
def altRightMetricVal : AltRightHandedModule ⊗[ℂ] AltRightHandedModule :=
  altRightAltRightToMatrix.symm (metricRaw)

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of `rightMetricVal` into the left basis. -/
lemma altRightMetricVal_expand_tmul : altRightMetricVal =
    altRightBasis 0 ⊗ₜ[ℂ] altRightBasis 1 - altRightBasis 1 ⊗ₜ[ℂ] altRightBasis 0 := by
  simp only [altRightMetricVal, Fin.isValue]
  erw [altRightAltRightToMatrix_symm_expand_tmul]
  simp only [metricRaw, of_apply, cons_val', empty_val', cons_val_fin_one, Fin.sum_univ_two,
    Fin.isValue, cons_val_zero, cons_val_one, zero_smul, one_smul, zero_add, add_zero]
  module

/-- The metric `ε_{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ altRightHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def altRightMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (altRightHandedRep.tprod altRightHandedRep) where
  toFun := fun a =>
      let a' : ℂ := a
      a' • altRightMetricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • altRightMetricVal =
      (TensorProduct.map (altRightHandedRep M) (altRightHandedRep M)) (x • altRightMetricVal)
    simp only [map_smul]
    apply congrArg
    trans altRightAltRightToMatrix.symm
      (((M.1)⁻¹).conjTranspose * metricRaw * (((M.1)⁻¹).conjTranspose)ᵀ)
    · rw [altRightMetricVal]
      apply congrArg
      rw [← metricRaw_comm_star, mul_assoc]
      have h1 : ((M.1).map star * (M.1)⁻¹ᴴᵀ) = 1 := by
        refine transpose_eq_one.mp ?_
        rw [@transpose_mul]
        simp only [transpose_transpose, RCLike.star_def]
        change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
        rw [← @conjTranspose_mul]
        simp
      rw [h1, mul_one]
    · rw [← altRightAltRightToMatrix_ρ_symm metricRaw M]
      rfl

lemma altRightMetric_apply_one : altRightMetric (1 : ℂ) = altRightMetricVal := by
  change (1 : ℂ) • altRightMetricVal = altRightMetricVal
  simp only [one_smul]

/-!

## Contraction of metrics

-/

set_option backward.isDefEq.respectTransparency false in
lemma leftAltContraction_apply_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (leftAltContraction.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (leftMetric 1) ⊗ₜ[ℂ] (altLeftMetric 1)) = altLeftLeftUnit (1 : ℂ) := by
  rw [leftMetric_apply_one, altLeftMetric_apply_one]
  rw [leftMetricVal_expand_tmul', altLeftMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [← Representation.IntertwiningMap.toLinearMap_apply]
  repeat erw [leftAltContraction_basis]
  simp only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte, one_smul, zero_ne_one]
  erw [altLeftLeftUnit_apply_one, altLeftLeftUnitVal_expand_tmul]
  rw [add_comm]
  module

lemma altLeftContraction_apply_metric :
    (TensorProduct.comm ℂ _ _ <|
    (TensorProduct.lid ℂ _).lTensor _ <|
    (altLeftContraction.toLinearMap.rTensor _).lTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
    TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
    (altLeftMetric 1) ⊗ₜ[ℂ] (leftMetric 1)) = leftAltLeftUnit (1 : ℂ) := by
  rw [leftMetric_apply_one, altLeftMetric_apply_one]
  rw [leftMetricVal_expand_tmul', altLeftMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [← Representation.IntertwiningMap.toLinearMap_apply]
  repeat erw [altLeftContraction_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, ↓reduceIte, one_smul, Nat.zero_mod,
    zero_ne_one, zero_smul, sub_zero, one_ne_zero, zero_sub, sub_neg_eq_add,
    Representation.IntertwiningMap.coe_toLinearMap]
  erw [leftAltLeftUnit_apply_one, leftAltLeftUnitVal_expand_tmul]

set_option backward.isDefEq.respectTransparency false in
lemma rightAltContraction_apply_metric :
    (TensorProduct.comm ℂ _ _ <|
    (TensorProduct.lid ℂ _).lTensor _ <|
    (rightAltContraction.toLinearMap.rTensor _).lTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
    TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
    (rightMetric 1) ⊗ₜ[ℂ] (altRightMetric 1)) = altRightRightUnit (1 : ℂ) := by
  rw [rightMetric_apply_one, altRightMetric_apply_one]
  rw [rightMetricVal_expand_tmul', altRightMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [← Representation.IntertwiningMap.toLinearMap_apply]
  repeat erw [rightAltContraction_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.zero_mod, one_ne_zero, ↓reduceIte,
    one_smul, zero_ne_one]
  erw [altRightRightUnit_apply_one, altRightRightUnitVal_expand_tmul]
  rw [add_comm]
  module

lemma altRightContraction_apply_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (altRightContraction.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (altRightMetric 1) ⊗ₜ[ℂ] (rightMetric 1)) = rightAltRightUnit (1 : ℂ) := by
  rw [rightMetric_apply_one, altRightMetric_apply_one]
  rw [rightMetricVal_expand_tmul', altRightMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [← Representation.IntertwiningMap.toLinearMap_apply]
  repeat erw [altRightContraction_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, ↓reduceIte, one_smul, Nat.zero_mod,
    zero_ne_one, zero_smul, sub_zero, one_ne_zero, zero_sub, sub_neg_eq_add,
    Representation.IntertwiningMap.coe_toLinearMap]
  erw [rightAltRightUnit_apply_one, rightAltRightUnitVal_expand_tmul]

end
end Fermion
