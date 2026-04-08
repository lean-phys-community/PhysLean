/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Units.Pre
/-!

# Metric for complex Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory
namespace Lorentz

/-- The metric `ηᵃᵃ` as an element of `(complexContr ⊗ complexContr).V`. -/
def contrMetricVal : (complexContr ⊗ complexContr).V :=
  contrContrToMatrix.symm ((@minkowskiMatrix 3).map ofRealHom)

set_option backward.isDefEq.respectTransparency false in
/-- The expansion of `contrMetricVal` into basis vectors. -/
lemma contrMetricVal_expand_tmul : contrMetricVal =
    complexContrBasis (Sum.inl 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inl 0)
    - complexContrBasis (Sum.inr 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 0)
    - complexContrBasis (Sum.inr 1) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 1)
    - complexContrBasis (Sum.inr 2) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 2) := by
  simp only [contrMetricVal, Fin.isValue]
  rw [contrContrToMatrix_symm_expand_tmul]
  simp only [map_apply, ofRealHom_eq_coe, coe_smul, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq,
    not_false_eq_true, minkowskiMatrix.off_diag_zero, zero_smul, add_zero, zero_add, Sum.inr.injEq,
    zero_ne_one, Fin.reduceEq, one_ne_zero]
  rw [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.inr_i_inr_i]
  simp only [Fin.isValue, one_smul, neg_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The metric `ηᵃᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexContr`,
  making its invariance under the action of `SL(2,ℂ)`. -/
def contrMetric : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexContr := Rep.ofHom {
    toFun := fun a =>
      let a' : ℂ := a
      a' • contrMetricVal,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • contrMetricVal =
        (TensorProduct.map (complexContr.ρ M) (complexContr.ρ M)) (x • contrMetricVal)
      simp only [map_smul]
      apply congrArg
      simp only [contrMetricVal]
      rw [contrContrToMatrix_ρ_symm]
      apply congrArg
      simp only [LorentzGroup.toComplex_mul_minkowskiMatrix_mul_transpose]
}

lemma contrMetric_apply_one : contrMetric.hom (1 : ℂ) = contrMetricVal := by
  change (1 : ℂ) • contrMetricVal = contrMetricVal
  simp only [one_smul]

/-- The metric `ηᵢᵢ` as an element of `(complexCo ⊗ complexCo).V`. -/
def coMetricVal : (complexCo ⊗ complexCo).V :=
  coCoToMatrix.symm ((@minkowskiMatrix 3).map ofRealHom)

set_option backward.isDefEq.respectTransparency false in
/-- The expansion of `coMetricVal` into basis vectors. -/
lemma coMetricVal_expand_tmul : coMetricVal =
    complexCoBasis (Sum.inl 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inl 0)
    - complexCoBasis (Sum.inr 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 0)
    - complexCoBasis (Sum.inr 1) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 1)
    - complexCoBasis (Sum.inr 2) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 2) := by
  simp only [coMetricVal, Fin.isValue]
  rw [coCoToMatrix_symm_expand_tmul]
  simp only [map_apply, ofRealHom_eq_coe, coe_smul, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq,
    not_false_eq_true, minkowskiMatrix.off_diag_zero, zero_smul, add_zero, zero_add, Sum.inr.injEq,
    zero_ne_one, Fin.reduceEq, one_ne_zero]
  rw [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.inr_i_inr_i]
  simp only [Fin.isValue, one_smul, neg_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The metric `ηᵢᵢ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexCo`,
  making its invariance under the action of `SL(2,ℂ)`. -/
def coMetric : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexCo := Rep.ofHom {
    toFun := fun a =>
      let a' : ℂ := a
      a' • coMetricVal,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • coMetricVal =
        (TensorProduct.map (complexCo.ρ M) (complexCo.ρ M)) (x • coMetricVal)
      simp only [map_smul]
      apply congrArg
      simp only [coMetricVal]
      rw [coCoToMatrix_ρ_symm]
      apply congrArg
      rw [LorentzGroup.toComplex_inv]
      simp only [LorentzGroup.inv_eq_dual, SL2C.toLorentzGroup_apply_coe,
        LorentzGroup.toComplex_transpose_mul_minkowskiMatrix_mul_self]
}

lemma coMetric_apply_one : coMetric.hom (1 : ℂ) = coMetricVal := by
  change (1 : ℂ) • coMetricVal = coMetricVal
  simp only [one_smul]

/-!

## Contraction of metrics

-/

set_option backward.isDefEq.respectTransparency false in
lemma contrCoContraction_apply_metric : (β_ complexContr complexCo).hom.hom
    ((complexContr ◁ (λ_ complexCo).hom)
    ((complexContr ◁ contrCoContraction ▷ complexCo)
    ((complexContr ◁ (α_ complexContr complexCo complexCo).inv)
    ((α_ complexContr complexContr (complexCo ⊗ complexCo)).hom
    (contrMetric.hom (1 : ℂ) ⊗ₜ[ℂ] coMetric.hom (1 : ℂ)))))) =
    coContrUnit.hom (1 : ℂ) := by
  rw [contrMetric_apply_one, coMetric_apply_one]
  rw [contrMetricVal_expand_tmul, coMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub]
  simp [← Representation.IntertwiningMap.toLinearMap_apply]
  repeat erw [contrCoContraction_basis']
  simp only [Fin.isValue, ↓reduceIte, one_smul, reduceCtorEq, zero_smul, sub_zero, zero_sub,
    Sum.inr.injEq, one_ne_zero, Fin.reduceEq, sub_neg_eq_add, zero_ne_one, sub_self]
  erw [coContrUnit_apply_one, coContrUnitVal_expand_tmul]

set_option backward.isDefEq.respectTransparency false in
lemma coContrContraction_apply_metric : (β_ complexCo complexContr).hom.hom
    ((complexCo ◁ (λ_ complexContr).hom)
    ((complexCo ◁ coContrContraction ▷ complexContr)
    ((complexCo ◁ (α_ complexCo complexContr complexContr).inv)
    ((α_ complexCo complexCo (complexContr ⊗ complexContr)).hom
    (coMetric.hom (1 : ℂ) ⊗ₜ[ℂ] contrMetric.hom (1 : ℂ)))))) =
    contrCoUnit.hom (1 : ℂ) := by
  rw [coMetric_apply_one, contrMetric_apply_one]
  rw [coMetricVal_expand_tmul, contrMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub]
  simp [← Representation.IntertwiningMap.toLinearMap_apply]
  repeat erw [coContrContraction_basis']
  simp only [Fin.isValue, ↓reduceIte, one_smul, reduceCtorEq, Sum.inr.injEq, one_ne_zero,
    Fin.reduceEq, zero_ne_one]
  erw [contrCoUnit_apply_one, contrCoUnitVal_expand_tmul]
  module

end Lorentz
end
