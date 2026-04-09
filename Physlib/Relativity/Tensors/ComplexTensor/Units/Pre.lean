/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Matrix.Pre
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Contraction
/-!

# Unit for complex Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory
namespace Lorentz

/-- The contra-co unit for complex lorentz vectors. Usually denoted `δⁱᵢ`. -/
def contrCoUnitVal : (complexContr ⊗ complexCo).V :=
  contrCoToMatrix.symm 1

/-- Expansion of `contrCoUnitVal` into basis. -/
lemma contrCoUnitVal_expand_tmul : contrCoUnitVal =
    complexContrBasis (Sum.inl 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inl 0)
    + complexContrBasis (Sum.inr 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 0)
    + complexContrBasis (Sum.inr 1) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 1)
    + complexContrBasis (Sum.inr 2) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 2) := by
  simp only [contrCoUnitVal, Fin.isValue]
  erw [contrCoToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

lemma contrCoUnitVal_eq_sum_tmul : contrCoUnitVal =
    ∑ i, complexContrBasis i ⊗ₜ[ℂ] complexCoBasis i := by
  simp [contrCoUnitVal_expand_tmul, Fin.isValue, Fin.sum_univ_three]
  module

set_option backward.isDefEq.respectTransparency false in
/-- The contra-co unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexCo`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def contrCoUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexCo := Rep.ofHom
{
    toFun := fun a =>
      let a' : ℂ := a
      a' • contrCoUnitVal,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • contrCoUnitVal =
        (TensorProduct.map (complexContr.ρ M) (complexCo.ρ M)) (x • contrCoUnitVal)
      simp only [map_smul]
      apply congrArg
      simp only [contrCoUnitVal]
      rw [contrCoToMatrix_ρ_symm]
      apply congrArg
      simp
}

lemma contrCoUnit_apply_one : contrCoUnit.hom (1 : ℂ) = contrCoUnitVal := by
  change (1 : ℂ) • contrCoUnitVal = contrCoUnitVal
  rw [one_smul]

/-- The co-contra unit for complex lorentz vectors. Usually denoted `δᵢⁱ`. -/
def coContrUnitVal : (complexCo ⊗ complexContr).V :=
  coContrToMatrix.symm 1

/-- Expansion of `coContrUnitVal` into basis. -/
lemma coContrUnitVal_expand_tmul : coContrUnitVal =
    complexCoBasis (Sum.inl 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inl 0)
    + complexCoBasis (Sum.inr 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 0)
    + complexCoBasis (Sum.inr 1) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 1)
    + complexCoBasis (Sum.inr 2) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 2) := by
  simp only [coContrUnitVal, Fin.isValue]
  rw [coContrToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

lemma coContrUnitVal_eq_sum_tmul : coContrUnitVal =
    ∑ i, complexCoBasis i ⊗ₜ[ℂ] complexContrBasis i := by
  simp [coContrUnitVal_expand_tmul, Fin.isValue, Fin.sum_univ_three]
  module

set_option backward.isDefEq.respectTransparency false in
/-- The co-contra unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexContr`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def coContrUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexContr := Rep.ofHom {
    toFun := fun a =>
      let a' : ℂ := a
      a' • coContrUnitVal,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • coContrUnitVal =
        (TensorProduct.map (complexCo.ρ M) (complexContr.ρ M)) (x • coContrUnitVal)
      simp only [map_smul]
      apply congrArg
      simp only [coContrUnitVal]
      rw [coContrToMatrix_ρ_symm]
      apply congrArg
      symm
      refine transpose_eq_one.mp ?h.h.h.a
      simp
}

lemma coContrUnit_apply_one : coContrUnit.hom (1 : ℂ) = coContrUnitVal := by
  change (1 : ℂ) • coContrUnitVal = coContrUnitVal
  rw [one_smul]

/-!

## Contraction of the units

-/

set_option backward.isDefEq.respectTransparency false in
/-- Contraction on the right with `contrCoUnit` does nothing. -/
lemma contr_contrCoUnit (x : complexCo) :
    (λ_ complexCo).hom.hom
    ((coContrContraction ▷ complexCo).hom
    ((α_ _ _ complexCo).inv.hom
    (x ⊗ₜ[ℂ] contrCoUnit.hom (1 : ℂ)))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span complexCoBasis x)
  subst hc
  rw [contrCoUnit_apply_one, contrCoUnitVal_eq_sum_tmul]
  simp [- Fintype.sum_sum_type, tmul_sum, sum_tmul, map_sum, Representation.TensorProduct.assoc,
    ← Representation.IntertwiningMap.toLinearMap_apply, smul_tmul]
  conv_lhs =>
    enter [2,x, 2, y]
    erw [coContrContraction_basis']
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Contraction on the right with `coContrUnit`. -/
lemma contr_coContrUnit (x : complexContr) :
    (λ_ complexContr).hom.hom
    ((contrCoContraction ▷ complexContr).hom
    ((α_ _ _ complexContr).inv.hom
    (x ⊗ₜ[ℂ] coContrUnit.hom (1 : ℂ)))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span complexContrBasis x)
  subst hc
  rw [coContrUnit_apply_one, coContrUnitVal_eq_sum_tmul]
  simp [- Fintype.sum_sum_type, tmul_sum, sum_tmul, map_sum, Representation.TensorProduct.assoc,
    ← Representation.IntertwiningMap.toLinearMap_apply, smul_tmul]
  conv_lhs =>
    enter [2,x, 2, y]
    erw [contrCoContraction_basis']
  simp

/-!

## Symmetry properties of the units

-/

open CategoryTheory

lemma contrCoUnit_symm :
    (contrCoUnit.hom (1 : ℂ)) = (complexContr ◁ 𝟙 _).hom ((β_ complexCo complexContr).hom.hom
    (coContrUnit.hom (1 : ℂ))) := by
  rw [contrCoUnit_apply_one, contrCoUnitVal_expand_tmul]
  rw [coContrUnit_apply_one, coContrUnitVal_expand_tmul]
  rfl

lemma coContrUnit_symm :
    (coContrUnit.hom (1 : ℂ)) = (complexCo ◁ 𝟙 _).hom ((β_ complexContr complexCo).hom.hom
    (contrCoUnit.hom (1 : ℂ))) := by
  rw [coContrUnit_apply_one, coContrUnitVal_expand_tmul]
  rw [contrCoUnit_apply_one, contrCoUnitVal_expand_tmul]
  rfl

end Lorentz
end
