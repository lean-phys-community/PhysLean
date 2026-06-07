/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Units.Pre
/-!

# Metric for real Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix MatrixGroups Complex TensorProduct CategoryTheory.MonoidalCategory

namespace Lorentz
open scoped TensorProduct

/-- The metric `ηᵃᵃ` as an element of `(Contr d ⊗ Contr d).V`. -/
def preContrMetricVal (d : ℕ := 3) : ContrMod d ⊗[ℝ] ContrMod d :=
  contrContrToMatrixRe.symm ((@minkowskiMatrix d))

/-- Expansion of `preContrMetricVal` into basis. -/
lemma preContrMetricVal_expand_tmul {d : ℕ} : preContrMetricVal d =
    contrBasis d (Sum.inl 0) ⊗ₜ[ℝ] contrBasis d (Sum.inl 0) -
    ∑ i, contrBasis d (Sum.inr i) ⊗ₜ[ℝ] contrBasis d (Sum.inr i) := by
  simp only [preContrMetricVal, Fin.isValue]
  rw [contrContrToMatrixRe_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, ne_eq, reduceCtorEq, not_false_eq_true,
    minkowskiMatrix.off_diag_zero, zero_smul, Finset.sum_const_zero, add_zero,
    minkowskiMatrix.inl_0_inl_0, one_smul, zero_add, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr
  funext x
  rw [Finset.sum_eq_single x,]
  · simp [minkowskiMatrix.inr_i_inr_i]
  · simp only [Finset.mem_univ, ne_eq, smul_eq_zero, forall_const]
    intro b hb
    left
    refine minkowskiMatrix.off_diag_zero ?_
    simp only [ne_eq, Sum.inr.injEq]
    exact fun a => hb (id (Eq.symm a))
  · simp

lemma preContrMetricVal_expand_tmul_minkowskiMatrix {d : ℕ} : preContrMetricVal d =
    ∑ i, (minkowskiMatrix i i) • (contrBasis d i ⊗ₜ[ℝ] contrBasis d i) := by
  rw [preContrMetricVal_expand_tmul]
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, minkowskiMatrix.inl_0_inl_0, one_smul,
    minkowskiMatrix.inr_i_inr_i, neg_smul, Finset.sum_neg_distrib]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- The metric `ηᵃᵃ` as a morphism `𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ Contr d ⊗ Contr d`,
  making its invariance under the action of `LorentzGroup d`. -/
def preContrMetric (d : ℕ := 3) :
    (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((ContrMod.rep).tprod (ContrMod.rep)) where
  toFun := fun a => a • (preContrMetricVal d)
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • (preContrMetricVal d) =
      (TensorProduct.map ((Contr d).ρ M) ((Contr d).ρ M)) (x • (preContrMetricVal d))
    simp only [map_smul]
    apply congrArg
    simp only [preContrMetricVal]
    conv_rhs =>
      rw [contrContrToMatrixRe_ρ_symm]
    apply congrArg
    simp

lemma preContrMetric_apply_one {d : ℕ} : (preContrMetric d) (1 : ℝ) = preContrMetricVal d:= by
  change (1 : ℝ) • preContrMetricVal d = preContrMetricVal d
  rw [one_smul]

/-- The metric `ηᵢᵢ` as an element of `(Co d ⊗ Co d).V`. -/
def preCoMetricVal (d : ℕ := 3) : (Co d ⊗ Co d).V :=
  coCoToMatrixRe.symm ((@minkowskiMatrix d))

/-- Expansion of `preContrMetricVal` into basis. -/
lemma preCoMetricVal_expand_tmul {d : ℕ} : preCoMetricVal d =
    coBasis d (Sum.inl 0) ⊗ₜ[ℝ] coBasis d (Sum.inl 0) -
    ∑ i, coBasis d (Sum.inr i) ⊗ₜ[ℝ] coBasis d (Sum.inr i) := by
  simp only [preCoMetricVal, Fin.isValue]
  rw [coCoToMatrixRe_symm_expand_tmul]
  simp [minkowskiMatrix.inl_0_inl_0]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr
  funext x
  rw [Finset.sum_eq_single x]
  · simp [minkowskiMatrix.inr_i_inr_i]
  · simp only [Finset.mem_univ, ne_eq, smul_eq_zero, forall_const]
    intro b hb
    left
    refine minkowskiMatrix.off_diag_zero ?_
    simp only [ne_eq, Sum.inr.injEq]
    exact fun a => hb (id (Eq.symm a))
  · simp

lemma preCoMetricVal_expand_tmul_minkowskiMatrix {d : ℕ} : preCoMetricVal d =
    ∑ i, (minkowskiMatrix i i) • (coBasis d i ⊗ₜ[ℝ] coBasis d i) := by
  rw [preCoMetricVal_expand_tmul]
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, minkowskiMatrix.inl_0_inl_0, one_smul,
    minkowskiMatrix.inr_i_inr_i, neg_smul, Finset.sum_neg_distrib]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- The metric `ηᵢᵢ` as a morphism `𝟙_ (Rep ℂ (LorentzGroup d))) ⟶ Co d ⊗ Co d`,
  making its invariance under the action of `LorentzGroup d`. -/
def preCoMetric (d : ℕ := 3) : (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((CoMod.rep).tprod (CoMod.rep)) where
  toFun := fun a => a • preCoMetricVal d
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • preCoMetricVal d =
      (TensorProduct.map ((Co d).ρ M) ((Co d).ρ M)) (x • preCoMetricVal d)
    simp only [_root_.map_smul]
    apply congrArg
    simp only [preCoMetricVal]
    rw [coCoToMatrixRe_ρ_symm]
    apply congrArg
    rw [← LorentzGroup.coe_inv, LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]

lemma preCoMetric_apply_one {d : ℕ} : (preCoMetric d) (1 : ℝ) = preCoMetricVal d := by
  change (1 : ℝ) • preCoMetricVal d = preCoMetricVal d
  rw [one_smul]

/-!

## Contraction of metrics

-/

open minkowskiMatrix in
lemma contrCoContract_apply_metric {d : ℕ} :
    (TensorProduct.comm ℝ _ _ <|
      (TensorProduct.lid ℝ _).lTensor _ <|
      (contrCoContract.toLinearMap.rTensor (CoMod d)).lTensor (ContrMod d) <|
      (TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (CoMod d)).symm.toLinearMap.lTensor
        (ContrMod d) <|
      TensorProduct.assoc ℝ (ContrMod d) (ContrMod d) ((CoMod d) ⊗[ℝ] (CoMod d)) <|
      (preContrMetric d 1) ⊗ₜ[ℝ] (preCoMetric d 1)) = preCoContrUnit d (1 : ℝ) := by
  calc _
    _ = (TensorProduct.comm ℝ _ _ <|
      (TensorProduct.lid ℝ _).lTensor _ <|
      (contrCoContract.toLinearMap.rTensor (CoMod d)).lTensor (ContrMod d) <|
      (TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (CoMod d)).symm.toLinearMap.lTensor
        (ContrMod d) <|
      TensorProduct.assoc ℝ (ContrMod d) (ContrMod d) ((CoMod d) ⊗[ℝ] (CoMod d)) <|
      ∑ i, ∑ j, ((η i i * η j j) •
      ((contrBasis d i ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] (coBasis d j ⊗ₜ[ℝ] coBasis d j)))) := by
        congr
        rw [preContrMetric_apply_one, preCoMetric_apply_one,
          preContrMetricVal_expand_tmul_minkowskiMatrix, preCoMetricVal_expand_tmul_minkowskiMatrix]
        simp [tmul_sum, sum_tmul, - Fintype.sum_sum_type, Finset.smul_sum]
        rw [Finset.sum_comm]
        congr 1
        funext x
        congr 1
        funext y
        simp [smul_tmul, smul_smul]
        rw [mul_comm]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
        (contrBasis d i ⊗ₜ[ℝ] (contrCoContract (contrBasis d i ⊗ₜ[ℝ] coBasis d j)
          ⊗ₜ[ℝ] coBasis d j))) := by
        congr
        simp only [map_sum, map_smul]
        rfl
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
          ∑ i, contrBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] coBasis d i)) := by
        congr
        funext x
        rw [Finset.sum_eq_single x]
        · simp only [minkowskiMatrix.η_apply_mul_η_apply_diag, one_smul]
          rw [contrCoContract_basis]
          simp
        · intro b _ hb
          rw [contrCoContract_basis]
          rw [if_neg]
          · simp
          · exact id (Ne.symm hb)
        · simp
    _ = (TensorProduct.comm ℝ _ _ <| ∑ i, contrBasis d i ⊗ₜ[ℝ] coBasis d i) := by
        congr
        simp only [map_sum]
        simp
  rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
  simp

open minkowskiMatrix in
lemma coContrContract_apply_metric {d : ℕ} :
    (TensorProduct.comm ℝ _ _ <|
    (TensorProduct.lid ℝ _).lTensor _ <|
    (coContrContract.toLinearMap.rTensor (ContrMod d)).lTensor (CoMod d) <|
    (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (ContrMod d)).symm.toLinearMap.lTensor
      (CoMod d) <|
    TensorProduct.assoc ℝ (CoMod d) (CoMod d) ((ContrMod d) ⊗[ℝ] (ContrMod d)) <|
    (preCoMetric d 1) ⊗ₜ[ℝ] (preContrMetric d 1)) = preContrCoUnit d (1 : ℝ) := by
  calc _
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      (coContrContract.toLinearMap.rTensor (ContrMod d)).lTensor (CoMod d) <|
      (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (ContrMod d)).symm.toLinearMap.lTensor
        (CoMod d) <|
      TensorProduct.assoc ℝ (CoMod d) (CoMod d) ((ContrMod d) ⊗[ℝ] (ContrMod d)) <|
      ∑ i, ∑ j, ((η i i * η j j) •
      ((coBasis d i ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] (contrBasis d j ⊗ₜ[ℝ] contrBasis d j)))) := by
        congr
        rw [preCoMetric_apply_one, preContrMetric_apply_one,
          preCoMetricVal_expand_tmul_minkowskiMatrix,
          preContrMetricVal_expand_tmul_minkowskiMatrix]
        simp [tmul_sum, sum_tmul, - Fintype.sum_sum_type, Finset.smul_sum]
        rw [Finset.sum_comm]
        congr 1
        funext x
        congr 1
        funext y
        simp [smul_tmul, smul_smul]
        rw [mul_comm]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
        (coBasis d i ⊗ₜ[ℝ] (coContrContract (coBasis d i ⊗ₜ[ℝ] contrBasis d j)
          ⊗ₜ[ℝ] contrBasis d j))) := by
        congr
        simp only [map_sum, map_smul]
        rfl
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
          ∑ i, coBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] contrBasis d i)) := by
        congr
        funext x
        rw [Finset.sum_eq_single x]
        · simp only [minkowskiMatrix.η_apply_mul_η_apply_diag, one_smul]
          rw [coContrContract_basis]
          simp
        · intro b _ hb
          rw [coContrContract_basis]
          rw [if_neg]
          · simp
          · exact id (Ne.symm hb)
        · simp
    _ = (TensorProduct.comm ℝ _ _ <| ∑ i, coBasis d i ⊗ₜ[ℝ] contrBasis d i) := by
        congr
        simp only [map_sum]
        simp
  rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
  simp

end Lorentz
end
