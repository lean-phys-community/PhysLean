/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Basic
/-!

# Tensor product of two Weyl fermion

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-!

## Equivalences to matrices.

-/

/-- Equivalence of `leftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def leftLeftToMatrix : (LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis leftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftLeftToMatrix` in terms of the standard basis. -/
lemma leftLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] leftBasis j) := by
  simp only [leftLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply leftBasis leftBasis i j)
  · simp

/-- Equivalence of `dualLeftHanded ⊗ dualLeftHanded` to `2 x 2` complex matrices. -/
def dualLeftdualLeftToMatrix : (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct dualLeftBasis dualLeftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `dualLeftdualLeftToMatrix` in terms of the standard basis. -/
lemma dualLeftdualLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualLeftdualLeftToMatrix.symm M = ∑ i, ∑ j, M i j •
      (dualLeftBasis i ⊗ₜ[ℂ] dualLeftBasis j) := by
  simp only [dualLeftdualLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply dualLeftBasis dualLeftBasis i j)
  · simp

/-- Equivalence of `leftHanded ⊗ dualLeftHanded` to `2 x 2` complex matrices. -/
def leftDualLeftToMatrix : (LeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis dualLeftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftDualLeftToMatrix` in terms of the standard basis. -/
lemma leftDualLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftDualLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] dualLeftBasis j) := by
  simp only [leftDualLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply leftBasis dualLeftBasis i j)
  · simp

/-- Equivalence of `dualLeftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def dualLeftLeftToMatrix : (DualLeftHandedWeyl ⊗[ℂ] LeftHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct dualLeftBasis leftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `dualLeftLeftToMatrix` in terms of the standard basis. -/
lemma dualLeftLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualLeftLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (dualLeftBasis i ⊗ₜ[ℂ] leftBasis j) := by
  simp only [dualLeftLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply dualLeftBasis leftBasis i j)
  · simp

/-- Equivalence of `rightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def rightRightToMatrix : (RightHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct rightBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `rightRightToMatrix` in terms of the standard basis. -/
lemma rightRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rightRightToMatrix.symm M = ∑ i, ∑ j, M i j • (rightBasis i ⊗ₜ[ℂ] rightBasis j) := by
  simp only [rightRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply rightBasis rightBasis i j)
  · simp

/-- Equivalence of `dualRightHanded ⊗ dualRightHanded` to `2 x 2` complex matrices. -/
def dualRightDualRightToMatrix : (DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct dualRightBasis dualRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `dualRightDualRightToMatrix` in terms of the standard basis. -/
lemma dualRightDualRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualRightDualRightToMatrix.symm M =
    ∑ i, ∑ j, M i j • (dualRightBasis i ⊗ₜ[ℂ] dualRightBasis j) := by
  simp only [dualRightDualRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply dualRightBasis dualRightBasis i j)
  · simp

/-- Equivalence of `rightHanded ⊗ dualRightHanded` to `2 x 2` complex matrices. -/
def rightDualRightToMatrix : (RightHandedWeyl ⊗[ℂ] DualRightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct rightBasis dualRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `rightDualRightToMatrix` in terms of the standard basis. -/
lemma rightDualRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rightDualRightToMatrix.symm M = ∑ i, ∑ j, M i j • (rightBasis i ⊗ₜ[ℂ] dualRightBasis j) := by
  simp only [rightDualRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply rightBasis dualRightBasis i j)
  · simp

/-- Equivalence of `dualRightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def dualRightRightToMatrix : (DualRightHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct dualRightBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `dualRightRightToMatrix` in terms of the standard basis. -/
lemma dualRightRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualRightRightToMatrix.symm M = ∑ i, ∑ j, M i j • (dualRightBasis i ⊗ₜ[ℂ] rightBasis j) := by
  simp only [dualRightRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply dualRightBasis rightBasis i j)
  · simp

/-- Equivalence of `dualLeftHanded ⊗ dualRightHanded` to `2 x 2` complex matrices. -/
def dualLeftDualRightToMatrix : (DualLeftHandedWeyl ⊗[ℂ] DualRightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct dualLeftBasis dualRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `dualLeftDualRightToMatrix` in terms of the standard basis. -/
lemma dualLeftDualRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualLeftDualRightToMatrix.symm M = ∑ i, ∑ j, M i j •
      (dualLeftBasis i ⊗ₜ[ℂ] dualRightBasis j) := by
  simp only [dualLeftDualRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply dualLeftBasis dualRightBasis i j)
  · simp

/-- Equivalence of `leftHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def leftRightToMatrix : (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftRightToMatrix` in terms of the standard basis. -/
lemma leftRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftRightToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] rightBasis j) := by
  simp only [leftRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply leftBasis rightBasis i j)
  · simp

/-!

## Group actions

-/

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ leftHanded` is equivalent to
  `M.1 * leftLeftToMatrix v * (M.1)ᵀ`. -/
lemma leftLeftToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl)) (M : SL(2,ℂ)) :
    leftLeftToMatrix (TensorProduct.map (leftHandedRep M) (leftHandedRep M) v) =
    M.1 * leftLeftToMatrix v * (M.1)ᵀ := by
  nth_rewrite 1 [leftLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (leftBasis.tensorProduct leftBasis) (leftBasis.tensorProduct leftBasis)
      (TensorProduct.map (leftHandedRep M) (leftHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((leftBasis.tensorProduct leftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (leftBasis.tensorProduct leftBasis)
      (leftBasis.tensorProduct leftBasis) (TensorProduct.map (leftHandedRep M) (leftHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M))
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M)) (i, j) k)
        * leftLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ j : Fin 2, M.1 i j * leftLeftToMatrix v j x) * M.1 j x
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftLeftToMatrix v x1 x) * M.1 j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [leftBasis_ρ_apply]
  rw [mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualLeftHanded ⊗ dualLeftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftLeftToMatrix v * (M.1⁻¹)`. -/
lemma dualLeftdualLeftToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl)) (M : SL(2,ℂ)) :
    dualLeftdualLeftToMatrix (TensorProduct.map (dualLeftHandedRep M) (dualLeftHandedRep M) v) =
    (M.1⁻¹)ᵀ * dualLeftdualLeftToMatrix v * (M.1⁻¹) := by
  nth_rewrite 1 [dualLeftdualLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (dualLeftBasis.tensorProduct dualLeftBasis) (dualLeftBasis.tensorProduct dualLeftBasis)
      (TensorProduct.map (dualLeftHandedRep M) (dualLeftHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((dualLeftBasis.tensorProduct dualLeftBasis).repr v)))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (dualLeftBasis.tensorProduct dualLeftBasis)
      (dualLeftBasis.tensorProduct dualLeftBasis)
      (TensorProduct.map (dualLeftHandedRep M) (dualLeftHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M))
        ((LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M)) (i, j) k)
        * dualLeftdualLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i *
    dualLeftdualLeftToMatrix v x1 x) * (M.1)⁻¹ x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, ((M.1)⁻¹ x1 i *
    dualLeftdualLeftToMatrix v x1 x) * (M.1)⁻¹ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [dualLeftBasis_ρ_apply, transpose_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ dualLeftHanded` is equivalent to
  `M.1 * leftDualLeftToMatrix v * (M.1⁻¹)`. -/
lemma leftDualLeftToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl)) (M : SL(2,ℂ)) :
    leftDualLeftToMatrix (TensorProduct.map (leftHandedRep M) (dualLeftHandedRep M) v) =
    M.1 * leftDualLeftToMatrix v * (M.1⁻¹) := by
  nth_rewrite 1 [leftDualLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (leftBasis.tensorProduct dualLeftBasis) (leftBasis.tensorProduct dualLeftBasis)
      (TensorProduct.map (leftHandedRep M) (dualLeftHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((leftBasis.tensorProduct dualLeftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (leftBasis.tensorProduct dualLeftBasis)
      (leftBasis.tensorProduct dualLeftBasis)
      (TensorProduct.map (leftHandedRep M) (dualLeftHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M))
        ((LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M)) (i, j) k)
        * leftDualLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, M.1 i x1 * leftDualLeftToMatrix v x1 x) * (M.1⁻¹) x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftDualLeftToMatrix v x1 x) * (M.1⁻¹) x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [leftBasis_ρ_apply, dualLeftBasis_ρ_apply, transpose_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualLeftHanded ⊗ leftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftDualLeftToMatrix v * (M.1)ᵀ`. -/
lemma dualLeftLeftToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] LeftHandedWeyl)) (M : SL(2,ℂ)) :
    dualLeftLeftToMatrix (TensorProduct.map (dualLeftHandedRep M) (leftHandedRep M) v) =
    (M.1⁻¹)ᵀ * dualLeftLeftToMatrix v * (M.1)ᵀ := by
  nth_rewrite 1 [dualLeftLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (dualLeftBasis.tensorProduct leftBasis) (dualLeftBasis.tensorProduct leftBasis)
      (TensorProduct.map (dualLeftHandedRep M) (leftHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((dualLeftBasis.tensorProduct leftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (dualLeftBasis.tensorProduct leftBasis)
      (dualLeftBasis.tensorProduct leftBasis)
      (TensorProduct.map (dualLeftHandedRep M) (leftHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M))
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M)) (i, j) k)
        * dualLeftLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * dualLeftLeftToMatrix v x1 x) * M.1 j x
    = ∑ x : Fin 2, ∑ x1 : Fin 2, ((M.1)⁻¹ x1 i * dualLeftLeftToMatrix v x1 x) * M.1 j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [dualLeftBasis_ρ_apply, transpose_apply, leftBasis_ρ_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ rightHanded` is equivalent to
  `(M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ`. -/
lemma rightRightToMatrix_ρ (v : (RightHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    rightRightToMatrix (TensorProduct.map (rightHandedRep M) (rightHandedRep M) v) =
    (M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ := by
  nth_rewrite 1 [rightRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (rightBasis.tensorProduct rightBasis) (rightBasis.tensorProduct rightBasis)
      (TensorProduct.map (rightHandedRep M) (rightHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((rightBasis.tensorProduct rightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (rightBasis.tensorProduct rightBasis)
      (rightBasis.tensorProduct rightBasis)
      (TensorProduct.map (rightHandedRep M) (rightHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M))
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M)) (i, j) k)
        * rightRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1.map star) i x1 * rightRightToMatrix v x1 x) *
      (M.1.map star) j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1.map star) i x1 * rightRightToMatrix v x1 x) * (M.1.map star) j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [rightBasis_ρ_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualRightHanded ⊗ dualRightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma dualRightDualRightToMatrix_ρ (v : (DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl))
    (M : SL(2,ℂ)) :
    dualRightDualRightToMatrix (TensorProduct.map (dualRightHandedRep M) (dualRightHandedRep M) v) =
    ((M.1⁻¹).conjTranspose) * dualRightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  nth_rewrite 1 [dualRightDualRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (dualRightBasis.tensorProduct dualRightBasis) (dualRightBasis.tensorProduct dualRightBasis)
      (TensorProduct.map (dualRightHandedRep M) (dualRightHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((dualRightBasis.tensorProduct dualRightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (dualRightBasis.tensorProduct dualRightBasis)
      (dualRightBasis.tensorProduct dualRightBasis)
      (TensorProduct.map (dualRightHandedRep M) (dualRightHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M))
        ((LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M)) (i, j) k)
        * dualRightDualRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (↑M)⁻¹ᴴ i x1 * dualRightDualRightToMatrix v x1 x) *
      (↑M)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((↑M)⁻¹ᴴ i x1 * dualRightDualRightToMatrix v x1 x) * (↑M)⁻¹ᴴ j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [dualRightBasis_ρ_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ dualRightHanded` is equivalent to
  `(M.1.map star) * rightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma rightDualRightToMatrix_ρ (v : (RightHandedWeyl ⊗[ℂ] DualRightHandedWeyl)) (M : SL(2,ℂ)) :
    rightDualRightToMatrix (TensorProduct.map (rightHandedRep M) (dualRightHandedRep M) v) =
    (M.1.map star) * rightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  nth_rewrite 1 [rightDualRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (rightBasis.tensorProduct dualRightBasis) (rightBasis.tensorProduct dualRightBasis)
      (TensorProduct.map (rightHandedRep M) (dualRightHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((rightBasis.tensorProduct dualRightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (rightBasis.tensorProduct dualRightBasis)
    (rightBasis.tensorProduct dualRightBasis)
    (TensorProduct.map (rightHandedRep M) (dualRightHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M))
        ((LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M)) (i, j) k)
        * rightDualRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1.map star) i x1 * rightDualRightToMatrix v x1 x)
      * (↑M)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1.map star) i x1 * rightDualRightToMatrix v x1 x) * (↑M)⁻¹ᴴ j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [rightBasis_ρ_apply, dualRightBasis_ρ_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualRightHanded ⊗ rightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightDualRightToMatrix v * ((M.1.map star)).ᵀ`. -/
lemma dualRightRightToMatrix_ρ (v : (DualRightHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    dualRightRightToMatrix (TensorProduct.map (dualRightHandedRep M) (rightHandedRep M) v) =
    ((M.1⁻¹).conjTranspose) * dualRightRightToMatrix v * (M.1.map star)ᵀ := by
  nth_rewrite 1 [dualRightRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (dualRightBasis.tensorProduct rightBasis) (dualRightBasis.tensorProduct rightBasis)
      (TensorProduct.map (dualRightHandedRep M) (rightHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((dualRightBasis.tensorProduct rightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (dualRightBasis.tensorProduct rightBasis)
      (dualRightBasis.tensorProduct rightBasis)
      (TensorProduct.map (dualRightHandedRep M) (rightHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M))
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M)) (i, j) k)
        * dualRightRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2,
      (↑M)⁻¹ᴴ i x1 * dualRightRightToMatrix v x1 x) * (M.1.map star) j x
      = ∑ x : Fin 2, ∑ x1 : Fin 2, ((↑M)⁻¹ᴴ i x1 * dualRightRightToMatrix v x1 x) *
      (M.1.map star) j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [dualRightBasis_ρ_apply, rightBasis_ρ_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma dualLeftDualRightToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] DualRightHandedWeyl))
    (M : SL(2,ℂ)) :
    dualLeftDualRightToMatrix (TensorProduct.map (dualLeftHandedRep M) (dualRightHandedRep M) v) =
    (M.1⁻¹)ᵀ * dualLeftDualRightToMatrix v * ((M.1⁻¹).conjTranspose)ᵀ := by
  nth_rewrite 1 [dualLeftDualRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (dualLeftBasis.tensorProduct dualRightBasis) (dualLeftBasis.tensorProduct dualRightBasis)
      (TensorProduct.map (dualLeftHandedRep M) (dualRightHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((dualLeftBasis.tensorProduct dualRightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (dualLeftBasis.tensorProduct dualRightBasis)
      (dualLeftBasis.tensorProduct dualRightBasis)
      (TensorProduct.map (dualLeftHandedRep M) (dualRightHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M))
        ((LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M)) (i, j) k)
        * dualLeftDualRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * dualLeftDualRightToMatrix v x1 x) *
      (M.1)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1)⁻¹ x1 i * dualLeftDualRightToMatrix v x1 x) * (M.1)⁻¹ᴴ j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [dualLeftBasis_ρ_apply, transpose_apply, dualRightBasis_ρ_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma leftRightToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    leftRightToMatrix (TensorProduct.map (leftHandedRep M) (rightHandedRep M) v) =
    M.1 * leftRightToMatrix v * (M.1)ᴴ := by
  nth_rewrite 1 [leftRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (leftBasis.tensorProduct rightBasis) (leftBasis.tensorProduct rightBasis)
      (TensorProduct.map (leftHandedRep M) (rightHandedRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((leftBasis.tensorProduct rightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (leftBasis.tensorProduct rightBasis)
      (leftBasis.tensorProduct rightBasis)
      (TensorProduct.map (leftHandedRep M) (rightHandedRep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M))
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M)) (i, j) k)
        * leftRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, M.1 i x1 * leftRightToMatrix v x1 x) * (M.1)ᴴ x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftRightToMatrix v x1 x) * (M.1)ᴴ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [leftBasis_ρ_apply, rightBasis_ρ_apply]
  rw [Matrix.conjTranspose]
  simp only [RCLike.star_def, map_apply, transpose_apply]
  ring

/-!

## The symm version of the group actions.

-/

lemma leftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHandedRep M) (leftHandedRep M) (leftLeftToMatrix.symm v) =
    leftLeftToMatrix.symm (M.1 * v * (M.1)ᵀ) := by
  have h1 := leftLeftToMatrix_ρ (leftLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma dualLeftdualLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualLeftHandedRep M) (dualLeftHandedRep M)
      (dualLeftdualLeftToMatrix.symm v) =
    dualLeftdualLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1⁻¹)) := by
  have h1 := dualLeftdualLeftToMatrix_ρ (dualLeftdualLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma leftDualLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHandedRep M) (dualLeftHandedRep M) (leftDualLeftToMatrix.symm v) =
    leftDualLeftToMatrix.symm (M.1 * v * (M.1⁻¹)) := by
  have h1 := leftDualLeftToMatrix_ρ (leftDualLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma dualLeftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualLeftHandedRep M) (leftHandedRep M) (dualLeftLeftToMatrix.symm v) =
    dualLeftLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1)ᵀ) := by
  have h1 := dualLeftLeftToMatrix_ρ (dualLeftLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma rightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (rightHandedRep M) (rightHandedRep M) (rightRightToMatrix.symm v) =
    rightRightToMatrix.symm ((M.1.map star) * v * ((M.1.map star))ᵀ) := by
  have h1 := rightRightToMatrix_ρ (rightRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma dualRightDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualRightHandedRep M) (dualRightHandedRep M)
      (dualRightDualRightToMatrix.symm v) =
    dualRightDualRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * ((M.1⁻¹).conjTranspose)ᵀ) := by
  have h1 := dualRightDualRightToMatrix_ρ (dualRightDualRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma rightDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (rightHandedRep M) (dualRightHandedRep M) (rightDualRightToMatrix.symm v) =
    rightDualRightToMatrix.symm ((M.1.map star) * v * (((M.1⁻¹).conjTranspose)ᵀ)) := by
  have h1 := rightDualRightToMatrix_ρ (rightDualRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma dualRightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualRightHandedRep M) (rightHandedRep M) (dualRightRightToMatrix.symm v) =
    dualRightRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * (M.1.map star)ᵀ) := by
  have h1 := dualRightRightToMatrix_ρ (dualRightRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma dualLeftDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualLeftHandedRep M) (dualRightHandedRep M)
      (dualLeftDualRightToMatrix.symm v) =
    dualLeftDualRightToMatrix.symm ((M.1⁻¹)ᵀ * v * ((M.1⁻¹).conjTranspose)ᵀ) := by
  have h1 := dualLeftDualRightToMatrix_ρ (dualLeftDualRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma leftRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHandedRep M) (rightHandedRep M) (leftRightToMatrix.symm v) =
    leftRightToMatrix.symm (M.1 * v * (M.1)ᴴ) := by
  have h1 := leftRightToMatrix_ρ (leftRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

open Lorentz

lemma dualLeftDualRightToMatrix_ρ_symm_selfAdjoint (v : Matrix (Fin 2) (Fin 2) ℂ)
    (hv : IsSelfAdjoint v) (M : SL(2,ℂ)) :
    TensorProduct.map (dualLeftHandedRep M) (dualRightHandedRep M)
      (dualLeftDualRightToMatrix.symm v) =
    dualLeftDualRightToMatrix.symm (SL2C.toSelfAdjointMap (M.transpose⁻¹) ⟨v, hv⟩) := by
  rw [dualLeftDualRightToMatrix_ρ_symm]
  apply congrArg
  simp only [SL2C.toSelfAdjointMap_apply_coe, SpecialLinearGroup.coe_inv,
    SpecialLinearGroup.coe_transpose]
  congr 1
  · rw [SL2C.inverse_coe]
    simp only [SpecialLinearGroup.coe_inv]
    rw [@adjugate_transpose]
  · rw [SL2C.inverse_coe]
    simp only [SpecialLinearGroup.coe_inv]
    rw [← @adjugate_transpose]
    rfl

lemma leftRightToMatrix_ρ_symm_selfAdjoint (v : Matrix (Fin 2) (Fin 2) ℂ)
    (hv : IsSelfAdjoint v) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHandedRep M) (rightHandedRep M) (leftRightToMatrix.symm v) =
    leftRightToMatrix.symm (SL2C.toSelfAdjointMap M ⟨v, hv⟩) := by
  rw [leftRightToMatrix_ρ_symm]
  rfl

end
end Fermion
