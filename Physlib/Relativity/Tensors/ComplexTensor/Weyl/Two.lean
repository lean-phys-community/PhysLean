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

/-- Expanding the inverse of the canonical equivalence from a tensor product of two
based modules to matrices, in terms of the standard basis tensors. Every `*ToMatrix`
below is definitionally this composition, so each `*ToMatrix_symm_expand_tmul` lemma
is a direct specialization. -/
lemma tensorBasis_toMatrix_symm_expand
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (b₁ : Basis ι₁ ℂ V₁) (b₂ : Basis ι₂ ℂ V₂) (M : Matrix ι₁ ι₂ ℂ) :
    ((Basis.tensorProduct b₁ b₂).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℂ ℂ (ι₁ × ι₂) ≪≫ₗ
      LinearEquiv.curry ℂ ℂ ι₁ ι₂).symm M =
    ∑ i, ∑ j, M i j • (b₁ i ⊗ₜ[ℂ] b₂ j) := by
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply, Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply b₁ b₂ i j)
  · simp

/-- Equivalence of `leftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def leftLeftToMatrix : (LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis leftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftLeftToMatrix` in terms of the standard basis. -/
lemma leftLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] leftBasis j) := by
  exact tensorBasis_toMatrix_symm_expand leftBasis leftBasis M

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
  exact tensorBasis_toMatrix_symm_expand dualLeftBasis dualLeftBasis M

/-- Equivalence of `leftHanded ⊗ dualLeftHanded` to `2 x 2` complex matrices. -/
def leftDualLeftToMatrix : (LeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis dualLeftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftDualLeftToMatrix` in terms of the standard basis. -/
lemma leftDualLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftDualLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] dualLeftBasis j) := by
  exact tensorBasis_toMatrix_symm_expand leftBasis dualLeftBasis M

/-- Equivalence of `dualLeftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def dualLeftLeftToMatrix : (DualLeftHandedWeyl ⊗[ℂ] LeftHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct dualLeftBasis leftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `dualLeftLeftToMatrix` in terms of the standard basis. -/
lemma dualLeftLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualLeftLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (dualLeftBasis i ⊗ₜ[ℂ] leftBasis j) := by
  exact tensorBasis_toMatrix_symm_expand dualLeftBasis leftBasis M

/-- Equivalence of `rightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def rightRightToMatrix : (RightHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct rightBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `rightRightToMatrix` in terms of the standard basis. -/
lemma rightRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rightRightToMatrix.symm M = ∑ i, ∑ j, M i j • (rightBasis i ⊗ₜ[ℂ] rightBasis j) := by
  exact tensorBasis_toMatrix_symm_expand rightBasis rightBasis M

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
  exact tensorBasis_toMatrix_symm_expand dualRightBasis dualRightBasis M

/-- Equivalence of `rightHanded ⊗ dualRightHanded` to `2 x 2` complex matrices. -/
def rightDualRightToMatrix : (RightHandedWeyl ⊗[ℂ] DualRightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct rightBasis dualRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `rightDualRightToMatrix` in terms of the standard basis. -/
lemma rightDualRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rightDualRightToMatrix.symm M = ∑ i, ∑ j, M i j • (rightBasis i ⊗ₜ[ℂ] dualRightBasis j) := by
  exact tensorBasis_toMatrix_symm_expand rightBasis dualRightBasis M

/-- Equivalence of `dualRightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def dualRightRightToMatrix : (DualRightHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct dualRightBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `dualRightRightToMatrix` in terms of the standard basis. -/
lemma dualRightRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualRightRightToMatrix.symm M = ∑ i, ∑ j, M i j • (dualRightBasis i ⊗ₜ[ℂ] rightBasis j) := by
  exact tensorBasis_toMatrix_symm_expand dualRightBasis rightBasis M

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
  exact tensorBasis_toMatrix_symm_expand dualLeftBasis dualRightBasis M

/-- Equivalence of `leftHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def leftRightToMatrix : (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftRightToMatrix` in terms of the standard basis. -/
lemma leftRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftRightToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] rightBasis j) := by
  exact tensorBasis_toMatrix_symm_expand leftBasis rightBasis M

/-!

## Group actions

-/

/-- Common core for the `*ToMatrix_ρ` lemmas: the `ToMatrix` equivalence intertwines
`TensorProduct.map f g` with conjugation by the matrices of `f` and `g`, where the
equivalence is the canonical triple composition built from the bases `b₁`, `b₂`. -/
private lemma tensorBasis_toMatrix_map
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (b₁ : Basis (Fin 2) ℂ V₁) (b₂ : Basis (Fin 2) ℂ V₂)
    (f : V₁ →ₗ[ℂ] V₁) (g : V₂ →ₗ[ℂ] V₂)
    (eqv : (V₁ ⊗[ℂ] V₂) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (heqv : eqv = (b₁.tensorProduct b₂).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
      LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2))
    (v : V₁ ⊗[ℂ] V₂) :
    eqv (TensorProduct.map f g v) =
    (LinearMap.toMatrix b₁ b₁ f) * eqv v * (LinearMap.toMatrix b₂ b₂ g)ᵀ := by
  have hpt : ∀ (w : V₁ ⊗[ℂ] V₂) (i j : Fin 2), eqv w i j =
      (((b₁.tensorProduct b₂).repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
        LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) w) i j := by
    intro w i j
    rw [heqv]
    rfl
  funext i j
  have key : eqv (TensorProduct.map f g v) i j =
      ((LinearMap.toMatrix (b₁.tensorProduct b₂) (b₁.tensorProduct b₂)
        (TensorProduct.map f g))
        *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
        ((b₁.tensorProduct b₂).repr v))) (i, j) := by
    rw [hpt (TensorProduct.map f g v) i j]
    simp only [LinearEquiv.trans_apply]
    have h1 := (LinearMap.toMatrix_mulVec_repr (b₁.tensorProduct b₂)
      (b₁.tensorProduct b₂) (TensorProduct.map f g) v)
    erw [h1]
    rfl
  rw [key, TensorProduct.toMatrix_map]
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix b₁ b₁) f)
        ((LinearMap.toMatrix b₂ b₂) g) (i, j) k)
        * (((b₁.tensorProduct b₂).repr ≪≫ₗ
          Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
          LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) v) k.1 k.2) = _
  simp_rw [← hpt v]
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x, (∑ x1, (LinearMap.toMatrix b₁ b₁) f i x1 * eqv v x1 x)
      * (LinearMap.toMatrix b₂ b₂) g j x
      = ∑ x, ∑ x1, ((LinearMap.toMatrix b₁ b₁) f i x1 * eqv v x1 x)
      * (LinearMap.toMatrix b₂ b₂) g j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ leftHanded` is equivalent to
  `M.1 * leftLeftToMatrix v * (M.1)ᵀ`. -/
lemma leftLeftToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl)) (M : SL(2,ℂ)) :
    leftLeftToMatrix (TensorProduct.map (leftHandedRep M) (leftHandedRep M) v) =
    M.1 * leftLeftToMatrix v * (M.1)ᵀ := by
  rw [tensorBasis_toMatrix_map leftBasis leftBasis (leftHandedRep M)
    (leftHandedRep M) leftLeftToMatrix rfl v]
  have h : (LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M) = M.1 := by
    ext i j
    simp
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualLeftHanded ⊗ dualLeftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftLeftToMatrix v * (M.1⁻¹)`. -/
lemma dualLeftdualLeftToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl)) (M : SL(2,ℂ)) :
    dualLeftdualLeftToMatrix (TensorProduct.map (dualLeftHandedRep M) (dualLeftHandedRep M) v) =
    (M.1⁻¹)ᵀ * dualLeftdualLeftToMatrix v * (M.1⁻¹) := by
  rw [tensorBasis_toMatrix_map dualLeftBasis dualLeftBasis (dualLeftHandedRep M)
    (dualLeftHandedRep M) dualLeftdualLeftToMatrix rfl v]
  have h : (LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M)
      = (M.1⁻¹)ᵀ := by
    ext i j
    simp
  rw [h, transpose_transpose]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ dualLeftHanded` is equivalent to
  `M.1 * leftDualLeftToMatrix v * (M.1⁻¹)`. -/
lemma leftDualLeftToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl)) (M : SL(2,ℂ)) :
    leftDualLeftToMatrix (TensorProduct.map (leftHandedRep M) (dualLeftHandedRep M) v) =
    M.1 * leftDualLeftToMatrix v * (M.1⁻¹) := by
  rw [tensorBasis_toMatrix_map leftBasis dualLeftBasis (leftHandedRep M)
    (dualLeftHandedRep M) leftDualLeftToMatrix rfl v]
  have h1 : (LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M) = M.1 := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M)
      = (M.1⁻¹)ᵀ := by
    ext i j
    simp
  rw [h1, h2, transpose_transpose]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualLeftHanded ⊗ leftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftDualLeftToMatrix v * (M.1)ᵀ`. -/
lemma dualLeftLeftToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] LeftHandedWeyl)) (M : SL(2,ℂ)) :
    dualLeftLeftToMatrix (TensorProduct.map (dualLeftHandedRep M) (leftHandedRep M) v) =
    (M.1⁻¹)ᵀ * dualLeftLeftToMatrix v * (M.1)ᵀ := by
  rw [tensorBasis_toMatrix_map dualLeftBasis leftBasis (dualLeftHandedRep M)
    (leftHandedRep M) dualLeftLeftToMatrix rfl v]
  have h1 : (LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M)
      = (M.1⁻¹)ᵀ := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M) = M.1 := by
    ext i j
    simp
  rw [h1, h2]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ rightHanded` is equivalent to
  `(M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ`. -/
lemma rightRightToMatrix_ρ (v : (RightHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    rightRightToMatrix (TensorProduct.map (rightHandedRep M) (rightHandedRep M) v) =
    (M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ := by
  rw [tensorBasis_toMatrix_map rightBasis rightBasis (rightHandedRep M)
    (rightHandedRep M) rightRightToMatrix rfl v]
  have h : (LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M)
      = M.1.map star := by
    ext i j
    simp
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualRightHanded ⊗ dualRightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma dualRightDualRightToMatrix_ρ (v : (DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl))
    (M : SL(2,ℂ)) :
    dualRightDualRightToMatrix (TensorProduct.map (dualRightHandedRep M) (dualRightHandedRep M) v) =
    ((M.1⁻¹).conjTranspose) * dualRightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  rw [tensorBasis_toMatrix_map dualRightBasis dualRightBasis (dualRightHandedRep M)
    (dualRightHandedRep M) dualRightDualRightToMatrix rfl v]
  have h : (LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M)
      = (M.1⁻¹).conjTranspose := by
    ext i j
    simp
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ dualRightHanded` is equivalent to
  `(M.1.map star) * rightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma rightDualRightToMatrix_ρ (v : (RightHandedWeyl ⊗[ℂ] DualRightHandedWeyl)) (M : SL(2,ℂ)) :
    rightDualRightToMatrix (TensorProduct.map (rightHandedRep M) (dualRightHandedRep M) v) =
    (M.1.map star) * rightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  rw [tensorBasis_toMatrix_map rightBasis dualRightBasis (rightHandedRep M)
    (dualRightHandedRep M) rightDualRightToMatrix rfl v]
  have h1 : (LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M)
      = M.1.map star := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M)
      = (M.1⁻¹).conjTranspose := by
    ext i j
    simp
  rw [h1, h2]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualRightHanded ⊗ rightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightDualRightToMatrix v * ((M.1.map star)).ᵀ`. -/
lemma dualRightRightToMatrix_ρ (v : (DualRightHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    dualRightRightToMatrix (TensorProduct.map (dualRightHandedRep M) (rightHandedRep M) v) =
    ((M.1⁻¹).conjTranspose) * dualRightRightToMatrix v * (M.1.map star)ᵀ := by
  rw [tensorBasis_toMatrix_map dualRightBasis rightBasis (dualRightHandedRep M)
    (rightHandedRep M) dualRightRightToMatrix rfl v]
  have h1 : (LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M)
      = (M.1⁻¹).conjTranspose := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M)
      = M.1.map star := by
    ext i j
    simp
  rw [h1, h2]

set_option backward.isDefEq.respectTransparency false in
lemma dualLeftDualRightToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] DualRightHandedWeyl))
    (M : SL(2,ℂ)) :
    dualLeftDualRightToMatrix (TensorProduct.map (dualLeftHandedRep M) (dualRightHandedRep M) v) =
    (M.1⁻¹)ᵀ * dualLeftDualRightToMatrix v * ((M.1⁻¹).conjTranspose)ᵀ := by
  rw [tensorBasis_toMatrix_map dualLeftBasis dualRightBasis (dualLeftHandedRep M)
    (dualRightHandedRep M) dualLeftDualRightToMatrix rfl v]
  have h1 : (LinearMap.toMatrix dualLeftBasis dualLeftBasis) (dualLeftHandedRep M)
      = (M.1⁻¹)ᵀ := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix dualRightBasis dualRightBasis) (dualRightHandedRep M)
      = (M.1⁻¹).conjTranspose := by
    ext i j
    simp
  rw [h1, h2]

set_option backward.isDefEq.respectTransparency false in
lemma leftRightToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    leftRightToMatrix (TensorProduct.map (leftHandedRep M) (rightHandedRep M) v) =
    M.1 * leftRightToMatrix v * (M.1)ᴴ := by
  rw [tensorBasis_toMatrix_map leftBasis rightBasis (leftHandedRep M)
    (rightHandedRep M) leftRightToMatrix rfl v]
  have h1 : (LinearMap.toMatrix leftBasis leftBasis) (leftHandedRep M) = M.1 := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix rightBasis rightBasis) (rightHandedRep M)
      = M.1.map star := by
    ext i j
    simp
  have h3 : (M.1.map star)ᵀ = (M.1)ᴴ := rfl
  rw [h1, h2, h3]

/-!

## The symm version of the group actions.

-/

/-- A `_ρ` group-action law on a `*ToMatrix` equivalence transports through the inverse: if
  `eqv (ρ w) = A * eqv w * B` then `ρ (eqv.symm v) = eqv.symm (A * v * B)`. Used to derive the
  `_ρ_symm` lemmas from their `_ρ` counterparts. -/
private lemma map_symm_of_ρ {n : Type*} [Fintype n] [DecidableEq n] {W : Type*}
    [AddCommGroup W] [Module ℂ W] (eqv : W ≃ₗ[ℂ] Matrix n n ℂ) (ρ : W →ₗ[ℂ] W)
    {A B : Matrix n n ℂ} (hρ : ∀ w, eqv (ρ w) = A * eqv w * B) (v : Matrix n n ℂ) :
    ρ (eqv.symm v) = eqv.symm (A * v * B) := by
  have h1 := hρ (eqv.symm v)
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma leftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHandedRep M) (leftHandedRep M) (leftLeftToMatrix.symm v) =
    leftLeftToMatrix.symm (M.1 * v * (M.1)ᵀ) :=
  map_symm_of_ρ leftLeftToMatrix _ (fun w => leftLeftToMatrix_ρ w M) v

lemma dualLeftdualLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualLeftHandedRep M) (dualLeftHandedRep M)
      (dualLeftdualLeftToMatrix.symm v) =
    dualLeftdualLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1⁻¹)) :=
  map_symm_of_ρ dualLeftdualLeftToMatrix _ (fun w => dualLeftdualLeftToMatrix_ρ w M) v

lemma leftDualLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHandedRep M) (dualLeftHandedRep M) (leftDualLeftToMatrix.symm v) =
    leftDualLeftToMatrix.symm (M.1 * v * (M.1⁻¹)) :=
  map_symm_of_ρ leftDualLeftToMatrix _ (fun w => leftDualLeftToMatrix_ρ w M) v

lemma dualLeftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualLeftHandedRep M) (leftHandedRep M) (dualLeftLeftToMatrix.symm v) =
    dualLeftLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1)ᵀ) :=
  map_symm_of_ρ dualLeftLeftToMatrix _ (fun w => dualLeftLeftToMatrix_ρ w M) v

lemma rightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (rightHandedRep M) (rightHandedRep M) (rightRightToMatrix.symm v) =
    rightRightToMatrix.symm ((M.1.map star) * v * ((M.1.map star))ᵀ) :=
  map_symm_of_ρ rightRightToMatrix _ (fun w => rightRightToMatrix_ρ w M) v

lemma dualRightDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualRightHandedRep M) (dualRightHandedRep M)
      (dualRightDualRightToMatrix.symm v) =
    dualRightDualRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * ((M.1⁻¹).conjTranspose)ᵀ) :=
  map_symm_of_ρ dualRightDualRightToMatrix _ (fun w => dualRightDualRightToMatrix_ρ w M) v

lemma rightDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (rightHandedRep M) (dualRightHandedRep M) (rightDualRightToMatrix.symm v) =
    rightDualRightToMatrix.symm ((M.1.map star) * v * (((M.1⁻¹).conjTranspose)ᵀ)) :=
  map_symm_of_ρ rightDualRightToMatrix _ (fun w => rightDualRightToMatrix_ρ w M) v

lemma dualRightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualRightHandedRep M) (rightHandedRep M) (dualRightRightToMatrix.symm v) =
    dualRightRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * (M.1.map star)ᵀ) :=
  map_symm_of_ρ dualRightRightToMatrix _ (fun w => dualRightRightToMatrix_ρ w M) v

lemma dualLeftDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (dualLeftHandedRep M) (dualRightHandedRep M)
      (dualLeftDualRightToMatrix.symm v) =
    dualLeftDualRightToMatrix.symm ((M.1⁻¹)ᵀ * v * ((M.1⁻¹).conjTranspose)ᵀ) :=
  map_symm_of_ρ dualLeftDualRightToMatrix _ (fun w => dualLeftDualRightToMatrix_ρ w M) v

lemma leftRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHandedRep M) (rightHandedRep M) (leftRightToMatrix.symm v) =
    leftRightToMatrix.symm (M.1 * v * (M.1)ᴴ) :=
  map_symm_of_ρ leftRightToMatrix _ (fun w => leftRightToMatrix_ρ w M) v

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
