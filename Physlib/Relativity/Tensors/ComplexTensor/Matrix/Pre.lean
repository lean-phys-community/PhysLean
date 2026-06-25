/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
/-!

# Tensor products of two complex Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

namespace Lorentz

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

/-- Equivalence of `complexContr ⊗ complexContr` to `4 x 4` complex matrices. -/
def contrContrToMatrix : (ContrℂModule ⊗[ℂ] ContrℂModule) ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct complexContrBasis complexContrBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

/-- Expanding `contrContrToMatrix` in terms of the standard basis. -/
lemma contrContrToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    contrContrToMatrix.symm M =
    ∑ i, ∑ j, M i j • (complexContrBasis i ⊗ₜ[ℂ] complexContrBasis j) := by
  exact tensorBasis_toMatrix_symm_expand complexContrBasis complexContrBasis M

/-- Equivalence of `complexCo ⊗ complexCo` to `4 x 4` complex matrices. -/
def coCoToMatrix : (CoℂModule ⊗[ℂ] CoℂModule) ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct complexCoBasis complexCoBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

/-- Expanding `coCoToMatrix` in terms of the standard basis. -/
lemma coCoToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    coCoToMatrix.symm M = ∑ i, ∑ j, M i j • (complexCoBasis i ⊗ₜ[ℂ] complexCoBasis j) := by
  exact tensorBasis_toMatrix_symm_expand complexCoBasis complexCoBasis M

/-- Equivalence of `complexContr ⊗ complexCo` to `4 x 4` complex matrices. -/
def contrCoToMatrix : (ContrℂModule ⊗[ℂ] CoℂModule) ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct complexContrBasis complexCoBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

/-- Expansion of `contrCoToMatrix` in terms of the standard basis. -/
lemma contrCoToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    contrCoToMatrix.symm M = ∑ i, ∑ j, M i j • (complexContrBasis i ⊗ₜ[ℂ] complexCoBasis j) := by
  exact tensorBasis_toMatrix_symm_expand complexContrBasis complexCoBasis M

/-- Equivalence of `complexCo ⊗ complexContr` to `4 x 4` complex matrices. -/
def coContrToMatrix : (CoℂModule ⊗[ℂ] ContrℂModule) ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct complexCoBasis complexContrBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

/-- Expansion of `coContrToMatrix` in terms of the standard basis. -/
lemma coContrToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    coContrToMatrix.symm M = ∑ i, ∑ j, M i j • (complexCoBasis i ⊗ₜ[ℂ] complexContrBasis j) := by
  exact tensorBasis_toMatrix_symm_expand complexCoBasis complexContrBasis M

/-!

## Group actions

-/

/-- Common core for the `*ToMatrix_ρ` lemmas: the `ToMatrix` equivalence intertwines
`TensorProduct.map f g` with conjugation by the matrices of `f` and `g`, where the
equivalence is the canonical triple composition built from the bases `b₁`, `b₂`. -/
private lemma tensorBasis_toMatrix_map
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (b₁ : Basis (Fin 1 ⊕ Fin 3) ℂ V₁) (b₂ : Basis (Fin 1 ⊕ Fin 3) ℂ V₂)
    (f : V₁ →ₗ[ℂ] V₁) (g : V₂ →ₗ[ℂ] V₂)
    (eqv : (V₁ ⊗[ℂ] V₂) ≃ₗ[ℂ] Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ)
    (heqv : eqv = (b₁.tensorProduct b₂).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
      LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3))
    (v : V₁ ⊗[ℂ] V₂) :
    eqv (TensorProduct.map f g v) =
    (LinearMap.toMatrix b₁ b₁ f) * eqv v * (LinearMap.toMatrix b₂ b₂ g)ᵀ := by
  have hpt : ∀ (w : V₁ ⊗[ℂ] V₂) (i j : Fin 1 ⊕ Fin 3), eqv w i j =
      (((b₁.tensorProduct b₂).repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
        LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) w) i j := by
    intro w i j
    rw [heqv]
    rfl
  funext i j
  have key : eqv (TensorProduct.map f g v) i j =
      ((LinearMap.toMatrix (b₁.tensorProduct b₂) (b₁.tensorProduct b₂)
        (TensorProduct.map f g))
        *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
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
          Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
          LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) v) k.1 k.2) = _
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
lemma contrContrToMatrix_ρ (v : (ContrℂModule ⊗[ℂ] ContrℂModule)) (M : SL(2,ℂ)) :
    contrContrToMatrix (TensorProduct.map (ContrℂModule.SL2CRep M) (ContrℂModule.SL2CRep M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * contrContrToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ := by
  rw [tensorBasis_toMatrix_map complexContrBasis complexContrBasis (ContrℂModule.SL2CRep M)
    (ContrℂModule.SL2CRep M) contrContrToMatrix rfl v]
  have h : (LinearMap.toMatrix complexContrBasis complexContrBasis) (ContrℂModule.SL2CRep M)
      = LorentzGroup.toComplex (SL2C.toLorentzGroup M) := by
    ext i j
    simp
  rw [h]

set_option backward.isDefEq.respectTransparency false in
lemma coCoToMatrix_ρ (v : (CoℂModule ⊗[ℂ] CoℂModule)) (M : SL(2,ℂ)) :
    coCoToMatrix (TensorProduct.map (CoℂModule.SL2CRep M) (CoℂModule.SL2CRep M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * coCoToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ := by
  rw [tensorBasis_toMatrix_map complexCoBasis complexCoBasis (CoℂModule.SL2CRep M)
    (CoℂModule.SL2CRep M) coCoToMatrix rfl v]
  have h : (LinearMap.toMatrix complexCoBasis complexCoBasis) (CoℂModule.SL2CRep M)
      = (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ := by
    ext i j
    simp
  rw [h, transpose_transpose]

set_option backward.isDefEq.respectTransparency false in
lemma contrCoToMatrix_ρ (v : (ContrℂModule ⊗[ℂ] CoℂModule)) (M : SL(2,ℂ)) :
    contrCoToMatrix (TensorProduct.map (ContrℂModule.SL2CRep M) (CoℂModule.SL2CRep M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * contrCoToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ := by
  rw [tensorBasis_toMatrix_map complexContrBasis complexCoBasis (ContrℂModule.SL2CRep M)
    (CoℂModule.SL2CRep M) contrCoToMatrix rfl v]
  have h1 : (LinearMap.toMatrix complexContrBasis complexContrBasis) (ContrℂModule.SL2CRep M)
      = LorentzGroup.toComplex (SL2C.toLorentzGroup M) := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix complexCoBasis complexCoBasis) (CoℂModule.SL2CRep M)
      = (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ := by
    ext i j
    simp
  rw [h1, h2, transpose_transpose]

set_option backward.isDefEq.respectTransparency false in
lemma coContrToMatrix_ρ (v : (CoℂModule ⊗[ℂ] ContrℂModule)) (M : SL(2,ℂ)) :
    coContrToMatrix (TensorProduct.map (CoℂModule.SL2CRep M) (ContrℂModule.SL2CRep M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * coContrToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ := by
  rw [tensorBasis_toMatrix_map complexCoBasis complexContrBasis (CoℂModule.SL2CRep M)
    (ContrℂModule.SL2CRep M) coContrToMatrix rfl v]
  have h1 : (LinearMap.toMatrix complexCoBasis complexCoBasis) (CoℂModule.SL2CRep M)
      = (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix complexContrBasis complexContrBasis) (ContrℂModule.SL2CRep M)
      = LorentzGroup.toComplex (SL2C.toLorentzGroup M) := by
    ext i j
    simp
  rw [h1, h2]

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

lemma contrContrToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (ContrℂModule.SL2CRep M) (ContrℂModule.SL2CRep M)
      (contrContrToMatrix.symm v) =
    contrContrToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ) :=
  map_symm_of_ρ contrContrToMatrix _ (fun w => contrContrToMatrix_ρ w M) v

lemma coCoToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (CoℂModule.SL2CRep M) (CoℂModule.SL2CRep M) (coCoToMatrix.symm v) =
    coCoToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹) :=
  map_symm_of_ρ coCoToMatrix _ (fun w => coCoToMatrix_ρ w M) v

lemma contrCoToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (ContrℂModule.SL2CRep M) (CoℂModule.SL2CRep M) (contrCoToMatrix.symm v) =
    contrCoToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹) :=
  map_symm_of_ρ contrCoToMatrix _ (fun w => contrCoToMatrix_ρ w M) v

lemma coContrToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (CoℂModule.SL2CRep M) (ContrℂModule.SL2CRep M) (coContrToMatrix.symm v) =
    coContrToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ) :=
  map_symm_of_ρ coContrToMatrix _ (fun w => coContrToMatrix_ρ w M) v

end Lorentz
end
