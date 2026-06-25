/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
/-!

# Tensor products of two real Lorentz vectors

-/

@[expose] public section
noncomputable section

open Matrix Module MatrixGroups Complex TensorProduct CategoryTheory.MonoidalCategory

namespace Lorentz

/-- Expanding the inverse of the canonical equivalence from a tensor product of two
based real modules to matrices, in terms of the standard basis tensors. Every
`*ToMatrixRe` below is definitionally this composition, so each
`*ToMatrixRe_symm_expand_tmul` lemma is a direct specialization. -/
lemma tensorBasis_toMatrixRe_symm_expand
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
    (b₁ : Basis ι₁ ℝ V₁) (b₂ : Basis ι₂ ℝ V₂) (M : Matrix ι₁ ι₂ ℝ) :
    ((Basis.tensorProduct b₁ b₂).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℝ ℝ (ι₁ × ι₂) ≪≫ₗ
      LinearEquiv.curry ℝ ℝ ι₁ ι₂).symm M =
    ∑ i, ∑ j, M i j • (b₁ i ⊗ₜ[ℝ] b₂ j) := by
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply, Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply b₁ b₂ i j)
  · simp

/-- Equivalence of `Contr ⊗ Contr` to `(1 + d) x (1 + d)` real matrices. -/
def contrContrToMatrixRe {d : ℕ} : (ContrMod d ⊗[ℝ] ContrMod d) ≃ₗ[ℝ]
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  (Basis.tensorProduct (contrBasis d) (contrBasis d)).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
  LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)

/-- Expanding `contrContrToMatrixRe` in terms of the standard basis. -/
lemma contrContrToMatrixRe_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    contrContrToMatrixRe.symm M = ∑ i, ∑ j, M i j • (contrBasis d i ⊗ₜ[ℝ] contrBasis d j) := by
  exact tensorBasis_toMatrixRe_symm_expand (contrBasis d) (contrBasis d) M

/-- Equivalence of `Co ⊗ Co` to `(1 + d) x (1 + d)` real matrices. -/
def coCoToMatrixRe {d : ℕ} : (Co d ⊗ Co d).V ≃ₗ[ℝ]
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  (Basis.tensorProduct (coBasis d) (coBasis d)).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
  LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)

/-- Expanding `coCoToMatrixRe` in terms of the standard basis. -/
lemma coCoToMatrixRe_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    coCoToMatrixRe.symm M = ∑ i, ∑ j, M i j • (coBasis d i ⊗ₜ[ℝ] coBasis d j) := by
  exact tensorBasis_toMatrixRe_symm_expand (coBasis d) (coBasis d) M

/-- Equivalence of `Contr d ⊗ Co d` to `(1 + d) x (1 + d)` real matrices. -/
def contrCoToMatrixRe {d : ℕ} : (Contr d ⊗ Co d).V ≃ₗ[ℝ]
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  (Basis.tensorProduct (contrBasis d) (coBasis d)).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
  LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)

/-- Expansion of ` (coBasis d) (coBasis d)` in terms of the standard basis. -/
lemma contrCoToMatrixRe_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    contrCoToMatrixRe.symm M = ∑ i, ∑ j, M i j • (contrBasis d i ⊗ₜ[ℝ] coBasis d j) := by
  exact tensorBasis_toMatrixRe_symm_expand (contrBasis d) (coBasis d) M

/-- Equivalence of `Co d ⊗ Contr d` to `(1 + d) x (1 + d)` real matrices. -/
def coContrToMatrixRe : (Co d ⊗ Contr d).V ≃ₗ[ℝ]
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  (Basis.tensorProduct (coBasis d) (contrBasis d)).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
  LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)

/-- Expansion of `coContrToMatrixRe` in terms of the standard basis. -/
lemma coContrToMatrixRe_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    coContrToMatrixRe.symm M = ∑ i, ∑ j, M i j • (coBasis d i ⊗ₜ[ℝ] contrBasis d j) := by
  exact tensorBasis_toMatrixRe_symm_expand (coBasis d) (contrBasis d) M

/-!

## Group actions

-/

/-- Common core for the `*ToMatrixRe_ρ` lemmas: the `ToMatrixRe` equivalence intertwines
`TensorProduct.map f g` with conjugation by the matrices of `f` and `g`, where the
equivalence is the canonical triple composition built from the bases `b₁`, `b₂`. -/
private lemma tensorBasis_toMatrixRe_map {d : ℕ}
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
    (b₁ : Basis (Fin 1 ⊕ Fin d) ℝ V₁) (b₂ : Basis (Fin 1 ⊕ Fin d) ℝ V₂)
    (f : V₁ →ₗ[ℝ] V₁) (g : V₂ →ₗ[ℝ] V₂)
    (eqv : (V₁ ⊗[ℝ] V₂) ≃ₗ[ℝ] Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (heqv : eqv = (b₁.tensorProduct b₂).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
      LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d))
    (v : V₁ ⊗[ℝ] V₂) :
    eqv (TensorProduct.map f g v) =
    (LinearMap.toMatrix b₁ b₁ f) * eqv v * (LinearMap.toMatrix b₂ b₂ g)ᵀ := by
  have hpt : ∀ (w : V₁ ⊗[ℝ] V₂) (i j : Fin 1 ⊕ Fin d), eqv w i j =
      (((b₁.tensorProduct b₂).repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
        LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)) w) i j := by
    intro w i j
    rw [heqv]
    rfl
  funext i j
  have key : eqv (TensorProduct.map f g v) i j =
      ((LinearMap.toMatrix (b₁.tensorProduct b₂) (b₁.tensorProduct b₂)
        (TensorProduct.map f g))
        *ᵥ ((Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)))
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
          Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
          LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)) v) k.1 k.2) = _
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
lemma contrContrToMatrixRe_ρ {d : ℕ} (v : (Contr d ⊗ Contr d).V) (M : LorentzGroup d) :
    contrContrToMatrixRe (TensorProduct.map ((Contr d).ρ M) ((Contr d).ρ M) v) =
    M.1 * contrContrToMatrixRe v * Mᵀ := by
  rw [show contrContrToMatrixRe ((TensorProduct.map ((Contr d).ρ M) ((Contr d).ρ M)) v)
    = _ from tensorBasis_toMatrixRe_map (contrBasis d) (contrBasis d) _ _
    contrContrToMatrixRe rfl v]
  have h : (LinearMap.toMatrix (contrBasis d) (contrBasis d)) ((Contr d).ρ M) = M.1 := by
    ext i j
    simp
  rw [h]

set_option backward.isDefEq.respectTransparency false in
lemma coCoToMatrixRe_ρ {d : ℕ} (v : ((Co d) ⊗ (Co d)).V) (M : LorentzGroup d) :
    coCoToMatrixRe (TensorProduct.map ((Co d).ρ M) ((Co d).ρ M) v) =
    M.1⁻¹ᵀ * coCoToMatrixRe v * M⁻¹ := by
  rw [show coCoToMatrixRe ((TensorProduct.map ((Co d).ρ M) ((Co d).ρ M)) v)
    = _ from tensorBasis_toMatrixRe_map (coBasis d) (coBasis d) _ _
    coCoToMatrixRe rfl v]
  have h : (LinearMap.toMatrix (coBasis d) (coBasis d)) ((Co d).ρ M) = M.1⁻¹ᵀ := by
    ext i j
    simp [← LorentzGroup.coe_inv]
  rw [h, transpose_transpose, ← LorentzGroup.coe_inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma contrCoToMatrixRe_ρ {d : ℕ} (v : ((Contr d) ⊗ (Co d)).V) (M : LorentzGroup d) :
    contrCoToMatrixRe (TensorProduct.map ((Contr d).ρ M) ((Co d).ρ M) v) =
    M.1 * contrCoToMatrixRe v * M.1⁻¹ := by
  rw [show contrCoToMatrixRe ((TensorProduct.map ((Contr d).ρ M) ((Co d).ρ M)) v)
    = _ from tensorBasis_toMatrixRe_map (contrBasis d) (coBasis d) _ _
    contrCoToMatrixRe rfl v]
  have h1 : (LinearMap.toMatrix (contrBasis d) (contrBasis d)) ((Contr d).ρ M) = M.1 := by
    ext i j
    simp
  have h2 : (LinearMap.toMatrix (coBasis d) (coBasis d)) ((Co d).ρ M) = M.1⁻¹ᵀ := by
    ext i j
    simp [← LorentzGroup.coe_inv]
  rw [h1, h2, transpose_transpose]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma coContrToMatrixRe_ρ {d : ℕ} (v : ((Co d) ⊗ (Contr d)).V) (M : LorentzGroup d) :
    coContrToMatrixRe (TensorProduct.map ((Co d).ρ M) ((Contr d).ρ M) v) =
    M.1⁻¹ᵀ * coContrToMatrixRe v * M.1ᵀ := by
  rw [show coContrToMatrixRe ((TensorProduct.map ((Co d).ρ M) ((Contr d).ρ M)) v)
    = _ from tensorBasis_toMatrixRe_map (coBasis d) (contrBasis d) _ _
    coContrToMatrixRe rfl v]
  have h1 : (LinearMap.toMatrix (coBasis d) (coBasis d)) ((Co d).ρ M) = M.1⁻¹ᵀ := by
    ext i j
    simp [← LorentzGroup.coe_inv]
  have h2 : (LinearMap.toMatrix (contrBasis d) (contrBasis d)) ((Contr d).ρ M) = M.1 := by
    ext i j
    simp
  rw [h1, h2]
  rfl

/-!

## The symm version of the group actions.

-/

lemma contrContrToMatrixRe_ρ_symm {d : ℕ} (v : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (M : LorentzGroup d) :
    TensorProduct.map ((Contr d).ρ M) ((Contr d).ρ M) (contrContrToMatrixRe.symm v) =
    contrContrToMatrixRe.symm (M.1 * v * M.1ᵀ) := by
  have h1 := contrContrToMatrixRe_ρ (contrContrToMatrixRe.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma coCoToMatrixRe_ρ_symm {d : ℕ} (v : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (M : LorentzGroup d) :
    TensorProduct.map ((Co d).ρ M) ((Co d).ρ M) (coCoToMatrixRe.symm v) =
    coCoToMatrixRe.symm (M.1⁻¹ᵀ * v * M.1⁻¹) := by
  have h1 := coCoToMatrixRe_ρ (coCoToMatrixRe.symm v) M
  simp only [LinearEquiv.apply_symm_apply, ← LorentzGroup.coe_inv] at h1
  simp only [← LorentzGroup.coe_inv]
  rw [← h1]
  simp

lemma contrCoToMatrixRe_ρ_symm {d : ℕ} (v : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (M : LorentzGroup d) :
    TensorProduct.map ((Contr d).ρ M) ((Co d).ρ M) (contrCoToMatrixRe.symm v) =
    contrCoToMatrixRe.symm (M.1 * v * M.1⁻¹) := by
  have h1 := contrCoToMatrixRe_ρ (contrCoToMatrixRe.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma coContrToMatrixRe_ρ_symm {d : ℕ} (v : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (M : LorentzGroup d) :
    TensorProduct.map ((Co d).ρ M) ((Contr d).ρ M) (coContrToMatrixRe.symm v) =
    coContrToMatrixRe.symm (M.1⁻¹ᵀ * v * M.1ᵀ) := by
  have h1 := coContrToMatrixRe_ρ (coContrToMatrixRe.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

end Lorentz
end
