/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Basic
/-!

# Contraction of Weyl fermions

We define the contraction of Weyl fermions.

-/

@[expose] public section

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## Contraction of Weyl fermions.

-/
open CategoryTheory.MonoidalCategory

/-- The bi-linear map corresponding to contraction of a left-handed Weyl fermion with a
  alt-left-handed Weyl fermion. -/
def leftAltBi : LeftHandedModule →ₗ[ℂ] AltLeftHandedModule →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r ψ := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The bi-linear map corresponding to contraction of a alt-left-handed Weyl fermion with a
  left-handed Weyl fermion. -/
def altLeftBi : AltLeftHandedModule →ₗ[ℂ] LeftHandedModule →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The bi-linear map corresponding to contraction of a right-handed Weyl fermion with a
  alt-right-handed Weyl fermion. -/
def rightAltBi : RightHandedModule →ₗ[ℂ] AltRightHandedModule →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r ψ := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The bi-linear map corresponding to contraction of a alt-right-handed Weyl fermion with a
  right-handed Weyl fermion. -/
def altRightBi : AltRightHandedModule →ₗ[ℂ] RightHandedModule →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The linear map from leftHandedWeyl ⊗ altLeftHandedWeyl to ℂ given by
    summing over components of leftHandedWeyl and altLeftHandedWeyl in the
    standard basis (i.e. the dot product).
    Physically, the contraction of a left-handed Weyl fermion with a alt-left-handed Weyl fermion.
    In index notation this is ψ^a φ_a. -/
def leftAltContraction : (leftHandedRep.tprod altLeftHandedRep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift leftAltBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
    change (M.1 *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    simp

lemma leftAltContraction_hom_tmul (ψ : LeftHandedModule)
    (φ : AltLeftHandedModule) :
    leftAltContraction (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma leftAltContraction_basis (i j : Fin 2) :
    leftAltContraction (leftBasis i ⊗ₜ altLeftBasis j) = if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [leftAltContraction_hom_tmul]
  simp only [leftBasis_toFin2ℂ, altLeftBasis_toFin2ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- The linear map from altLeftHandedWeyl ⊗ leftHandedWeyl to ℂ given by
    summing over components of altLeftHandedWeyl and leftHandedWeyl in the
    standard basis (i.e. the dot product).
    Physically, the contraction of a alt-left-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ_a ψ^a. -/
def altLeftContraction : (altLeftHandedRep.tprod leftHandedRep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift altLeftBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
    change (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1 *ᵥ ψ.toFin2ℂ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    simp

lemma altLeftContraction_hom_tmul (φ : AltLeftHandedModule) (ψ : LeftHandedModule) :
    altLeftContraction (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma altLeftContraction_basis (i j : Fin 2) :
    altLeftContraction (altLeftBasis i ⊗ₜ leftBasis j) = if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [altLeftContraction_hom_tmul]
  simp only [altLeftBasis_toFin2ℂ, leftBasis_toFin2ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/--
The linear map from `rightHandedWeyl ⊗ altRightHandedWeyl` to `ℂ` given by
  summing over components of `rightHandedWeyl` and `altRightHandedWeyl` in the
  standard basis (i.e. the dot product).
  The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
  In index notation this is `ψ^{dot a} φ_{dot a}`.
-/
def rightAltContraction : (rightHandedRep.tprod altRightHandedRep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift rightAltBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
    change (M.1.map star *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹.conjTranspose *ᵥ φ.toFin2ℂ) =
      ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    have h1 : (M.1)⁻¹ᴴ = ((M.1)⁻¹.map star)ᵀ := by rfl
    rw [dotProduct_mulVec, h1, vecMul_transpose, mulVec_mulVec]
    have h2 : ((M.1)⁻¹.map star * (M.1).map star) = 1 := by
      refine transpose_inj.mp ?_
      rw [transpose_mul]
      change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
      rw [← @conjTranspose_mul]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
    rw [h2]
    simp only [one_mulVec, vec2_dotProduct, Fin.isValue, RightHandedModule.toFin2ℂEquiv_apply,
      AltRightHandedModule.toFin2ℂEquiv_apply]

lemma rightAltContraction_hom_tmul (ψ : RightHandedModule)
    (φ : AltRightHandedModule) :
    rightAltContraction (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma rightAltContraction_basis (i j : Fin 2) :
    rightAltContraction (rightBasis i ⊗ₜ altRightBasis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [rightAltContraction_hom_tmul]
  simp only [rightBasis_toFin2ℂ, altRightBasis_toFin2ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/--
  The linear map from altRightHandedWeyl ⊗ rightHandedWeyl to ℂ given by
    summing over components of altRightHandedWeyl and rightHandedWeyl in the
    standard basis (i.e. the dot product).
  The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ_{dot a} ψ^{dot a}.
-/
def altRightContraction : (altRightHandedRep.tprod rightHandedRep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift altRightBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
    change (M.1⁻¹.conjTranspose *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1.map star *ᵥ ψ.toFin2ℂ) =
      φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    have h1 : (M.1)⁻¹ᴴ = ((M.1)⁻¹.map star)ᵀ := by rfl
    rw [dotProduct_mulVec, h1, mulVec_transpose, vecMul_vecMul]
    have h2 : ((M.1)⁻¹.map star * (M.1).map star) = 1 := by
      refine transpose_inj.mp ?_
      rw [transpose_mul]
      change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
      rw [← @conjTranspose_mul]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
    rw [h2]
    simp only [vecMul_one, vec2_dotProduct, Fin.isValue, AltRightHandedModule.toFin2ℂEquiv_apply,
      RightHandedModule.toFin2ℂEquiv_apply]

lemma altRightContraction_hom_tmul (φ : AltRightHandedModule)
    (ψ : RightHandedModule) :
    altRightContraction (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma altRightContraction_basis (i j : Fin 2) :
    altRightContraction (altRightBasis i ⊗ₜ rightBasis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [altRightContraction_hom_tmul]
  simp only [altRightBasis_toFin2ℂ, rightBasis_toFin2ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

## Symmetry properties

-/

lemma leftAltContraction_tmul_symm (ψ : LeftHandedModule) (φ : AltLeftHandedModule) :
    leftAltContraction (ψ ⊗ₜ[ℂ] φ) = altLeftContraction (φ ⊗ₜ[ℂ] ψ) := by
  rw [leftAltContraction_hom_tmul, altLeftContraction_hom_tmul, dotProduct_comm]

lemma altLeftContraction_tmul_symm (φ : AltLeftHandedModule) (ψ : LeftHandedModule) :
    altLeftContraction (φ ⊗ₜ[ℂ] ψ) = leftAltContraction (ψ ⊗ₜ[ℂ] φ) := by
  rw [leftAltContraction_tmul_symm]

lemma rightAltContraction_tmul_symm (ψ : RightHandedModule) (φ : AltRightHandedModule) :
    rightAltContraction (ψ ⊗ₜ[ℂ] φ) = altRightContraction (φ ⊗ₜ[ℂ] ψ) := by
  rw [rightAltContraction_hom_tmul, altRightContraction_hom_tmul, dotProduct_comm]

lemma altRightContraction_tmul_symm (φ : AltRightHandedModule) (ψ : RightHandedModule) :
    altRightContraction (φ ⊗ₜ[ℂ] ψ) = rightAltContraction (ψ ⊗ₜ[ℂ] φ) := by
  rw [rightAltContraction_tmul_symm]

end
end Fermion
