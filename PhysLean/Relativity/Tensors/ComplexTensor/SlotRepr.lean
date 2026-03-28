/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Basic
public import PhysLean.Relativity.Tensors.Basic
/-!

## Component formula for the Lorentz action on a vector slot

`slot_repr_up` and `slot_repr_down` express the basis coefficients of
`ρ Λ` on a single `up` / `down` slot of `complexLorentzTensor` in terms of
`LorentzGroup.toComplex (SL2C.toLorentzGroup Λ)` (contravariant case) and its
inverse (covariant case). These are reusable facts for complex Lorentz tensors,
independent of `realLorentzTensor` or `toComplex`.

-/

@[expose] public section

namespace complexLorentzTensor

open TensorSpecies Tensor Lorentz Lorentz.SL2C Matrix MatrixGroups Complex CategoryTheory Module

variable {n : ℕ} {c : Fin n → complexLorentzTensor.Color}

/-- Basis coefficient for the Lorentz action on a contravariant (`up`) vector slot,
  as a matrix entry of `LorentzGroup.toComplex (SL2C.toLorentzGroup Λ)`. -/
lemma slot_repr_up (k : Fin n) (h : c k = Color.up) (Λ : SL(2, ℂ))
    (b i : ComponentIdx (S := complexLorentzTensor) c) :
    ((complexLorentzTensor.basis (c k)).repr
        (((complexLorentzTensor.FD.obj { as := c k }).ρ Λ)
          ((complexLorentzTensor.basis (c k)) (b k)))) (i k) =
      (LorentzGroup.toComplex (Lorentz.SL2C.toLorentzGroup Λ))
        (finSumFinEquiv.symm (Fin.cast (by
          rw [h]
          rfl) (i k)))
        (finSumFinEquiv.symm (Fin.cast (by
          rw [h]
          rfl) (b k))) := by
  rw [repr_ρ_basis_FDTransport (S := complexLorentzTensor) (c := c k) (c₁ := Color.up) h Λ (i k)
    (b k)]
  simp only [complexLorentzTensor.basis_up_eq, Lorentz.complexContrBasisFin4]
  erw [show
      (Lorentz.complexContrBasis.reindex finSumFinEquiv)
        (Fin.cast _ (b k)) =
      Lorentz.complexContrBasisFin4 (Fin.cast _ (b k)) from rfl]
  simp_rw [complexLorentzTensor.basis_eq_complexContrBasisFin4]
  simp_rw [(show Lorentz.complexContrBasisFin4 =
      Lorentz.complexContrBasis.reindex finSumFinEquiv from rfl)]
  rw [Basis.repr_reindex_apply, Basis.reindex_apply]
  simp_rw [complexLorentzTensor.FD_obj_up]
  conv_lhs => erw [← LinearMap.toMatrix_apply]
  exact (Lorentz.complexContrBasis_ρ_apply (M := Λ)
    (i := finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) (i k)))
    (j := finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) (b k))))

/-- Basis coefficient for the Lorentz action on a covariant (`down`) vector slot,
  using the inverse matrix in the same convention as `complexCoBasis_ρ_apply`. -/
lemma slot_repr_down (k : Fin n) (h : c k = Color.down) (Λ : SL(2, ℂ))
    (b i : ComponentIdx (S := complexLorentzTensor) c) :
    ((complexLorentzTensor.basis (c k)).repr
        (((complexLorentzTensor.FD.obj { as := c k }).ρ Λ)
          ((complexLorentzTensor.basis (c k)) (b k)))) (i k) =
      (LorentzGroup.toComplex (Lorentz.SL2C.toLorentzGroup Λ))⁻¹
        (finSumFinEquiv.symm (Fin.cast (by
          rw [h]
          rfl) (b k)))
        (finSumFinEquiv.symm (Fin.cast (by
          rw [h]
          rfl) (i k))) := by
  rw [repr_ρ_basis_FDTransport (S := complexLorentzTensor) (c := c k) (c₁ := Color.down) h Λ (i k)
    (b k)]
  simp only [complexLorentzTensor.basis_down_eq, Lorentz.complexCoBasisFin4]
  erw [show
      (Lorentz.complexCoBasis.reindex finSumFinEquiv)
        (Fin.cast _ (b k)) =
      Lorentz.complexCoBasisFin4 (Fin.cast _ (b k)) from rfl]
  simp_rw [complexLorentzTensor.basis_eq_complexCoBasisFin4]
  simp_rw [(show Lorentz.complexCoBasisFin4 =
      Lorentz.complexCoBasis.reindex finSumFinEquiv from rfl)]
  rw [Basis.repr_reindex_apply, Basis.reindex_apply]
  simp_rw [complexLorentzTensor.FD_obj_down]
  conv_lhs => erw [← LinearMap.toMatrix_apply]
  erw [Lorentz.complexCoBasis_ρ_apply (M := Λ)
    (i := finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) (i k)))
    (j := finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) (b k)))]
  simp only [Matrix.transpose_apply]

end complexLorentzTensor

end
