/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Basic
public import PhysLean.Relativity.Tensors.Basic
/-!

## Component formulas for the standard vector slots of `complexLorentzTensor`

In `complexLorentzTensor`, the colors `Color.up` and `Color.down` are the standard Lorentz
vector colors: they are represented by the canonical contravariant and covariant 4-dimensional
complex Lorentz representations.

This file provides the corresponding component formulas for the action of `SL(2, ℂ)` on such slots.
Concretely, it rewrites basis coefficients for the action on a color-indexed slot
`(complexLorentzTensor.FD.obj { as := c k })` in terms of the usual matrix entries of the standard
complex Lorentz matrix.

These lemmas are meant as reusable API for later componentwise proofs with complex Lorentz tensors:
they let one pass directly from an `up`/`down` slot of `complexLorentzTensor`
to the standard 4-vector / 4-covector formulas.

-/

@[expose] public section

namespace complexLorentzTensor

open TensorSpecies Tensor Lorentz Lorentz.SL2C Matrix MatrixGroups Complex CategoryTheory Module

variable {n : ℕ} {c : Fin n → complexLorentzTensor.Color}

/--
Component formula for the standard contravariant vector color `Color.up`.

If the `k`-th slot of a complex Lorentz tensor has color `up`, then the `(i k)`-coordinate
of the image of the basis vector `(basis (c k)) (b k)` under the slot action
`((complexLorentzTensor.FD.obj { as := c k }).ρ Λ)` is exactly the corresponding entry of
the standard complex Lorentz matrix `LorentzGroup.toComplex (SL2C.toLorentzGroup Λ)`.

This is the coefficient-level identification of an `up` slot of `complexLorentzTensor` with
the usual contravariant Lorentz 4-vector representation.
-/
lemma repr_ρ_basis_vector_up (k : Fin n) (h : c k = Color.up) (Λ : SL(2, ℂ))
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
  simp only [complexLorentzTensor.basis_up_eq]
  erw [Lorentz.complexContrBasis_reindex_apply_eq_fin4]
  simp_rw [complexLorentzTensor.basis_eq_complexContrBasisFin4,
    Lorentz.complexContrBasisFin4_eq_reindex]
  rw [Basis.repr_reindex_apply, Basis.reindex_apply]
  simp_rw [complexLorentzTensor.FD_obj_up]
  conv_lhs => erw [← LinearMap.toMatrix_apply]
  exact (Lorentz.complexContrBasis_ρ_apply (M := Λ)
    (i := finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) (i k)))
    (j := finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) (b k))))

/--
Component formula for the standard covariant vector color `Color.down`.

If the `k`-th slot of a complex Lorentz tensor has color `down`, then the `(i k)`-coordinate of
the image of the basis vector `(basis (c k)) (b k)` under the slot action
`((complexLorentzTensor.FD.obj { as := c k }).ρ Λ)` is the corresponding entry of
the inverse complex Lorentz matrix, in the same convention as `Lorentz.complexCoBasis_ρ_apply`.

This is the coefficient-level identification of a `down` slot of `complexLorentzTensor` with
the usual covariant Lorentz 4-covector representation.
-/
lemma repr_ρ_basis_vector_down (k : Fin n) (h : c k = Color.down) (Λ : SL(2, ℂ))
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
  simp only [complexLorentzTensor.basis_down_eq]
  erw [Lorentz.complexCoBasis_reindex_apply_eq_fin4]
  simp_rw [complexLorentzTensor.basis_eq_complexCoBasisFin4, Lorentz.complexCoBasisFin4_eq_reindex]
  rw [Basis.repr_reindex_apply, Basis.reindex_apply]
  simp_rw [complexLorentzTensor.FD_obj_down]
  conv_lhs => erw [← LinearMap.toMatrix_apply]
  erw [Lorentz.complexCoBasis_ρ_apply (M := Λ)
    (i := finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) (i k)))
    (j := finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) (b k)))]
  simp only [Matrix.transpose_apply]

end complexLorentzTensor

end
