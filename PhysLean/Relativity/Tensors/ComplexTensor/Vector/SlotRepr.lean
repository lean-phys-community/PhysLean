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

The main lemmas `repr_ρ_basis_vector_up` and `repr_ρ_basis_vector_down` are stated directly for
`Color.up` / `Color.down` with indices in `Fin 4` (the same as `Fin (repDim Color.up)` and
`Fin (repDim Color.down)` by definition).

When a slot color is only known up to an equality `c₀ = Color.up` (or `down`), for example as
`c k` in a multi-index tensor, use `repr_ρ_basis_vector_up_of_eq` /
`repr_ρ_basis_vector_down_of_eq`, which package the `Fin.cast` along `repDim` and the transport
on the basis and representation.

-/

@[expose] public section

namespace complexLorentzTensor

open TensorSpecies Tensor Lorentz Lorentz.SL2C Matrix MatrixGroups Complex CategoryTheory Module

/--
Component formula for the standard contravariant vector slot `Color.up`.

For `b, i : Fin 4`, the `i`-component of `ρ Λ` on `basis Color.up b` equals the corresponding entry
of `LorentzGroup.toComplex (SL2C.toLorentzGroup Λ)` in `Fin 1 ⊕ Fin 3` coordinates.
-/
lemma repr_ρ_basis_vector_up (Λ : SL(2, ℂ)) (b i : Fin 4) :
    ((complexLorentzTensor.basis Color.up).repr
        (((complexLorentzTensor.FD.obj { as := Color.up }).ρ Λ)
          (complexLorentzTensor.basis Color.up b))) i =
      (LorentzGroup.toComplex (Lorentz.SL2C.toLorentzGroup Λ))
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm b) := by
  simp only [complexLorentzTensor.basis_up_eq]
  erw [Lorentz.complexContrBasis_reindex_apply_eq_fin4]
  simp_rw [complexLorentzTensor.basis_eq_complexContrBasisFin4,
    Lorentz.complexContrBasisFin4_eq_reindex]
  rw [Basis.repr_reindex_apply, Basis.reindex_apply]
  simp_rw [complexLorentzTensor.FD_obj_up]
  conv_lhs => erw [← LinearMap.toMatrix_apply]
  exact Lorentz.complexContrBasis_ρ_apply (M := Λ) (i := finSumFinEquiv.symm i)
    (j := finSumFinEquiv.symm b)

/--
Transport version of `repr_ρ_basis_vector_up` for a color `c₀` that is propositionally `Color.up`.
-/
lemma repr_ρ_basis_vector_up_of_eq (c₀ : complexLorentzTensor.Color) (h : c₀ = Color.up)
    (Λ : SL(2, ℂ)) (b i : Fin (complexLorentzTensor.repDim c₀)) :
    ((complexLorentzTensor.basis c₀).repr
        (((complexLorentzTensor.FD.obj { as := c₀ }).ρ Λ)
          (complexLorentzTensor.basis c₀ b))) i =
      (LorentzGroup.toComplex (Lorentz.SL2C.toLorentzGroup Λ))
        (finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) i))
        (finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) b)) := by
  subst h
  simpa using repr_ρ_basis_vector_up Λ b i

/--
Component formula for the standard covariant vector slot `Color.down`.

For `b, i : Fin 4`, the `i`-component of `ρ Λ` on `basis Color.down b` matches the inverse complex
Lorentz matrix as in `Lorentz.complexCoBasis_ρ_apply` (with transpose indexing on `Fin 1 ⊕ Fin 3`).
-/
lemma repr_ρ_basis_vector_down (Λ : SL(2, ℂ)) (b i : Fin 4) :
    ((complexLorentzTensor.basis Color.down).repr
        (((complexLorentzTensor.FD.obj { as := Color.down }).ρ Λ)
          (complexLorentzTensor.basis Color.down b))) i =
      (LorentzGroup.toComplex (Lorentz.SL2C.toLorentzGroup Λ))⁻¹
        (finSumFinEquiv.symm b) (finSumFinEquiv.symm i) := by
  simp only [complexLorentzTensor.basis_down_eq]
  erw [Lorentz.complexCoBasis_reindex_apply_eq_fin4]
  simp_rw [complexLorentzTensor.basis_eq_complexCoBasisFin4,
    Lorentz.complexCoBasisFin4_eq_reindex]
  rw [Basis.repr_reindex_apply, Basis.reindex_apply]
  simp_rw [complexLorentzTensor.FD_obj_down]
  conv_lhs => erw [← LinearMap.toMatrix_apply]
  erw [Lorentz.complexCoBasis_ρ_apply (M := Λ) (i := finSumFinEquiv.symm i)
    (j := finSumFinEquiv.symm b)]
  simp only [Matrix.transpose_apply]

/--
Transport version of `repr_ρ_basis_vector_down` for a color `c₀` that is propositionally
`Color.down`.
-/
lemma repr_ρ_basis_vector_down_of_eq (c₀ : complexLorentzTensor.Color) (h : c₀ = Color.down)
    (Λ : SL(2, ℂ)) (b i : Fin (complexLorentzTensor.repDim c₀)) :
    ((complexLorentzTensor.basis c₀).repr
        (((complexLorentzTensor.FD.obj { as := c₀ }).ρ Λ)
          (complexLorentzTensor.basis c₀ b))) i =
      (LorentzGroup.toComplex (Lorentz.SL2C.toLorentzGroup Λ))⁻¹
        (finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) b))
        (finSumFinEquiv.symm (Fin.cast (by rw [h]; rfl) i)) := by
  subst h
  simpa using repr_ρ_basis_vector_down Λ b i

end complexLorentzTensor

end
