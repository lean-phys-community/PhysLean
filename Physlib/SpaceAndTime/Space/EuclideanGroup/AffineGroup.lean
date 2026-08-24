/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu
-/
module

public import Physlib.SpaceAndTime.Space.EuclideanGroup.Basic

/-!
# The inclusion of the Euclidean group into the affine automorphism group

This file has two parts.

**Part 1: the inclusion.** The abstract Euclidean group `EuclideanGroup n = ℝⁿ ⋊ O(n)` is
included into Mathlib's affine automorphism group as the composite of two monoid homomorphisms

`EuclideanGroup n →* AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) _ →* AffineEquiv ℝ _ _`.

* `EuclideanGroup.orthogonalToLinearIsometryEquiv` : an orthogonal matrix as a linear isometry
  equivalence of `EuclideanSpace ℝ (Fin n)`; the linear ingredient of the first leg.
* `EuclideanGroup.toAffineIsometryHom` : the first leg, `⟨t, Q⟩ ↦ (x ↦ Q x + t)`.
* `AffineIsometryEquiv.toAffineEquivHom` : the second leg, `AffineIsometryEquiv.toAffineEquiv`
  as a monoid homomorphism.
* `EuclideanGroup.toAffineEquiv` : the composite of the two legs; the result intended for use
  elsewhere.

**Part 2: strengthening the first leg to an isomorphism.** Every affine isometry of
`EuclideanSpace ℝ (Fin n)` is `x ↦ Q x + t` for a unique orthogonal `Q` and translation `t`, so
the first leg is in fact a group isomorphism. We record it as
`EuclideanGroup.toAffineIsometryMulEquiv`, a `MulEquiv` whose fields are supplied as follows:

* `toFun`, `map_mul'` : reused from `EuclideanGroup.toAffineIsometryHom` in part 1;
* `invFun` : built from `EuclideanGroup.linearIsometryEquivToOrthogonal`, the inverse of the
  linear bridge `orthogonalToLinearIsometryEquiv`;
* `left_inv` : from the round trip `orthogonalToLinearIsometryEquiv_left_inv` together with the
  projection lemma `linearIsometryEquiv_constVAdd_mul`;
* `right_inv` : from the round trip `orthogonalToLinearIsometryEquiv_right_inv`.

Part 2 is self-contained; nothing in part 1 depends on it.
-/

@[expose] public section

variable {n : ℕ}

namespace EuclideanGroup

/-! ## Part 1: the inclusion

The chain is: `orthogonalToLinearIsometryEquiv` (linear ingredient) → `toAffineIsometryHom`
(first leg) → `AffineIsometryEquiv.toAffineEquivHom` (second leg) → `toAffineEquiv`
(the composite). -/

open scoped Matrix in
/-- An orthogonal matrix viewed as a linear isometry equivalence of `EuclideanSpace ℝ (Fin n)`;
the linear ingredient of the first leg `toAffineIsometryHom`. -/
noncomputable def orthogonalToLinearIsometryEquiv
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (DistribMulAction.toLinearEquiv ℝ (EuclideanSpace ℝ (Fin n)) Q).isometryOfInner fun x y => by
    simp only [DistribMulAction.toLinearEquiv_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    show (Q.val *ᵥ y.ofLp) ⬝ᵥ (Q.val *ᵥ x.ofLp) = y.ofLp ⬝ᵥ x.ofLp
    have hQ : (Q.val)ᵀ * Q.val = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp Q.property
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hQ, Matrix.vecMul_one]

@[simp] lemma orthogonalToLinearIsometryEquiv_apply
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalToLinearIsometryEquiv Q x = Q • x := rfl

/-- The first leg of the inclusion: `⟨t, Q⟩ ↦ (x ↦ Q x + t)`, bundled as a monoid homomorphism
from the Euclidean group into the affine isometry group of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def toAffineIsometryHom :
    EuclideanGroup n →*
      AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun A := AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) A.translation *
    (orthogonalToLinearIsometryEquiv A.linear).toAffineIsometryEquiv
  map_one' := by
    apply AffineIsometryEquiv.ext
    intro x; simp
  map_mul' A B := by
    apply AffineIsometryEquiv.ext
    intro x
    simp [mul_smul, add_assoc]

/-- Unfolds `toAffineIsometryHom` into its translation and linear factors. -/
@[simp] lemma toAffineIsometryHom_apply (A : EuclideanGroup n) :
    toAffineIsometryHom A =
      AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) A.translation *
        (orthogonalToLinearIsometryEquiv A.linear).toAffineIsometryEquiv := rfl

/-- The second leg of the inclusion: `AffineIsometryEquiv.toAffineEquiv` bundled as a monoid
homomorphism into the affine automorphism group. -/
noncomputable def _root_.AffineIsometryEquiv.toAffineEquivHom :
    AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) →*
      AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun e := e.toAffineEquiv
  map_one' := by
    apply AffineEquiv.ext; intro x; trivial
  map_mul' e e' := by
    apply AffineEquiv.ext; intro x; simp

/-- The inclusion of the Euclidean group into Mathlib's affine automorphism group: the composite
of the two legs `toAffineIsometryHom` and `AffineIsometryEquiv.toAffineEquivHom`. -/
noncomputable def toAffineEquiv :
    EuclideanGroup n →* AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  AffineIsometryEquiv.toAffineEquivHom.comp toAffineIsometryHom

/-! ## Part 2: strengthening the first leg to an isomorphism

The first leg `toAffineIsometryHom` is in fact a group isomorphism: every affine isometry of
`EuclideanSpace ℝ (Fin n)` is `x ↦ Q x + t` for a unique orthogonal `Q` and translation `t`. The
declarations below supply the remaining fields of the `MulEquiv` `toAffineIsometryMulEquiv`, in
field order: the `invFun` ingredient, the two lemmas proving `left_inv`, and the lemma proving
`right_inv`. Nothing in part 1 depends on this section. -/

/-- The `invFun` ingredient of `toAffineIsometryMulEquiv`: a linear isometry equivalence read back
as an orthogonal matrix, inverse to the linear bridge `orthogonalToLinearIsometryEquiv` (see the
round-trip `@[simp]` lemmas below). -/
noncomputable def linearIsometryEquivToOrthogonal
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.orthogonalGroup (Fin n) ℝ :=
   let b := EuclideanSpace.basisFun (Fin n) ℝ
   ⟨LinearMap.toMatrix b.toBasis b.toBasis L.toLinearEquiv, by
    have hb : LinearMap.toMatrix b.toBasis b.toBasis L.toLinearEquiv
        = b.toBasis.toMatrix (b.map L) := by
      ext i j
      simp [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.map_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    rw [hb]
    exact b.toMatrix_orthonormalBasis_mem_orthogonal (b.map L)⟩

/-- `linearIsometryEquivToOrthogonal` is a left inverse of `orthogonalToLinearIsometryEquiv`.
Together with `linearIsometryEquiv_constVAdd_mul`, this proves `left_inv` of
`toAffineIsometryMulEquiv`. -/
@[simp] lemma orthogonalToLinearIsometryEquiv_left_inv
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    linearIsometryEquivToOrthogonal (orthogonalToLinearIsometryEquiv Q) = Q := by
  apply Subtype.ext
  have hlin :
      ((orthogonalToLinearIsometryEquiv Q).toLinearEquiv :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
        = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Q.val := by
    ext x; rfl
  show LinearMap.toMatrix _ _
      ((orthogonalToLinearIsometryEquiv Q).toLinearEquiv :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = Q.val
  rw [hlin, LinearMap.toMatrix_toLin]

/-- The affine map `x ↦ t +ᵥ L x`, projected to its linear isometry component, is `L`.
Together with `orthogonalToLinearIsometryEquiv_left_inv`, this proves `left_inv` of
`toAffineIsometryMulEquiv`. -/
@[simp] lemma linearIsometryEquiv_constVAdd_mul
    (t : EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ((AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) t *
        L.toAffineIsometryEquiv).linearIsometryEquiv) = L := by
  apply LinearIsometryEquiv.ext; intro x
  have h := (AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) t *
      L.toAffineIsometryEquiv).map_vsub x 0
  rw [vsub_eq_sub, sub_zero] at h
  rw [h]
  simp

/-- `linearIsometryEquivToOrthogonal` is a right inverse of `orthogonalToLinearIsometryEquiv`;
this proves `right_inv` of `toAffineIsometryMulEquiv`. -/
@[simp] lemma orthogonalToLinearIsometryEquiv_right_inv
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    orthogonalToLinearIsometryEquiv (linearIsometryEquivToOrthogonal L) = L := by
    apply LinearIsometryEquiv.ext; intro x
    rw [orthogonalToLinearIsometryEquiv_apply]
    show Matrix.toEuclideanLin (linearIsometryEquivToOrthogonal L).val x = L x
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    show Matrix.toLin _ _
        (LinearMap.toMatrix _ _
          (L.toLinearEquiv : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) x = L x
    rw [Matrix.toLin_toMatrix]
    rfl

/-- `EuclideanGroup n ≃* AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) _`: the Euclidean group
is the full group of affine isometries of Euclidean space. This upgrades `toAffineIsometryHom` to
a group isomorphism with the same underlying map. -/
noncomputable def toAffineIsometryMulEquiv :
    EuclideanGroup n ≃*
      AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun := toAffineIsometryHom
  invFun e := ⟨e 0, linearIsometryEquivToOrthogonal e.linearIsometryEquiv⟩
  left_inv A := by
    refine EuclideanGroup.ext ?_ ?_
    · simp
    · simp [linearIsometryEquiv_constVAdd_mul, orthogonalToLinearIsometryEquiv_left_inv]
  right_inv e := by
    apply AffineIsometryEquiv.ext; intro x
    simp only [toAffineIsometryHom_apply,
      orthogonalToLinearIsometryEquiv_right_inv,
      AffineIsometryEquiv.coe_mul, Function.comp_apply,
      LinearIsometryEquiv.coe_toAffineIsometryEquiv,
      AffineIsometryEquiv.coe_constVAdd, vadd_eq_add]
    have h := e.map_vadd 0 x
    simp [vadd_eq_add, add_zero] at h
    rw [h, add_comm]
  map_mul' := toAffineIsometryHom.map_mul'

/-- `toAffineIsometryMulEquiv` agrees with `toAffineIsometryHom`. -/
@[simp] lemma toAffineIsometryMulEquiv_apply (A : EuclideanGroup n) :
    toAffineIsometryMulEquiv A = toAffineIsometryHom A := rfl

end EuclideanGroup
