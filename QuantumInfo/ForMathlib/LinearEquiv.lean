/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Relabelling linear equivalences

## i. Overview

This module provides linear equivalences obtained by relabelling the index type of a finite
function space `d → R` or of `EuclideanSpace 𝕜 d` along an index equivalence `e : d ≃ d₂`,
together with lemmas relating them to `Matrix.reindex`.

## ii. Key results

- `LinearEquiv.of_relabel` : the `R`-linear equivalence `(d₂ → R) ≃ₗ[R] (d → R)` induced by an
  index equivalence `e : d ≃ d₂`.
- `LinearEquiv.euclidean_of_relabel` : the `EuclideanSpace` analogue of `of_relabel`.
- `Matrix.reindex_toLin'` and `Matrix.reindex_toEuclideanLin` : reindexing a matrix conjugates
  its associated linear map by these relabelling equivalences.

## iii. Table of contents

This can be filled in later.

## iv. References

-/

@[expose] public section

variable {d d₁ d₂ d₃ R 𝕜 : Type*} [RCLike 𝕜]

namespace LinearEquiv

variable {R : Type*} [Semiring R]

variable (R) in
/-- The `R`-linear equivalence `(d₂ → R) ≃ₗ[R] (d → R)` that relabels the coordinates of a
function along an index equivalence `e : d ≃ d₂`. This is the linear-equivalence packaging of
`Equiv.piCongrLeft`. -/
@[simps]
def of_relabel (e : d ≃ d₂) : (d₂ → R) ≃ₗ[R] (d → R) := by
  refine' { e.symm.piCongrLeft (fun _ ↦ R) with .. }
  <;> (intros; ext; simp [Equiv.piCongrLeft_apply])

variable (e : d ≃ d₂)

variable (𝕜) in
/-- The `𝕜`-linear equivalence `EuclideanSpace 𝕜 d₂ ≃ₗ[𝕜] EuclideanSpace 𝕜 d` that relabels the
coordinates of a vector along an index equivalence `e : d ≃ d₂`. This is the `EuclideanSpace`
analogue of `LinearEquiv.of_relabel`, obtained by transporting it across the `WithLp`
identifications. -/
@[simps!]
def euclidean_of_relabel (e : d ≃ d₂) : EuclideanSpace 𝕜 d₂ ≃ₗ[𝕜] EuclideanSpace 𝕜 d :=
  (WithLp.linearEquiv 2 𝕜 _).trans ((of_relabel _ e).trans (WithLp.linearEquiv 2 𝕜 _).symm)

@[simp]
theorem of_relabel_refl : of_relabel R (.refl d) = LinearEquiv.refl R (d → R) := by
  rfl

@[simp]
theorem euclidean_of_relabel_refl : euclidean_of_relabel 𝕜 (.refl d) =
    LinearEquiv.refl 𝕜 (EuclideanSpace 𝕜 d) := by
  rfl

end LinearEquiv

namespace Matrix

variable {R : Type*} [CommSemiring R]
variable [Fintype d] [DecidableEq d]
variable [Fintype d₂] [DecidableEq d₂]

theorem reindex_toLin' (e : d₁ ≃ d₃) (f : d₂ ≃ d) (M : Matrix d₁ d₂ R) :
    (M.reindex e f).toLin' = (LinearEquiv.of_relabel R e.symm) ∘ₗ
      M.toLin' ∘ₗ (LinearEquiv.of_relabel R f) := by
  ext
  simp [mulVec, dotProduct, Equiv.piCongrLeft_apply]

theorem reindex_toEuclideanLin (e : d₁ ≃ d₃) (f : d₂ ≃ d) (M : Matrix d₁ d₂ 𝕜) :
    (M.reindex e f).toEuclideanLin = (LinearEquiv.euclidean_of_relabel 𝕜 e.symm) ∘ₗ
      M.toEuclideanLin ∘ₗ (LinearEquiv.euclidean_of_relabel 𝕜 f) := by
  ext
  simp [mulVec, dotProduct, Equiv.piCongrLeft_apply]

theorem reindex_right_toLin' (e : d ≃ d₂) (M : Matrix d₃ d R) :
    (M.reindex (.refl d₃) e).toLin' = M.toLin' ∘ₗ (LinearEquiv.of_relabel R e) := by
  rw [reindex_toLin']
  simp

theorem reindex_right_toEuclideanLin (e : d ≃ d₂) (M : Matrix d₃ d 𝕜) :
    (M.reindex (.refl d₃) e).toEuclideanLin =
      M.toEuclideanLin ∘ₗ (LinearEquiv.euclidean_of_relabel 𝕜 e) := by
  ext
  simp [mulVec, dotProduct, Equiv.piCongrLeft_apply]

theorem reindex_left_toLin' (e : d₁ ≃ d₃) (M : Matrix d₁ d₂ R) :
    (M.reindex e (.refl d₂)).toLin' = (LinearEquiv.of_relabel R e.symm) ∘ M.toLin' := by
  rw [Matrix.reindex_toLin']
  simp

theorem reindex_left_toEuclideanLin (e : d₁ ≃ d₃) (M : Matrix d₁ d₂ 𝕜) :
    (M.reindex e (.refl d₂)).toEuclideanLin =
      (LinearEquiv.euclidean_of_relabel 𝕜 e.symm) ∘ M.toEuclideanLin := by
  rw [Matrix.reindex_toEuclideanLin]
  simp

end Matrix
