/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.Matrix.Normed

/-!
# Maximal self-adjoint subrings

This file introduces the `IsMaximalSelfAdjoint R α` typeclass, which records that the
`TrivialStar` ring `R` carries the self-adjoint part of a star ring `α`. It bundles an
additive, `R`-linear map `selfadjMap : α →+ R` that inverts `algebraMap R α` on self-adjoint
elements. The guiding example is `R = ℝ`, `α = ℂ`: it lets a quantity such as the trace of a
Hermitian matrix be valued in `ℝ` instead of `ℂ`, reflecting that physical observables are
self-adjoint and take real expectation values.
-/

@[expose] public section

/-- `IsMaximalSelfAdjoint R α` witnesses that `R` is the maximal `TrivialStar` subring of the
star ring `α`, via an additive map `selfadjMap : α →+ R` collecting the self-adjoint part of
each element. This lets `HermitianMat.trace` return `𝕜` when `𝕜` already has a trivial star,
and the "clean" underlying type otherwise, e.g. `ℝ` when the input field is `ℂ`. -/
class IsMaximalSelfAdjoint (R : outParam Type*) (α : Type*) [Star α] [Star R] [CommSemiring R]
    [Semiring α] [TrivialStar R] [Algebra R α] where
  /-- The additive map sending an element of `α` to its self-adjoint part in `R`. -/
  selfadjMap : α →+ R
  /-- `selfadjMap` pulls scalar multiplication by `R` out of its argument. -/
  selfadj_smul : ∀ (r : R) (a : α), selfadjMap (r • a) = r * (selfadjMap a)
  /-- On self-adjoint elements, `selfadjMap` is a section of `algebraMap R α`. -/
  selfadj_algebra : ∀ {a : α}, IsSelfAdjoint a → algebraMap _ _ (selfadjMap a) = a

/-- Every `TrivialStar` `CommSemiring` is its own maximal self adjoints. -/
instance instTrivialStar_IsMaximalSelfAdjoint {R} [Star R] [TrivialStar R] [CommSemiring R] :
    IsMaximalSelfAdjoint R R where
  selfadjMap := AddMonoidHom.id R
  selfadj_smul _ __ := rfl
  selfadj_algebra {_} _ := rfl

/-- ℝ is the maximal self adjoint elements over RCLike -/
instance instRCLike_IsMaximalSelfAdjoint {α} [RCLike α] : IsMaximalSelfAdjoint ℝ α where
  selfadjMap := RCLike.re
  selfadj_smul := RCLike.smul_re
  selfadj_algebra := RCLike.conj_eq_iff_re.mp

namespace IsMaximalSelfAdjoint

-- In particular instances we care about, simplify selfadjMap should it appear.
-- It _seems_ like `selfadjMap 1 = 1`, always, but I can't find a proof. But these lemmas
-- take care of proving that anyway.

@[simp]
theorem trivial_selfadjMap {R} [Star R] [TrivialStar R] [CommSemiring R] :
    (selfadjMap : R →+ R) = .id R := by
  rfl

@[simp]
theorem RCLike_selfadjMap {α} [RCLike α] : (selfadjMap : α →+ ℝ) = RCLike.re := by
  rfl

end IsMaximalSelfAdjoint
