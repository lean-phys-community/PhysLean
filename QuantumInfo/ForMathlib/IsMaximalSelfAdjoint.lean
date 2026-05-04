/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/- We want to have `HermitianMat.trace` give 𝕜 when 𝕜 is already a TrivialStar field, but give the "clean" type
otherwise -- for instance, ℝ when the input field is ℂ. This typeclass lets us do so. -/
class IsMaximalSelfAdjoint (R : outParam Type*) (α : Type*) [Star α] [Star R] [CommSemiring R]
    [Semiring α] [TrivialStar R] [Algebra R α] where
  selfadjMap : α →+ R
  selfadj_smul : ∀ (r : R) (a : α), selfadjMap (r • a) = r * (selfadjMap a)
  selfadj_algebra : ∀ {a : α}, IsSelfAdjoint a → algebraMap _ _ (selfadjMap a) = a

/-- Every `TrivialStar` `CommSemiring` is its own maximal self adjoints. -/
instance instTrivialStar_IsMaximalSelfAdjoint {R} [Star R] [TrivialStar R] [CommSemiring R] : IsMaximalSelfAdjoint R R where
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
theorem trivial_selfadjMap {R} [Star R] [TrivialStar R] [CommSemiring R] : (selfadjMap : R →+ R) = .id R := by
  rfl

@[simp]
theorem RCLike_selfadjMap {α} [RCLike α] : (selfadjMap : α →+ ℝ) = RCLike.re := by
  rfl

end IsMaximalSelfAdjoint
