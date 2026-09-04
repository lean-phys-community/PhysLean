/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Effects
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Projection observables

Projections are the sharp effects: their only possible spectral values are `0` and `1`. This file
packages projections as observables and effects, together with their complements and spectrum.
-/

@[expose] public section
namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A projection observable: a self-adjoint idempotent element of the observable algebra. -/
abbrev Projection (A : Type*) [OperatorAlgebra A] := {p : A // IsStarProjection p}

namespace Projection

/-! ## A. Projections as sharp effects -/

/-- The observable underlying a projection. -/
def toObservable (p : Projection A) : Observable A :=
  ⟨p, p.property.isSelfAdjoint⟩

/-- Every projection determines an effect. -/
def toEffect (p : Projection A) : Effect A :=
  ⟨toObservable p, p.property.nonneg, p.property.le_one⟩

/-- The real spectrum of a projection is contained in `{0, 1}`. -/
lemma spectrum_subset_zero_one (p : Projection A) :
    spectrum ℝ (p : A) ⊆ {0, 1} :=
  (isStarProjection_iff_spectrum_subset_and_isSelfAdjoint.mp p.property).1

/-! ## B. Complement -/

/-- The complementary projection `1 - p`. -/
def complement (p : Projection A) : Projection A :=
  ⟨1 - p, p.property.one_sub⟩

/-- Taking the complement twice returns the original projection. -/
@[simp]
lemma complement_complement (p : Projection A) : complement (complement p) = p := by
  apply Subtype.ext
  simp [complement]

end Projection

end OperatorAlgebra
