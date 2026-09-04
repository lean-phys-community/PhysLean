/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Positive
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Effects

Effects are observables whose possible values lie between `0` and `1`. They describe individual
outcomes of general quantum measurements.
-/

@[expose] public section
namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A quantum effect: an observable between `0` and `1`. -/
abbrev Effect (A : Type*) [OperatorAlgebra A] := Set.Icc (0 : Observable A) 1

namespace Observable

/-! ## A. Spectral characterization -/

/-- An observable is an effect exactly when its spectrum lies in `[0, 1]`. -/
lemma mem_effect_iff_spectrum_subset (a : Observable A) :
    a ∈ Set.Icc (0 : Observable A) 1 ↔
      spectrum ℝ (a : A) ⊆ Set.Icc 0 1 := by
  constructor
  · rintro ⟨ha₀, ha₁⟩ x hx
    exact ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a : A) a.property).mp
        ha₀ x hx,
      (CFC.le_one_iff (R := ℝ) (a : A) a.property).mp ha₁ x hx⟩
  · intro ha
    exact ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a : A) a.property).mpr
        fun x hx => (ha hx).1,
      (CFC.le_one_iff (R := ℝ) (a : A) a.property).mpr fun x hx => (ha hx).2⟩

end Observable

namespace Effect

/-! ## B. Constructors and complement -/

/-- A continuous `[0,1]`-valued function of an observable is an effect. -/
noncomputable def ofFunctionalCalculus (f : C(ℝ, ℝ)) (a : Observable A)
    (hf : Set.MapsTo f (spectrum ℝ (a : A)) (Set.Icc 0 1)) : Effect A := by
  let b : Observable A := ⟨cfc f (a : A), cfc_predicate f (a : A)⟩
  refine ⟨b, ?_, ?_⟩
  · change 0 ≤ cfc (f : ℝ → ℝ) (a : A)
    exact (cfc_nonneg_iff (p := IsSelfAdjoint) (f : ℝ → ℝ) (a : A)
      f.continuous.continuousOn a.property).mpr fun _ hx => (hf hx).1
  · change cfc (f : ℝ → ℝ) (a : A) ≤ 1
    exact (cfc_le_one_iff (p := IsSelfAdjoint) (f : ℝ → ℝ) (a : A)
      f.continuous.continuousOn a.property).mpr fun _ hx => (hf hx).2

/-- The complementary effect `1 - E`. -/
noncomputable def complement (E : Effect A) : Effect A :=
  ⟨1 - E.1, sub_nonneg.mpr E.2.2,
    sub_le_self 1 (show (0 : Observable A) ≤ E.1 from E.2.1)⟩

/-- Taking the complement twice returns the original effect. -/
@[simp]
lemma complement_complement (E : Effect A) : complement (complement E) = E := by
  apply Subtype.ext
  simp [complement]

end Effect

end OperatorAlgebra
