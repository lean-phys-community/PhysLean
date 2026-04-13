/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.Mathematics.VariationalCalculus.IsTestFunction
/-!
# Admissible local variations

## i. Overview

This module packages the admissible variations used in the local first-variation problem.

For the first local stage, a variation is admissible if it is a smooth compactly supported map
`Space d → U` for a real normed vector space `U`. This reuses the existing `IsTestFunction`
predicate rather than introducing a second support calculus.

## ii. Key results

- `ClassicalFieldTheory.Local.AdmissibleVariation` : compactly supported smooth variations.

## iii. Table of contents

- A. Admissible variations
- B. Basic operations on admissible variations

## iv. References

-/

@[expose] public section

open MeasureTheory
open Physlib

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Admissible variations

-/

/-- An admissible local variation is a smooth compactly supported map `Space d → U`. -/
structure AdmissibleVariation (d : ℕ) (U : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U] where
  /-- The underlying variation function. -/
  toFun : Space d → U
  /-- Smoothness and compact support of the variation. -/
  isTestFunction : IsTestFunction toFun

namespace AdmissibleVariation

variable {d : ℕ} {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]

/-!
## B. Basic operations on admissible variations

-/

instance : CoeFun (AdmissibleVariation d U) (fun _ => Space d → U) where
  coe η := η.toFun

attribute [fun_prop] AdmissibleVariation.isTestFunction

/-- An admissible variation has compact support. -/
lemma hasCompactSupport (η : AdmissibleVariation d U) : HasCompactSupport (η.toFun) :=
  η.isTestFunction.supp

/-- View an admissible variation as a compactly supported continuous map. -/
noncomputable def toCompactlySupportedContinuousMap (η : AdmissibleVariation d U) :
    CompactlySupportedContinuousMap (Space d) U :=
  η.isTestFunction.toCompactlySupportedContinuousMap

noncomputable instance : Zero (AdmissibleVariation d U) where
  zero :=
    { toFun := fun _ => 0
      isTestFunction := IsTestFunction.zero }

@[simp]
lemma zero_apply (x : Space d) : (0 : AdmissibleVariation d U) x = 0 := rfl

noncomputable instance : Neg (AdmissibleVariation d U) where
  neg η :=
    { toFun := fun x => -η x
      isTestFunction := η.isTestFunction.neg }

@[simp]
lemma neg_apply (η : AdmissibleVariation d U) (x : Space d) : (-η) x = -η x := rfl

noncomputable instance : Add (AdmissibleVariation d U) where
  add η ξ :=
    { toFun := fun x => η x + ξ x
      isTestFunction := η.isTestFunction.add ξ.isTestFunction }

@[simp]
lemma add_apply (η ξ : AdmissibleVariation d U) (x : Space d) : (η + ξ) x = η x + ξ x := rfl

noncomputable instance : Sub (AdmissibleVariation d U) where
  sub η ξ :=
    { toFun := fun x => η x - ξ x
      isTestFunction := η.isTestFunction.sub ξ.isTestFunction }

@[simp]
lemma sub_apply (η ξ : AdmissibleVariation d U) (x : Space d) : (η - ξ) x = η x - ξ x := rfl

noncomputable instance : SMul ℝ (AdmissibleVariation d U) where
  smul c η :=
    { toFun := fun x => c • η x
      isTestFunction := IsTestFunction.smul_left (f := fun _ : Space d => c) (g := η.toFun)
        (by fun_prop) η.isTestFunction }

@[simp]
lemma smul_apply (c : ℝ) (η : AdmissibleVariation d U) (x : Space d) :
    (c • η) x = c • η x := rfl

@[fun_prop]
lemma coord {m : ℕ} (η : AdmissibleVariation d (Space m)) (a : Fin m) :
    IsTestFunction (fun x => (η.toFun x).coord a) := by
  simpa [Space.coord] using IsTestFunction.coord η.isTestFunction a

end AdmissibleVariation

end Local
end ClassicalFieldTheory
