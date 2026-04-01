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
`Space n → Space m`. This reuses the existing `IsTestFunction` predicate rather than introducing a
second support calculus.

## ii. Key results

- `ClassicalFieldTheory.Local.AdmissibleVariation` : compactly supported smooth variations.
- `ClassicalFieldTheory.Local.IsAdmissibleVariation` : predicate form of the same notion.

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

/-- Predicate form of admissible local variations. -/
abbrev IsAdmissibleVariation (η : Space n → Space m) : Prop := IsTestFunction η

/-- An admissible local variation is a smooth compactly supported map `Space n → Space m`. -/
structure AdmissibleVariation (n m : ℕ) where
  toFun : Space n → Space m
  isAdmissible : IsAdmissibleVariation toFun

namespace AdmissibleVariation

variable {n m : ℕ}

/-!
## B. Basic operations on admissible variations

-/

instance : CoeFun (AdmissibleVariation n m) (fun _ => Space n → Space m) where
  coe η := η.toFun

/-- The underlying test-function property of an admissible variation. -/
lemma isTestFunction (η : AdmissibleVariation n m) : IsTestFunction (η.toFun) := η.isAdmissible

lemma hasCompactSupport (η : AdmissibleVariation n m) : HasCompactSupport (η.toFun) :=
  η.isTestFunction.supp

noncomputable def toCompactlySupportedContinuousMap (η : AdmissibleVariation n m) :
    CompactlySupportedContinuousMap (Space n) (Space m) :=
  η.isTestFunction.toCompactlySupportedContinuousMap

/-- The zero admissible variation. -/
noncomputable def zero : AdmissibleVariation n m where
  toFun := fun _ => 0
  isAdmissible := IsTestFunction.zero

noncomputable instance : Zero (AdmissibleVariation n m) := ⟨zero⟩

@[simp]
lemma zero_apply (x : Space n) : (0 : AdmissibleVariation n m) x = 0 := rfl

/-- Negation of admissible variations. -/
noncomputable def neg (η : AdmissibleVariation n m) : AdmissibleVariation n m where
  toFun := fun x => -η x
  isAdmissible := η.isTestFunction.neg

noncomputable instance : Neg (AdmissibleVariation n m) := ⟨neg⟩

@[simp]
lemma neg_apply (η : AdmissibleVariation n m) (x : Space n) : (-η) x = -η x := rfl

/-- Sum of admissible variations. -/
noncomputable def add (η ξ : AdmissibleVariation n m) : AdmissibleVariation n m where
  toFun := fun x => η x + ξ x
  isAdmissible := η.isTestFunction.add ξ.isTestFunction

noncomputable instance : Add (AdmissibleVariation n m) := ⟨add⟩

@[simp]
lemma add_apply (η ξ : AdmissibleVariation n m) (x : Space n) : (η + ξ) x = η x + ξ x := rfl

/-- Difference of admissible variations. -/
noncomputable def sub (η ξ : AdmissibleVariation n m) : AdmissibleVariation n m where
  toFun := fun x => η x - ξ x
  isAdmissible := η.isTestFunction.sub ξ.isTestFunction

noncomputable instance : Sub (AdmissibleVariation n m) := ⟨sub⟩

@[simp]
lemma sub_apply (η ξ : AdmissibleVariation n m) (x : Space n) : (η - ξ) x = η x - ξ x := rfl

/-- Scalar multiples of admissible variations by real constants are admissible. -/
noncomputable def smul (c : ℝ) (η : AdmissibleVariation n m) : AdmissibleVariation n m where
  toFun := fun x => c • η x
  isAdmissible := IsTestFunction.smul_left (f := fun _ : Space n => c) (g := η.toFun)
    (by fun_prop) η.isTestFunction

noncomputable instance : SMul ℝ (AdmissibleVariation n m) := ⟨smul⟩

@[simp]
lemma smul_apply (c : ℝ) (η : AdmissibleVariation n m) (x : Space n) :
    (c • η) x = c • η x := rfl

lemma coord (η : AdmissibleVariation n m) (a : Fin m) :
    IsTestFunction (fun x => (η.toFun x).coord a) := by
  simpa [Space.coord] using IsTestFunction.coord η.isTestFunction a

end AdmissibleVariation

end Local
end ClassicalFieldTheory
