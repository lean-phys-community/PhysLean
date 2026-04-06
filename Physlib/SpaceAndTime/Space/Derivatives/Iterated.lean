/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.MultiIndex
/-!
# Iterated derivatives on `Space d`

## i. Overview

This module defines iterated coordinate derivatives on `Space d` indexed by multi-indices.

The implementation is intentionally modest. A multi-index is first expanded into a canonical list
of coordinate directions, and the iterated derivative is then defined by repeated application of
`Space.deriv` along that list.

## ii. Key results

- `Physlib.MultiIndex.toList` : the canonical ordered list of directions encoded by a multi-index.
- `Space.iteratedDeriv` : iterated coordinate derivatives on `Space d`.

## iii. Table of contents

- A. The combinatorics of iterated directions
- B. Iterated derivatives on `Space d`

## iv. References

-/

@[expose] public section

namespace Physlib

namespace MultiIndex

variable {d : ℕ}

/-!
## A. The combinatorics of iterated directions

-/

/-- The tail of a multi-index on `d + 1` coordinates, dropping the `0`-th coordinate. -/
def tail (I : MultiIndex d.succ) : MultiIndex d := ⟨fun i => I i.succ⟩

/-- The canonical ordered list of coordinate directions encoded by a multi-index. -/
def toList : {d : ℕ} → MultiIndex d → List (Fin d)
  | 0, _ => []
  | _ + 1, I => List.replicate (I 0) 0 ++ (toList (tail I)).map Fin.succ

@[simp]
lemma tail_zero : tail (0 : MultiIndex d.succ) = 0 := by
  ext i
  rfl

@[simp]
lemma tail_increment_zero (I : MultiIndex d.succ) : tail (increment I 0) = tail I := by
  ext i
  simp [tail, increment]

@[simp]
lemma tail_increment_succ (I : MultiIndex d.succ) (i : Fin d) :
    tail (increment I i.succ) = increment (tail I) i := by
  ext j
  by_cases h : j = i
  · subst h
    simp [tail, increment]
  · simp [tail, increment, h]

@[simp]
lemma toList_zero : toList (0 : MultiIndex d) = [] := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [toList, ih]

lemma length_toList (I : MultiIndex d) : I.toList.length = I.order := by
  induction d with
  | zero =>
      simp [toList, MultiIndex.order]
  | succ d ih =>
      simp [toList, tail, MultiIndex.order, Fin.sum_univ_succ, ih]

@[simp]
lemma toList_increment_zero (I : MultiIndex d.succ) :
    toList (increment I 0) = 0 :: toList I := by
  simp only [toList, increment_apply_same, tail_increment_zero]
  rw [show I 0 + 1 = 1 + I 0 by omega, List.replicate_add]
  simp

@[simp]
lemma toList_single (i : Fin d) : toList (increment 0 i : MultiIndex d) = [i] := by
  induction d with
  | zero =>
      exact Fin.elim0 i
  | succ d ih =>
      refine Fin.cases ?_ ?_ i
      · simp [toList_increment_zero]
      · intro j
        have htail :
            tail (increment (0 : MultiIndex d.succ) j.succ) = increment (0 : MultiIndex d) j := by
          rw [tail_increment_succ, tail_zero]
        have hzero : increment (0 : MultiIndex d.succ) j.succ 0 = 0 := by
          simp [increment]
        simp [toList, hzero, htail, ih j]

end MultiIndex

end Physlib

namespace Space

open Physlib

variable {M : Type} {d : ℕ}

/-!
## B. Iterated derivatives on `Space d`

-/

/-- The iterated coordinate derivative on `Space d` indexed by a multi-index. -/
noncomputable def iteratedDeriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (I : MultiIndex d) (f : Space d → M) : Space d → M :=
  I.toList.foldr (fun i g => deriv i g) f

@[simp]
lemma iteratedDeriv_zero [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Space d → M) : iteratedDeriv (0 : MultiIndex d) f = f := by
  simp [iteratedDeriv, Physlib.MultiIndex.toList_zero]

@[simp]
lemma iteratedDeriv_increment_zero [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (I : MultiIndex d.succ) (f : Space d.succ → M) :
    iteratedDeriv (MultiIndex.increment I 0) f = ∂[0] (iteratedDeriv I f) := by
  simp [iteratedDeriv, Physlib.MultiIndex.toList_increment_zero]

@[simp]
lemma iteratedDeriv_single [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (i : Fin d) (f : Space d → M) :
    iteratedDeriv (MultiIndex.increment 0 i) f = ∂[i] f := by
  simp [iteratedDeriv, Physlib.MultiIndex.toList_single]

end Space
