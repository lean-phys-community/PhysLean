/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/

module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Multi-indices

## i. Overview

This module defines the basic type of multi-indices used to index iterated partial derivatives.

A multi-index on `d` source coordinates is represented as a structure with an underlying function
`Fin d → ℕ`, together with the first basic operations needed later in the local Classical Field
Theory development.

## ii. Key results

- `Physlib.MultiIndex` : multi-indices on `d` coordinates.
- `MultiIndex.order` : the order `|I|` of a multi-index.
- `MultiIndex.increment` : increment a single coordinate of a multi-index.
- `MultiIndex.toList` : the canonical ordered list of directions encoded by a multi-index.

## iii. Table of contents

- A. The basic type of multi-indices
  - A.1. Basic operations
  - A.2. Basic lemmas
  - A.3. Canonical ordered lists of directions

## iv. References

-/

@[expose] public section

open scoped BigOperators

namespace Physlib

/-!
## A. The basic type of multi-indices

-/

/-- A multi-index on `d` source coordinates. -/
structure MultiIndex (d : ℕ) where
  /-- The coordinates of the multi-index. -/
  toFun : Fin d → ℕ
deriving DecidableEq

namespace MultiIndex

variable {d : ℕ}

instance : CoeFun (MultiIndex d) (fun _ => Fin d → ℕ) := ⟨MultiIndex.toFun⟩

instance : Zero (MultiIndex d) := ⟨⟨0⟩⟩

instance : Add (MultiIndex d) := ⟨fun I J => ⟨I.toFun + J.toFun⟩⟩

/-!
### A.1. Basic operations

-/

/-- The order `|I|` of a multi-index `I`, defined as the sum of its components. -/
def order (I : MultiIndex d) : Nat := ∑ i, I i

/-- Increment the `i`-th coordinate of a multi-index by one. -/
def increment (I : MultiIndex d) (i : Fin d) : MultiIndex d := ⟨I.toFun + Pi.single i 1⟩

/-!
### A.2. Basic lemmas

-/

@[ext]
lemma ext {I J : MultiIndex d} (h : ∀ i, I i = J i) : I = J := by
  cases I
  cases J
  simp only at h
  congr
  funext i
  exact h i

@[simp]
lemma zero_apply (i : Fin d) : (0 : MultiIndex d) i = 0 := rfl

@[simp]
lemma add_apply (I J : MultiIndex d) (i : Fin d) : (I + J) i = I i + J i := rfl

@[simp]
lemma increment_apply_same (I : MultiIndex d) (i : Fin d) :
    increment I i i = I i + 1 := by
  simp [increment]

@[simp]
lemma increment_apply_ne (I : MultiIndex d) {i j : Fin d} (h : j ≠ i) :
    increment I i j = I j := by
  simp [increment, Pi.single_eq_of_ne h]

@[simp]
lemma order_zero : order (0 : MultiIndex d) = 0 := by
  simp [order]

lemma order_add (I J : MultiIndex d) : order (I + J) = order I + order J := by
  simp [order, Finset.sum_add_distrib]

@[simp]
lemma order_single (i : Fin d) : order (⟨Pi.single i 1⟩ : MultiIndex d) = 1 := by
  classical
  unfold order
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    simp at hi

@[simp]
lemma order_increment (I : MultiIndex d) (i : Fin d) :
    order (increment I i) = order I + 1 := by
  simp [increment, order, Finset.sum_add_distrib]

/-!
### A.3. Canonical ordered lists of directions

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
