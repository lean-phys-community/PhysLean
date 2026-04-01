 /-
 Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Juan Jose Fernandez Morales
 -/
 
 module
 
 public import Mathlib.Algebra.BigOperators.Pi
 /-!
 # Multi-indices
 
 ## i. Overview
 
 This module defines the basic type of multi-indices used to index iterated partial derivatives.
 
 The implementation is intentionally minimal. A multi-index on `n` source coordinates is represented
 as a function `Fin n → Nat`, together with the first basic operations needed later in the local
 Classical Field Theory development.
 
 ## ii. Key results
 
 - `Physlib.MultiIndex` : multi-indices on `n` coordinates.
 - `MultiIndex.order` : the order `|I|` of a multi-index.
 - `MultiIndex.increment` : increment a single coordinate of a multi-index.
 
 ## iii. Table of contents
 
 - A. The basic type of multi-indices
   - A.1. Basic operations
   - A.2. Basic lemmas
 
 ## iv. References
 
 -/
 
 @[expose] public section
 
 open scoped BigOperators
 
 namespace Physlib
 
 /-!
 ## A. The basic type of multi-indices
 
 -/
 
 /-- A multi-index on `n` source coordinates. -/
 abbrev MultiIndex (n : ℕ) := Fin n → ℕ
 
 namespace MultiIndex
 
 variable {n : ℕ}
 
 instance : DecidableEq (MultiIndex n) := inferInstance
 
 /-!
 ### A.1. Basic operations
 
 -/
 
 /-- The order `|I|` of a multi-index `I`, defined as the sum of its components. -/
 def order (I : MultiIndex n) : Nat := ∑ i, I i
 
 /-- Increment the `i`-th coordinate of a multi-index by one. -/
 def increment (I : MultiIndex n) (i : Fin n) : MultiIndex n := I + Pi.single i 1
 
 /-!
 ### A.2. Basic lemmas
 
 -/
 
 @[ext]
 lemma ext {I J : MultiIndex n} (h : ∀ i, I i = J i) : I = J := funext h
 
 @[simp]
 lemma zero_apply (i : Fin n) : (0 : MultiIndex n) i = 0 := rfl
 
 @[simp]
 lemma increment_apply_same (I : MultiIndex n) (i : Fin n) :
     increment I i i = I i + 1 := by
   simp [increment]
 
 @[simp]
 lemma increment_apply_ne (I : MultiIndex n) {i j : Fin n} (h : j ≠ i) :
     increment I i j = I j := by
   simp [increment, Pi.single_eq_of_ne h]
 
 @[simp]
 lemma order_zero : order (0 : MultiIndex n) = 0 := by
   simp [order]
 
 lemma order_add (I J : MultiIndex n) : order (I + J) = order I + order J := by
   simp [order, Finset.sum_add_distrib]
 
 @[simp]
 lemma order_single (i : Fin n) : order (Pi.single i 1 : MultiIndex n) = 1 := by
   classical
   unfold order
   rw [Finset.sum_eq_single i]
   · simp
   · intro j _ hj
     simp [Pi.single_eq_of_ne hj]
   · intro hi
     simp at hi
 
 @[simp]
 lemma order_increment (I : MultiIndex n) (i : Fin n) :
     order (increment I i) = order I + 1 := by
   rw [increment, order_add, order_single]
 
 end MultiIndex
 
 end Physlib
