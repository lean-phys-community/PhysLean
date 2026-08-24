/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Physlib.SpaceAndTime.Space.Derivatives.MultiIndex
/-!
# Bounded derivative indices

## i. Overview

This module defines bounded derivative indices on `Space d`, i.e. multi-indices of total order at
most `k`.

These are the finite indexing objects used later for finite-order local jet coordinates, while
remaining independent of any specific jet or field-theory construction.

## ii. Key results

- `Physlib.DerivativeIndex`

## iii. Table of contents

- A. Definition and basic instances

## iv. References

-/

@[expose] public section

namespace Physlib

/-!
## A. Definition and basic instances

-/

/-- The multi-indices on `d` coordinates of order at most `k`. -/
abbrev DerivativeIndex (d k : ℕ) := { I : MultiIndex d // I.order ≤ k }

noncomputable instance (d k : ℕ) : Fintype (DerivativeIndex d k) :=
  Fintype.ofInjective
    (fun I : DerivativeIndex d k => fun i : Fin d =>
      ((⟨I.1 i, by
        have hle_order : I.1 i ≤ I.1.order := by
          classical
          unfold Physlib.MultiIndex.order
          simpa using
            (Finset.single_le_sum (fun j _ => Nat.zero_le (I.1 j)) (by simp : i ∈ Finset.univ) :
              I.1 i ≤ ∑ j : Fin d, I.1 j)
        exact Nat.lt_succ_of_le (le_trans hle_order I.2)⟩) : Fin (k + 1)))
    (by
      intro I J h
      apply Subtype.ext
      apply Physlib.MultiIndex.ext
      intro i
      exact congrArg Fin.val (congrFun h i))

instance (d k : ℕ) : DecidableEq (DerivativeIndex d k) := inferInstance

instance (d k : ℕ) : Zero (DerivativeIndex d k) where
  zero := ⟨0, by simp [Physlib.MultiIndex.order_zero]⟩

namespace DerivativeIndex

@[simp]
lemma coe_zero (d k : ℕ) :
    ((0 : DerivativeIndex d k) : MultiIndex d) = 0 := rfl

@[simp]
lemma zero_apply (d k : ℕ) (i : Fin d) :
    ((0 : DerivativeIndex d k) : MultiIndex d) i = 0 := rfl

end DerivativeIndex

end Physlib
