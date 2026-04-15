/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Iterated
/-!
# Local jets

## i. Overview

This module introduces the core local jet object for fields on `Space d` with values in `Space m`.

At this first stage, a `k`-jet is represented only by:

- its base point,
- its field value,
- and its derivative coordinates indexed by multi-indices of order at most `k`.

The explicit coordinate conversions and the evaluation of jets of fields are added in follow-up PRs.

## ii. Key results

- `ClassicalFieldTheory.Local.DerivativeIndex`
- `ClassicalFieldTheory.Local.JetCoordinates`
- `ClassicalFieldTheory.Local.LocalJet`

## iii. Table of contents

- A. Derivative indices
- B. Local jets

## iv. References

-/

@[expose] public section

open Physlib

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Derivative indices

-/

/-- The multi-indices on `d` coordinates of order at most `k`. -/
abbrev DerivativeIndex (d k : ℕ) := { I : MultiIndex d // I.order ≤ k }

/-- Coordinate data `u^a_I` for local jets of order `k`. -/
abbrev JetCoordinates (d m k : ℕ) := DerivativeIndex d k → Fin m → ℝ

/-- The zero multi-index as a derivative index of any order. -/
def zeroIndex (d k : ℕ) : DerivativeIndex d k := ⟨0, by simp [Physlib.MultiIndex.order_zero]⟩

/-!
## B. Local jets

-/

/-- Local jets of order `k` for fields `Space d → Space m`. -/
structure LocalJet (d m k : ℕ) where
  /-- The base point of the jet. -/
  base : Space d
  /-- The field value. -/
  value : Space m
  /-- The derivative coordinates indexed by all multi-indices of order at most `k`. -/
  deriv : JetCoordinates d m k
  /-- Compatibility between the explicit field value and the zero-th order jet coordinate. -/
  value_eq_zeroIndex : ∀ a : Fin m, deriv (zeroIndex d k) a = value a

namespace LocalJet

variable {d m k : ℕ}

@[ext]
lemma ext (J K : LocalJet d m k) (hbase : J.base = K.base) (hvalue : J.value = K.value)
    (hderiv : J.deriv = K.deriv) : J = K := by
  cases J
  cases K
  cases hbase
  cases hvalue
  cases hderiv
  rfl

/-- The derivative coordinate of a jet. -/
def coord (J : LocalJet d m k) (I : DerivativeIndex d k) (a : Fin m) : ℝ := J.deriv I a

@[simp]
lemma value_eq_coord_zeroIndex (J : LocalJet d m k) (a : Fin m) :
    J.value a = J.coord (zeroIndex d k) a := by
  exact (J.value_eq_zeroIndex a).symm

end LocalJet

end Local
end ClassicalFieldTheory
