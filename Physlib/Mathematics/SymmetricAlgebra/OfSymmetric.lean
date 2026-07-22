/-
Copyright (c) 2026 Nathaneal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Physlib.Mathematics.SymmetricAlgebra.SymmetricMap

/-!
# Symmetric multilinear constructions for the symmetric algebra

This file contains symmetric multilinear constructions specific to the symmetric algebra. The
generic `SymmetricMap` compatibility API is isolated in
`Physlib.Mathematics.SymmetricAlgebra.SymmetricMap` so that it can be removed cleanly once the
corresponding Mathlib API is available.

## Main definitions

* `SymmetricAlgebra.ιMulti` sends a finite tuple to the product of its generators.

-/

@[expose] public section

universe u v

/-!

## A. Products of symmetric algebra generators

-/

namespace SymmetricAlgebra

variable (R : Type u) [CommSemiring R]
variable (M : Type v) [AddCommMonoid M] [Module R M]

/-!

### A.1. Definition

-/

/-- The canonical symmetric multilinear map sending a finite tuple to the product of the
corresponding generators in the symmetric algebra. -/
def ιMulti (n : ℕ) : SymmetricMap R M (SymmetricAlgebra R M) (Fin n) :=
  (mkPiAlgebra R (Fin n) (SymmetricAlgebra R M)).compLinearMap (ι R M)

/-!

### A.2. Computation lemmas

-/

/-- Applying `ιMulti` to a tuple gives the product of the corresponding symmetric-algebra
generators. -/
lemma ιMulti_apply {n : ℕ} (v : Fin n → M) :
    ιMulti R M n v = ∏ i, ι R M (v i) :=
  rfl

/-- The degree-zero symmetric monomial is the multiplicative identity. -/
@[simp]
lemma ιMulti_zero_apply (v : Fin 0 → M) : ιMulti R M 0 v = 1 := by
  rw [ιMulti_apply]
  exact Fin.prod_univ_zero _

/-- A positive-degree symmetric monomial is its first generator multiplied by the product of the
remaining generators. -/
@[simp]
lemma ιMulti_succ_apply {n : ℕ} (v : Fin n.succ → M) :
    ιMulti R M n.succ v = ι R M (v 0) * ιMulti R M n (Matrix.vecTail v) := by
  rw [ιMulti_apply, Fin.prod_univ_succ, ιMulti_apply]
  rfl

end SymmetricAlgebra
