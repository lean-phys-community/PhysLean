/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Bounded operators on Hilbert space

This file connects the abstract operator-algebraic quantum-mechanics API with the concrete
C⋆-algebra of bounded operators on a complex Hilbert space. Mathlib supplies its C⋆-algebra
structure and the usual positive-operator order, where `A ≤ B` means that `B - A` is positive.
-/

@[expose] public section

namespace OperatorAlgebra

/-- Bounded operators on a complex Hilbert space, written in the usual physics notation. -/
notation "B(" H ")" => H →L[ℂ] H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded operators form an `OperatorAlgebra` using Mathlib's native Hilbert-space instances. -/
noncomputable instance instOperatorAlgebraBoundedOperators : OperatorAlgebra B(H) := {}

section Representation

/-- A Hilbert-space representation of `A` as a unital ⋆-homomorphism into `B(H)`. -/
abbrev Representation (A H : Type*) [OperatorAlgebra A] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] := A →⋆ₐ[ℂ] B(H)

end Representation

end OperatorAlgebra
