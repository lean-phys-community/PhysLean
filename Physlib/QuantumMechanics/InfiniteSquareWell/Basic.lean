/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.QuantumSystem.Basic
/-!

# The infinite square well

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Hilbert space
- C. Hamiltonian

## iv. References

-/

@[expose] public section

noncomputable section
namespace QuantumMechanics

open Set MeasureTheory

/-- A spinless quantum particle with mass `m > 0` confined to a cuboid in `Space d`. -/
structure InfiniteSquareWell where
  /-- The number of spatial dimensions. -/
  d : ℕ
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The lower bounds of the box. -/
  lower : Fin d → ℝ
  /-- The upper bounds of the box. -/
  upper : Fin d → ℝ
  /-- The box is non-empty. -/
  hbounds : ∀ i, lower i < upper i

variable {Q : InfiniteSquareWell}

namespace InfiniteSquareWell

/-!
## A. Basic properties
-/

@[simp]
lemma m_pos : 0 < Q.m := Q.hm

@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le

@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'

/-!
## B. The domain
-/

/-- The domain of the infinite square well as a Cartesian product of closed intervals. -/
def box : Set (Space Q.d) := Space.val ⁻¹' Icc Q.lower Q.upper

/-!
## C. Hilbert space
-/

/-- The measure associated with the domain of the infinite square well. -/
def measure : Measure (Space Q.d) := volume.restrict Q.box

/-- The Hilbert space for the infinite square well. -/
abbrev HS := SpaceDHilbertSpace Q.d Q.measure

end InfiniteSquareWell
end QuantumMechanics
end
