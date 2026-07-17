/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Multiplication
public import Physlib.QuantumMechanics.QuantumSystem.Basic
/-!

# The rectangular potential barrier

## i. Overview

The rectangular potential barrier in one dimension provides the simplest example of quantum
tunnelling. A particle of mass `m` is subject to a piece-wise constant potential which is `V₀`
on a closed interval and zero elsewhere.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Potential function
- C. Hilbert space
- D. Operators
  - D.1. Kinetic
  - D.2. Potential
  - D.3. Hamiltonian
- E. As a quantum system

## iv. References

-/

@[expose] public section

noncomputable section
namespace QuantumMechanics

open Set MeasureTheory SpaceDHilbertSpace

/-- A quantum particle with mass `m > 0` on `Space 1` subject to a rectangular potential barrier.

  The potential is `V₀` on the interval `Icc lower upper` and zero elsewhere. -/
structure RectangularBarrier where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The lower bound of the barrier. -/
  lower : ℝ
  /-- The upper bound of the barrier. -/
  upper : ℝ
  h_bounds : lower < upper
  /-- The height of the potential barrier. -/
  V₀ : ℝ

variable (Q : RectangularBarrier)

namespace RectangularBarrier

/-!
## A. Basic properties
-/

@[simp]
lemma m_pos : 0 < Q.m := Q.hm

@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le

@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'

end RectangularBarrier
end QuantumMechanics
end
