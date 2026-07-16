/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.QuantumSystem.Basic
/-!

# The free particle on `Space d`

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Hilbert space

## iv. References

-/

@[expose] public section

noncomputable section
namespace QuantumMechanics

/-- A free, spinless quantum particle with mass `m > 0` in `Space d`. -/
structure FreeParticle where
  /-- The number of spatial dimensions. -/
  d : ℕ
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m

variable {Q : FreeParticle}

namespace FreeParticle

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
## B. Hilbert space
-/

abbrev HS := SpaceDHilbertSpace Q.d

end FreeParticle
end QuantumMechanics
end
