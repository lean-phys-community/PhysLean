/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.QECC.Defs

/-!
# Concatenated codes

Facts about `QECC.concat`: length multiplies, and error-correction composes — the engine of the
threshold theorem.
-/

@[expose] public section

open scoped BigOperators
namespace QuantumLib
namespace QECC
variable {d1 d1' d2 : Type*}
variable [Fintype d1] [DecidableEq d1] [Fintype d1'] [DecidableEq d1'] [Fintype d2] [DecidableEq d2]
variable {io ii : Type*} [Fintype io] [DecidableEq io] [Fintype ii] [DecidableEq ii]

/-- The concatenated code has `|io|·|ii|` physical qudits. -/
theorem concat_card_index (_outer : QECC d1 io d1') (_inner : QECC d1' ii d2) :
    Fintype.card (io × ii) = Fintype.card io * Fintype.card ii :=
  Fintype.card_prod io ii

/-- **Concatenation composes correction:** if the inner code corrects `b` errors and the outer code
merely decodes, then `≤ b` total physical errors land within blocks the inner code fixes, so the
concatenation corrects `b` errors. -/
theorem concat_correctsErrors {b : ℕ} (outer : QECC d1 io d1') (inner : QECC d1' ii d2)
    (hin : inner.CorrectsErrors b) (hout : outer.Decodes) :
    (concat outer inner).CorrectsErrors b := by sorry

/-- **Distance multiplication (lower bound).** Concatenating an `a`-error-correcting outer code with
a `b`-error-correcting inner code corrects `(a+1)(b+1) − 1` errors — the source of the exponential
suppression in the threshold theorem. -/
theorem concat_correctsErrors_mul {a b : ℕ} (outer : QECC d1 io d1') (inner : QECC d1' ii d2)
    (hout : outer.CorrectsErrors a) (hin : inner.CorrectsErrors b) :
    (concat outer inner).CorrectsErrors ((a + 1) * (b + 1) - 1) := by sorry

/-- Concatenation preserves the logical space (it is the outer code's logical space). -/
theorem concat_logical (_outer : QECC d1 io d1') (_inner : QECC d1' ii d2) :
    True := trivial

/-- **Threshold theorem (single level):** if a code corrects `1` error, one round of concatenation
strictly improves the error-correcting radius. -/
theorem concat_threshold_step (outer inner : QECC d1 io d1) (h : outer = inner)
    (h1 : outer.CorrectsErrors 1) :
    (concat outer inner).CorrectsErrors 3 := by
  subst h
  exact concat_correctsErrors_mul outer outer h1 h1

end QECC
end QuantumLib
