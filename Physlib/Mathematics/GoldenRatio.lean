/-
Copyright (c) 2026 Trinity-S3AI contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trinity-S3AI contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic
/-!

# Golden-ratio identities for physics

This module collects the few derived identities about the golden ratio
`φ = (1 + √5) / 2` and its conjugate `ψ = (1 - √5) / 2` that are useful in
physical applications but are not (yet) stated in mathlib.

The basic algebra already lives in `Mathlib.NumberTheory.Real.GoldenRatio`,
which defines `Real.goldenRatio`, `Real.goldenConj` and the `scoped[goldenRatio]`
notations `φ`, `ψ`, and proves the golden equation, the Viète relations,
positivity, irrationality and Binet's formula. Per reviewer guidance, this
module does **not** introduce any new `phi`/`psi` names: it works directly on
`Real.goldenRatio` / `Real.goldenConj` and uses mathlib's own `φ` / `ψ`
notation, made available file-locally via `open scoped goldenRatio` (so the
single-letter `φ` is never exported globally and does not collide with `φ`
used elsewhere in physics as a phase or a potential).

What this module adds on top of mathlib:

* `goldenRatio_continued_fraction` — the fixed-point identity `φ = 1 + 1/φ`,
  the entry point to the continued-fraction expansion `φ = [1; 1, 1, …]` used
  in KAM theory and the "most irrational" rotation number.
* `goldenRatio_two_cos_pi_div_five` — the icosian identity `φ = 2 cos(π/5)`,
  the bridge from the algebraic golden ratio to the 5-fold symmetry of the
  pentagon (H₂), the 600-cell and the binary icosahedral group `2I ⊂ SU(2)`.
* `goldenRatio_inv_pos`, `goldenRatio_inv_lt_one` — explicit bounds on `1/φ`.
* `goldenRatio_quadratic`, `goldenConj_quadratic` — both roots of
  `X² - X - 1 = 0` in a form ready for substitution arguments.
* `goldenRatio_lower_bound`, `goldenRatio_upper_bound` — numerical envelopes.
* `goldenRatio_pow_three`, `_four`, `_five` — closed forms with the
  Fibonacci-coefficient pattern `φ^n = F_n · φ + F_{n-1}`.

All proofs are complete (no `sorry`, no `axiom`).
-/

@[expose] public section

namespace Physlib.GoldenRatio

open Real
open scoped goldenRatio

/-! ## Section 1: Derived physics-flavoured identities

These results are not in mathlib but are useful for physical applications.
They connect `φ` to its continued-fraction description, to the 5-fold
symmetry of the icosian Coxeter group, and to explicit positivity bounds. -/

/-- `1/φ > 0`. -/
theorem goldenRatio_inv_pos : 0 < φ⁻¹ :=
  inv_pos.mpr goldenRatio_pos

/-- `1/φ < 1`. -/
theorem goldenRatio_inv_lt_one : φ⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ one_lt_goldenRatio

/-- `1/φ ≠ 0`. -/
theorem goldenRatio_inv_ne_zero : φ⁻¹ ≠ 0 :=
  inv_ne_zero goldenRatio_ne_zero

/-- The fixed-point identity `φ = 1 + 1/φ` — the key relation behind the
continued-fraction expansion `φ = [1; 1, 1, …]`.

Proof: combine `φ + ψ = 1` (Viète) with `1/φ = -ψ` to get
`1 + 1/φ = 1 - ψ = φ`. -/
theorem goldenRatio_continued_fraction : φ = 1 + φ⁻¹ := by
  rw [inv_goldenRatio]
  have : φ + ψ = 1 := goldenRatio_add_goldenConj
  linarith

/-- Equivalent form of the fixed-point identity: `φ - 1 = 1/φ`. -/
theorem goldenRatio_sub_one_eq_inv : φ - 1 = φ⁻¹ := by
  have := goldenRatio_continued_fraction; linarith

/-- The icosian / Coxeter identity `φ = 2 cos(π / 5)`. This is the bridge
between the algebraic description of `φ` and the geometric description through
the 5-fold rotational symmetry of the regular pentagon (H₂ Coxeter group)
and, by extension, of the 600-cell and the binary icosahedral group `2I`.

Proof: `cos(π/5) = (1 + √5)/4` (mathlib's `Real.cos_pi_div_five`); doubling
gives `2 cos(π/5) = (1 + √5)/2 = φ`. -/
theorem goldenRatio_two_cos_pi_div_five : φ = 2 * Real.cos (Real.pi / 5) := by
  rw [Real.cos_pi_div_five]
  show Real.goldenRatio = 2 * ((1 + Real.sqrt 5) / 4)
  unfold Real.goldenRatio
  ring

/-- `φ` is a root of the quadratic `X² - X - 1`. -/
theorem goldenRatio_quadratic : φ ^ 2 - φ - 1 = 0 := by
  have := goldenRatio_sq; linarith

/-- `ψ` is a root of the quadratic `X² - X - 1`. -/
theorem goldenConj_quadratic : ψ ^ 2 - ψ - 1 = 0 := by
  have := goldenConj_sq; linarith

/-- Both roots of `X² - X - 1 = 0` satisfy the Viète relations. -/
theorem goldenRatio_goldenConj_vieta :
    φ + ψ = 1 ∧ φ * ψ = -1 :=
  ⟨goldenRatio_add_goldenConj, goldenRatio_mul_goldenConj⟩

/-! ## Section 2: Explicit numerical bounds

Useful for interval arithmetic and physical estimation. -/

/-- Lower bound: `1.6 < φ`. -/
theorem goldenRatio_lower_bound : (1.6 : ℝ) < φ := by
  have h₁ : (2.2 : ℝ) < Real.sqrt 5 := by
    have heq : (2.2 : ℝ) = Real.sqrt (2.2 ^ 2) := by
      rw [Real.sqrt_sq] <;> norm_num
    rw [heq]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  show (1.6 : ℝ) < (1 + Real.sqrt 5) / 2
  linarith

/-- Upper bound: `φ < 1.7`. -/
theorem goldenRatio_upper_bound : φ < (1.7 : ℝ) := by
  have h₁ : Real.sqrt 5 < (2.4 : ℝ) := by
    have heq : (2.4 : ℝ) = Real.sqrt (2.4 ^ 2) := by
      rw [Real.sqrt_sq] <;> norm_num
    rw [heq]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  show (1 + Real.sqrt 5) / 2 < (1.7 : ℝ)
  linarith

/-- Joint numerical envelope: `1.6 < φ < 1.7`. -/
theorem goldenRatio_bounds : (1.6 : ℝ) < φ ∧ φ < (1.7 : ℝ) :=
  ⟨goldenRatio_lower_bound, goldenRatio_upper_bound⟩

/-! ## Section 3: Powers of `φ`

Closed forms for low integer powers of `φ` obtained by iterating the golden
equation `φ² = φ + 1`. The coefficients are Fibonacci numbers, reflecting
Binet's formula.

The mathlib lemma `Real.goldenRatio_pow_sub_goldenRatio_pow` states
`φ^(n+2) - φ^(n+1) = φ^n`, i.e. `φ^(n+2) = φ^(n+1) + φ^n`. -/

/-- `φ ^ 3 = 2 φ + 1`. -/
theorem goldenRatio_pow_three : φ ^ 3 = 2 * φ + 1 := by
  have h := goldenRatio_sq
  have : φ ^ 3 = φ * φ ^ 2 := by ring
  rw [this, h]; ring

/-- `φ ^ 4 = 3 φ + 2`. -/
theorem goldenRatio_pow_four : φ ^ 4 = 3 * φ + 2 := by
  have h := goldenRatio_sq
  have h3 := goldenRatio_pow_three
  have : φ ^ 4 = φ * φ ^ 3 := by ring
  rw [this, h3]
  have : φ * (2 * φ + 1) = 2 * φ ^ 2 + φ := by ring
  rw [this, h]; ring

/-- `φ ^ 5 = 5 φ + 3`. The general Fibonacci-coefficient pattern:
`φ ^ n = F_n · φ + F_{n-1}`, where `F_n` is the n-th Fibonacci number. -/
theorem goldenRatio_pow_five : φ ^ 5 = 5 * φ + 3 := by
  have h := goldenRatio_sq
  have h4 := goldenRatio_pow_four
  have : φ ^ 5 = φ * φ ^ 4 := by ring
  rw [this, h4]
  have : φ * (3 * φ + 2) = 3 * φ ^ 2 + 2 * φ := by ring
  rw [this, h]; ring

end Physlib.GoldenRatio
