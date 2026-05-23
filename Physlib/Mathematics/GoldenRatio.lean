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

# The golden ratio for physics

The constant `φ = (1 + √5) / 2` and its algebraic conjugate `ψ = (1 - √5) / 2`
appear throughout physics: in the quasicrystal literature (Penrose tilings,
icosahedral symmetry of viral capsids and metallic alloys), in the H₄ root
system underlying the 600-cell and the binary icosahedral group `2I ⊂ SU(2)`,
in continuous-spectrum analyses where the irrational rotation number `1/φ`
plays the role of "most irrational" frequency, and in coupling-constant
relations of the icosian Coxeter program.

The bulk of the basic algebra is already in mathlib (`Mathlib.NumberTheory.
Real.GoldenRatio` defines `Real.goldenRatio`, `Real.goldenConj`, the `φ`
and `ψ` notations and proves the golden equation, positivity, irrationality
and Binet's formula). This module re-exports that API into the `Physlib`
namespace and adds the physics-flavoured derived identities that mathlib
does not state:

* `phi`, `psi` — `Physlib`-level shortcuts.
* `phi_continued_fraction` — the fixed-point identity `φ = 1 + 1/φ`, the
  entry point to the continued-fraction description used in KAM theory.
* `phi_inv_pos`, `phi_inv_lt_one` — explicit positivity of `1/φ`.
* `phi_two_cos_pi_div_five` — the icosian identity `φ = 2 cos(π/5)`,
  the bridge between the algebraic and the H₄/geometric descriptions.
* `phi_quadratic` and `psi_quadratic` — both roots of `X² - X - 1 = 0`
  in a form ready for substitution arguments.
* `phi_lower_bound`, `phi_upper_bound` — explicit numerical envelopes.
* `phi_pow_three`, `phi_pow_four`, `phi_pow_five` — closed forms with
  Fibonacci-coefficient pattern.

All proofs are by `Qed` (no `sorry`, no `axiom`).
-/

@[expose] public section

namespace Physlib

open Real goldenRatio

/-! ## Section 1: `Physlib`-level shortcuts -/

/-- The golden ratio `φ := (1 + √5) / 2`. Re-export of `Real.goldenRatio`. -/
abbrev phi : ℝ := Real.goldenRatio

/-- The conjugate of the golden ratio `ψ := (1 - √5) / 2`.
Re-export of `Real.goldenConj`. -/
abbrev psi : ℝ := Real.goldenConj

theorem phi_eq_goldenRatio : phi = φ := rfl

theorem psi_eq_goldenConj : psi = ψ := rfl

/-! ## Section 2: Re-export of the mathlib basic identities

These re-statements simply repackage the mathlib lemmas under the `Physlib`
namespace so downstream Physlib files do not have to know the mathlib path.
The mathlib originals are: `Real.goldenRatio_sq`, `Real.goldenRatio_pos`,
`Real.one_lt_goldenRatio`, `Real.goldenRatio_lt_two`,
`Real.goldenRatio_mul_goldenConj`, `Real.goldenRatio_add_goldenConj`,
`Real.inv_goldenRatio`. -/

theorem phi_sq : phi ^ 2 = phi + 1 := Real.goldenRatio_sq

theorem phi_pos : 0 < phi := Real.goldenRatio_pos

theorem phi_ne_zero : phi ≠ 0 := Real.goldenRatio_ne_zero

theorem one_lt_phi : 1 < phi := Real.one_lt_goldenRatio

theorem phi_lt_two : phi < 2 := Real.goldenRatio_lt_two

theorem psi_neg : psi < 0 := Real.goldenConj_neg

theorem psi_ne_zero : psi ≠ 0 := Real.goldenConj_ne_zero

theorem phi_psi_sum : phi + psi = 1 := Real.goldenRatio_add_goldenConj

theorem phi_psi_prod : phi * psi = -1 := Real.goldenRatio_mul_goldenConj

theorem phi_inv_eq_neg_psi : phi⁻¹ = -psi := Real.inv_goldenRatio

theorem psi_inv_eq_neg_phi : psi⁻¹ = -phi := Real.inv_goldenConj

theorem psi_sq : psi ^ 2 = psi + 1 := Real.goldenConj_sq

/-! ## Section 3: Derived physics-flavoured identities

These results are not in mathlib but are useful for physical applications.
They connect φ to its continued-fraction description, to the 5-fold
symmetry of the icosian Coxeter group, and to explicit positivity bounds. -/

/-- `1/φ > 0`. -/
theorem phi_inv_pos : 0 < phi⁻¹ :=
  inv_pos.mpr phi_pos

/-- `1/φ < 1`. -/
theorem phi_inv_lt_one : phi⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ one_lt_phi

/-- `1/φ ≠ 0`. -/
theorem phi_inv_ne_zero : phi⁻¹ ≠ 0 :=
  inv_ne_zero phi_ne_zero

/-- The fixed-point identity `φ = 1 + 1/φ` — the key relation behind the
continued-fraction expansion `φ = [1; 1, 1, ...]`.

Proof: combine `φ + ψ = 1` (Viète) with `1/φ = -ψ` to get
`1 + 1/φ = 1 - ψ = φ`. -/
theorem phi_continued_fraction : phi = 1 + phi⁻¹ := by
  rw [phi_inv_eq_neg_psi]
  have : phi + psi = 1 := phi_psi_sum
  linarith

/-- Equivalent form of the fixed-point identity: `φ - 1 = 1/φ`. -/
theorem phi_sub_one_eq_inv : phi - 1 = phi⁻¹ := by
  have := phi_continued_fraction; linarith

/-- The icosian / Coxeter identity `φ = 2 cos(π / 5)`. This is the bridge
between the algebraic description of φ and the geometric description through
the 5-fold rotational symmetry of the regular pentagon (H₂ Coxeter group)
and, by extension, of the 600-cell and the binary icosahedral group `2I`.

Proof: `cos(π/5) = (1 + √5)/4` (mathlib's `Real.cos_pi_div_five`); doubling
gives `2 cos(π/5) = (1 + √5)/2 = φ`. -/
theorem phi_two_cos_pi_div_five : phi = 2 * Real.cos (Real.pi / 5) := by
  rw [Real.cos_pi_div_five]
  show Real.goldenRatio = 2 * ((1 + Real.sqrt 5) / 4)
  unfold Real.goldenRatio
  ring

/-- φ is a root of the quadratic `X² - X - 1`. -/
theorem phi_quadratic : phi ^ 2 - phi - 1 = 0 := by
  have := phi_sq; linarith

/-- ψ is a root of the quadratic `X² - X - 1`. -/
theorem psi_quadratic : psi ^ 2 - psi - 1 = 0 := by
  have := psi_sq; linarith

/-- Both roots of `X² - X - 1 = 0` satisfy the Viète relations. -/
theorem phi_psi_vieta :
    phi + psi = 1 ∧ phi * psi = -1 :=
  ⟨phi_psi_sum, phi_psi_prod⟩

/-! ## Section 4: Explicit numerical bounds

Useful for interval arithmetic and physical estimation. -/

/-- Lower bound: `1.6 < φ`. -/
theorem phi_lower_bound : (1.6 : ℝ) < phi := by
  have h₁ : (2.2 : ℝ) < Real.sqrt 5 := by
    have heq : (2.2 : ℝ) = Real.sqrt (2.2 ^ 2) := by
      rw [Real.sqrt_sq] <;> norm_num
    rw [heq]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  show (1.6 : ℝ) < (1 + Real.sqrt 5) / 2
  linarith

/-- Upper bound: `φ < 1.7`. -/
theorem phi_upper_bound : phi < (1.7 : ℝ) := by
  have h₁ : Real.sqrt 5 < (2.4 : ℝ) := by
    have heq : (2.4 : ℝ) = Real.sqrt (2.4 ^ 2) := by
      rw [Real.sqrt_sq] <;> norm_num
    rw [heq]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  show (1 + Real.sqrt 5) / 2 < (1.7 : ℝ)
  linarith

/-- Joint numerical envelope: `1.6 < φ < 1.7`. -/
theorem phi_bounds : (1.6 : ℝ) < phi ∧ phi < (1.7 : ℝ) :=
  ⟨phi_lower_bound, phi_upper_bound⟩

/-! ## Section 5: Powers of φ

Closed forms for low integer powers of φ obtained by iterating the golden
equation `φ² = φ + 1`. The coefficients are Fibonacci numbers, reflecting
Binet's formula.

The mathlib lemma `Real.goldenRatio_pow_sub_goldenRatio_pow` states
`φ^(n+2) - φ^(n+1) = φ^n`, i.e. `φ^(n+2) = φ^(n+1) + φ^n`. -/

/-- `φ ^ 3 = 2 φ + 1`. -/
theorem phi_pow_three : phi ^ 3 = 2 * phi + 1 := by
  have h := phi_sq
  have : phi ^ 3 = phi * phi ^ 2 := by ring
  rw [this, h]; ring

/-- `φ ^ 4 = 3 φ + 2`. -/
theorem phi_pow_four : phi ^ 4 = 3 * phi + 2 := by
  have h := phi_sq
  have h3 := phi_pow_three
  have : phi ^ 4 = phi * phi ^ 3 := by ring
  rw [this, h3]
  have : phi * (2 * phi + 1) = 2 * phi ^ 2 + phi := by ring
  rw [this, h]; ring

/-- `φ ^ 5 = 5 φ + 3`. The general Fibonacci-coefficient pattern:
`φ ^ n = F_n · φ + F_{n-1}`, where `F_n` is the n-th Fibonacci number. -/
theorem phi_pow_five : phi ^ 5 = 5 * phi + 3 := by
  have h := phi_sq
  have h4 := phi_pow_four
  have : phi ^ 5 = phi * phi ^ 4 := by ring
  rw [this, h4]
  have : phi * (3 * phi + 2) = 3 * phi ^ 2 + 2 * phi := by ring
  rw [this, h]; ring

/-! ## Section 6: Irrationality (re-export)

`φ` and `ψ` are irrational; this is `Real.goldenRatio_irrational` and
`Real.goldenConj_irrational` in mathlib. -/

theorem phi_irrational : Irrational phi := Real.goldenRatio_irrational

theorem psi_irrational : Irrational psi := Real.goldenConj_irrational

end Physlib