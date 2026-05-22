/-
Copyright (c) 2026 Xylem Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic), Aristotle (Harmonic)
-/
module

public import QuantumInfo.Finite.Braket

/-!
# Bargmann Invariant and Geometric Phase

The Bargmann invariant for three quantum states is the cyclic product
of inner products `⟨ψ₁|ψ₂⟩ · ⟨ψ₂|ψ₃⟩ · ⟨ψ₃|ψ₁⟩`. Its argument is
the geometric (Pancharatnam-Berry) phase accumulated around the
geodesic triangle in projective Hilbert space.

## Important definitions
 * `bargmannInvariant3`: the 3-vertex Bargmann invariant `Δ₃`
 * `bargmannPhase3`: the geometric phase `arg(Δ₃)`

## Important results
 * `bargmannInvariant3_degenerate`: identical states give `Δ₃ = 1`
 * `bargmannPhase3_degenerate`: identical states give phase `= 0`
 * `bargmannInvariant3_reverse`: reversing conjugates `Δ₃`
 * `bargmannPhase3_reverse`: reversing negates the phase (mod 2π)

## References
 * V. Bargmann, "Note on Wigner's theorem on symmetry operations",
   J. Math. Phys. 5, 862 (1964)
 * S. Pancharatnam, "Generalized theory of interference, and its
   applications", Proc. Indian Acad. Sci. A 44, 247 (1956)
-/

open Braket Complex

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section

/-- The 3-vertex Bargmann invariant: `⟨ψ₁|ψ₂⟩ · ⟨ψ₂|ψ₃⟩ · ⟨ψ₃|ψ₁⟩`.
    This is a gauge-invariant complex number whose argument is the
    geometric phase of the geodesic triangle. -/
def bargmannInvariant3 (ψ₁ ψ₂ ψ₃ : Ket d) : ℂ :=
  〈ψ₁‖ψ₂〉 * 〈ψ₂‖ψ₃〉 * 〈ψ₃‖ψ₁〉

/-- The geometric (Pancharatnam-Berry) phase of three states. -/
def bargmannPhase3 (ψ₁ ψ₂ ψ₃ : Ket d) : ℝ :=
  Complex.arg (bargmannInvariant3 ψ₁ ψ₂ ψ₃)

/-! ## Degenerate triangles -/

/-- The Bargmann invariant of three identical states is 1. -/
@[simp]
lemma bargmannInvariant3_degenerate (ψ : Ket d) :
    bargmannInvariant3 ψ ψ ψ = 1 := by
  unfold bargmannInvariant3
  simp [Braket.dot_self_eq_one]

/-- The geometric phase of three identical states is 0. -/
lemma bargmannPhase3_degenerate (ψ : Ket d) :
    bargmannPhase3 ψ ψ ψ = 0 := by
  unfold bargmannPhase3; simp [Complex.arg_one]

/-! ## Conjugacy -/

/-- Swapping the arguments conjugates the overlap: `⟨ψ₂|ψ₁⟩ = conj(⟨ψ₁|ψ₂⟩)`. -/
lemma dot_swap_conj (ψ₁ ψ₂ : Ket d) :
    〈ψ₂‖ψ₁〉 = starRingEnd ℂ 〈ψ₁‖ψ₂〉 := by
  simp +decide [Braket.dot]
  ac_rfl

/-- Reversing the cyclic order conjugates the invariant. -/
lemma bargmannInvariant3_reverse (ψ₁ ψ₂ ψ₃ : Ket d) :
    bargmannInvariant3 ψ₃ ψ₂ ψ₁ = starRingEnd ℂ (bargmannInvariant3 ψ₁ ψ₂ ψ₃) := by
  unfold bargmannInvariant3
  conv_lhs =>
    rw [dot_swap_conj ψ₂ ψ₃, dot_swap_conj ψ₁ ψ₂, dot_swap_conj ψ₃ ψ₁,
        ← map_mul, ← map_mul]
  congr 1; ring

/-- Reversing the cyclic order negates the geometric phase (mod 2π). -/
lemma bargmannPhase3_reverse (ψ₁ ψ₂ ψ₃ : Ket d)
    (h : bargmannInvariant3 ψ₁ ψ₂ ψ₃ ≠ 0) :
    (bargmannPhase3 ψ₃ ψ₂ ψ₁ : Real.Angle) =
    -(bargmannPhase3 ψ₁ ψ₂ ψ₃ : Real.Angle) := by
  unfold bargmannPhase3; rw [bargmannInvariant3_reverse]
  exact Complex.arg_conj_coe_angle (bargmannInvariant3 ψ₁ ψ₂ ψ₃)
