/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.States.Statistics
public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Lie
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!

# Uncertainty relations

Positivity of a state gives a Cauchy--Schwarz inequality for expectation values.
Applied to centered observables, this yields the Robertson--Schrödinger and
Robertson uncertainty relations.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace OperatorAlgebra

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

namespace State

/-- The commutator `⁅a, b⁆` (canonically `⁅x, p⁆ = iℏ`) only sees fluctuations, not means:
centering `a` and `b` changes nothing about how badly they fail to commute. -/
@[simp]
lemma bracket_centered (ω : State A) (a b : Observable A) :
    ⁅centered ω a, centered ω b⁆ = ⁅a, b⁆ := by
  simp [centered, sub_lie, lie_sub]

/-- The expectation of a raw product of two fluctuations splits into a real symmetric part
(covariance) and an imaginary antisymmetric part (the commutator). This split is what turns the
Cauchy–Schwarz bound below into simultaneous control on covariance and commutator. -/
lemma apply_centered_mul_centered (ω : State A) (a b : Observable A) :
    ω ((centered ω a : A) * centered ω b) =
      (covariance ω a b : ℂ) + Complex.I * (ω⟨⁅a, b⁆⟩ : ℂ) := by
  rw [Observable.mul_decomposition, map_add, map_smul,
    apply_observable_eq_expectation, apply_observable_eq_expectation,
    bracket_centered]
  rfl

/-! ## Cauchy--Schwarz -/

/-- Cauchy–Schwarz for the positive sesquilinear form induced by a state. -/
lemma gns_cauchy_schwarz (ω : State A) (x y : A) :
    ‖ω (star x * y)‖ * ‖ω (star y * x)‖ ≤
      (ω (star x * x)).re * (ω (star y * y)).re := by
  let φ := ω.toPositiveLinearMap
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (φ.toPreGNS x) (φ.toPreGNS y)
  simp only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS] at h
  exact h

/-- Reversing the order of two observables in a product conjugates the state's value on it —
bookkeeping used to relate `ω(ba)` back to `ω(ab)`. -/
lemma apply_mul_comm_eq_star (ω : State A) (a b : Observable A) :
    ω ((b : A) * a) = star (ω ((a : A) * b)) := by
  rw [← map_star, star_mul, a.property.star_eq, b.property.star_eq]

/-- No state can correlate two fluctuations more strongly than the product of their spreads
allows — the GNS-Cauchy–Schwarz seed of every uncertainty relation below, before splitting the
left side via `apply_centered_mul_centered`. -/
lemma centered_gns_cauchy_schwarz (ω : State A) (a b : Observable A) :
    ‖ω ((centered ω a : A) * centered ω b)‖ *
        ‖ω ((centered ω b : A) * centered ω a)‖ ≤
      variance ω a * variance ω b := by
  rw [variance_eq_re_apply_centered_mul_self, variance_eq_re_apply_centered_mul_self]
  simpa only [(centered ω a).property.star_eq, (centered ω b).property.star_eq] using
    gns_cauchy_schwarz ω (centered ω a : A) (centered ω b : A)

/-- The squared-magnitude form of `centered_gns_cauchy_schwarz`, ready to be split via
`apply_centered_mul_centered` into `robertson_schrodinger`. -/
lemma centered_cauchy_schwarz (ω : State A) (a b : Observable A) :
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) ≤
      variance ω a * variance ω b := by
  calc
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) =
        ‖ω ((centered ω a : A) * centered ω b)‖ *
          ‖ω ((centered ω b : A) * centered ω a)‖ := by
      rw [apply_mul_comm_eq_star]
      simp [Complex.normSq_eq_norm_sq, pow_two]
    _ ≤ _ := centered_gns_cauchy_schwarz ω a b

/-! ## Uncertainty relations -/

/-- The Robertson–Schrödinger uncertainty inequality: the sharpest relation here, jointly bounding
covariance and commutator by the product of the individual spreads. Dropping either term below
recovers the more familiar `covariance_cauchy_schwarz` / `robertson`. -/
lemma robertson_schrodinger (ω : State A) (a b : Observable A) :
    covariance ω a b ^ 2 + ω⟨⁅a, b⁆⟩ ^ 2 ≤
      variance ω a * variance ω b := by
  have h := centered_cauchy_schwarz ω a b
  rw [apply_centered_mul_centered, Complex.normSq_apply] at h
  simpa [pow_two] using h

/-- Two observables cannot be more correlated than the product of their uncertainties allows —
the familiar `|correlation| ≤ σ_a · σ_b`, from dropping the commutator term in
`robertson_schrodinger`. -/
lemma covariance_cauchy_schwarz (ω : State A) (a b : Observable A) :
    covariance ω a b ^ 2 ≤ variance ω a * variance ω b := by
  nlinarith [robertson_schrodinger ω a b,
    sq_nonneg (ω⟨⁅a, b⁆⟩)]

/-- Heisenberg's uncertainty relation: observables that fail to commute cannot both be measured
with arbitrary precision. For position and momentum, `⁅x, p⁆ = iℏ` gives `ΔxΔp ≥ ℏ/2`. Obtained
from `robertson_schrodinger` by dropping the covariance term. -/
lemma robertson (ω : State A) (a b : Observable A) :
    ω⟨⁅a, b⁆⟩ ^ 2 ≤ variance ω a * variance ω b := by
  nlinarith [robertson_schrodinger ω a b,
    sq_nonneg (covariance ω a b)]

end State

end OperatorAlgebra
