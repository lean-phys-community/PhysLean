/-
Copyright (c) 2026 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
module

public import Physlib.Mathematics.SpecialFunctions.PhysHermite

/-!
# Sudden frequency change for the quantum harmonic oscillator

An oscillator of mass `m` with frequency `ω` is prepared in its ground state.
At time `t = 0` the frequency suddenly changes to `ω'`. We compute the
probability of finding the system in the `n`-th eigenstate of the *new*
Hamiltonian:

`Pₙ = |⟨ψₙ^{(ω')} | ψ₀^{(ω)}⟩|²`.

Parametrising by `α = mω/ℏ` and `β = mω'/ℏ`:

* For odd `n`, `Pₙ = 0` by parity.
* For `n = 0` (ground-state survival), `P₀ = 2√(αβ)/(α+β)`.
* For `n = 2k`, `P_{2k} = (2√(αβ)/(α+β)) · (2k)!/(2^{2k}(k!)²) · ((α-β)/(α+β))^{2k}`.

The main mathematical ingredient is the closed form

For `n` even, `∫ Hₙ(y) · exp(-p y²) dy = √(π/p) · n!/(n/2)! · ((1-p)/p)^{n/2}`.
For `n` odd, the integral vanishes.

for `p > 0`, proved here by induction using the Hermite three-term recurrence
and integration by parts.

## References

* DLMF 18.8.1 (Hermite differential equation) and 18.9.13 (recurrence),
  <https://dlmf.nist.gov/18.8>, <https://dlmf.nist.gov/18.9>.
* A. G. Abanov, *Landau's Theoretical Minimum: Quantum Mechanics*,
  <https://people.tamu.edu/~abanov/QE/TM-QM.pdf>.
-/

@[expose] public section

open Polynomial Physlib MeasureTheory

namespace Physlib.QuantumMechanics.HarmonicOscillator

/-! ## Hermite differential equation (polynomial level). -/

/-- The physicists' Hermite polynomials satisfy the Hermite differential equation
`Hₙ'' − 2X·Hₙ' + 2n·Hₙ = 0` in `Polynomial ℤ`. -/
theorem physHermite_ode (n : ℕ) :
    derivative (derivative (physHermite n))
      = 2 * X * derivative (physHermite n) - (2 * n) • physHermite n := by
  rcases n with _ | k
  · simp
  · rw [derivative_physHermite_succ k, physHermite_succ k]
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      derivative_mul, derivative_ofNat, derivative_natCast, derivative_add,
      derivative_one, zero_mul, zero_add]
    ring

/-! ## Hermite–Gaussian integrals. -/

private lemma integrable_polynomial_apply_mul_gaussian
    {p : ℝ} (hp : 0 < p) (P : Polynomial ℤ) :
    Integrable (fun y : ℝ => (P.aeval y) * Real.exp (- p * y ^ 2)) :=
  guassian_integrable_polynomial hp P

/-- `physHermite 1` evaluates to `2 y`. -/
lemma physHermite_one_apply (y : ℝ) : physHermite 1 y = 2 * y := by
  rw [physHermite_eq_aeval, physHermite_one]
  simp [Polynomial.aevalEquiv, Polynomial.aeval]

/-- Negation invariance of the full Lebesgue integral on ℝ. -/
lemma integral_comp_neg_real (f : ℝ → ℝ) :
    ∫ y : ℝ, f (-y) = ∫ y : ℝ, f y :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding f

/-- An odd integrable function over ℝ integrates to zero. -/
lemma integral_eq_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ y, f (-y) = - f y) :
    ∫ y : ℝ, f y = 0 := by
  have h1 : ∫ y : ℝ, f y = ∫ y : ℝ, f (-y) := (integral_comp_neg_real f).symm
  have h2 : ∫ y : ℝ, f (-y) = - ∫ y : ℝ, f y := by
    simp_rw [hodd, integral_neg]
  linarith [h1.trans h2]

/-- `∫ H₁(y)·exp(-py²) dy = 0` for any `p`, by parity. -/
lemma integral_physHermite_one_gaussian (p : ℝ) :
    ∫ y : ℝ, physHermite 1 y * Real.exp (- p * y ^ 2) = 0 := by
  apply integral_eq_zero_of_odd
  intro y
  simp only [physHermite_one_apply, neg_mul]
  have : (-y) ^ 2 = y ^ 2 := by ring
  rw [this]
  ring

/-- `HasDerivAt` for `H_{n+1}` with derivative `2(n+1) H_n`. -/
lemma physHermite_succ_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => physHermite (n + 1) y) (2 * (n + 1 : ℝ) * physHermite n x) x := by
  have hd : DifferentiableAt ℝ (fun y => physHermite (n + 1) y) x :=
    physHermite_differentiableAt _ _
  have h := hd.hasDerivAt
  have h1 := congr_fun (deriv_physHermite (n + 1)) x
  simp only [Pi.mul_apply, Nat.add_sub_cancel] at h1
  push_cast at h1
  rw [h1] at h
  convert h using 1

/-- `HasDerivAt` for `-1/(2p) · exp(-p y²)` with derivative `y · exp(-p y²)`. -/
lemma neg_gaussian_hasDerivAt {p : ℝ} (hp : p ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => -(1/(2*p)) * Real.exp (-p * y^2))
      (x * Real.exp (-p * x^2)) x := by
  have hinner : HasDerivAt (fun y : ℝ => -p * y^2) (-p * (2 * x)) x := by
    have hpow : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    exact hpow.const_mul (-p)
  have hexp : HasDerivAt (fun y => Real.exp (-p * y^2)) (Real.exp (-p * x^2) * (-p * (2 * x))) x :=
    hinner.exp
  have hscale := hexp.const_mul (-(1/(2*p)))
  convert hscale using 1
  field_simp

/-- Integration-by-parts identity: `∫ y · H_{n+1}(y) · e^{-py²} = (n+1)/p · ∫ H_n · e^{-py²}`. -/
lemma integral_y_mul_physHermite_succ_mul_gaussian {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ∫ y : ℝ, physHermite (n + 1) y * y * Real.exp (- p * y ^ 2)
      = ((n + 1 : ℝ) / p) * ∫ y : ℝ, physHermite n y * Real.exp (- p * y ^ 2) := by
  have hpne : p ≠ 0 := ne_of_gt hp
  have hint_uv' :
      Integrable (fun y : ℝ => physHermite (n + 1) y * (y * Real.exp (-p * y ^ 2))) := by
    have h := guassian_integrable_polynomial hp (X * physHermite (n + 1))
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro y
    show ((X * physHermite (n+1)).aeval y) * Real.exp (-p * y ^ 2)
        = physHermite (n+1) y * (y * Real.exp (-p * y ^ 2))
    rw [map_mul, aeval_X]; ring
  have hint_u'v :
      Integrable (fun y : ℝ => (2 * (n + 1 : ℝ) * physHermite n y) *
                                  (-(1 / (2 * p)) * Real.exp (-p * y ^ 2))) := by
    have h := (guassian_integrable_polynomial hp (physHermite n)).const_mul
                (2 * (n + 1 : ℝ) * (-(1 / (2 * p))))
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro y; ring
  have hint_uv :
      Integrable (fun y : ℝ => physHermite (n + 1) y *
                                  (-(1 / (2 * p)) * Real.exp (-p * y ^ 2))) := by
    have h := (guassian_integrable_polynomial hp (physHermite (n + 1))).const_mul
                (-(1 / (2 * p)))
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro y; ring
  have ibp : ∫ y : ℝ, physHermite (n + 1) y * (y * Real.exp (-p * y ^ 2))
      = - ∫ y : ℝ, (2 * (n + 1 : ℝ) * physHermite n y) *
        (-(1 / (2 * p)) * Real.exp (-p * y ^ 2)) := by
    apply integral_mul_deriv_eq_deriv_mul_of_integrable
    · intro x _; exact physHermite_succ_hasDerivAt n x
    · intro x _; exact neg_gaussian_hasDerivAt hpne x
    · exact hint_uv'
    · exact hint_u'v
    · exact hint_uv
  have hLHS : (fun y : ℝ => physHermite (n + 1) y * y * Real.exp (-p * y ^ 2))
            = (fun y : ℝ => physHermite (n + 1) y * (y * Real.exp (-p * y ^ 2))) := by
    funext y; ring
  rw [show ∫ y : ℝ, physHermite (n + 1) y * y * Real.exp (-p * y ^ 2)
        = ∫ y : ℝ, physHermite (n + 1) y * (y * Real.exp (-p * y ^ 2)) from by rw [hLHS]]
  rw [ibp]
  have hRHS : (fun y : ℝ => (2 * (n + 1 : ℝ) * physHermite n y) *
                              (-(1 / (2 * p)) * Real.exp (-p * y ^ 2)))
            = (fun y : ℝ => -((n + 1 : ℝ) / p) * (physHermite n y * Real.exp (-p * y ^ 2))) := by
    funext y; field_simp
  rw [show ∫ y : ℝ, (2 * (n + 1 : ℝ) * physHermite n y) *
        (-(1 / (2 * p)) * Real.exp (-p * y ^ 2))
      = ∫ y : ℝ, -((n + 1 : ℝ) / p) * (physHermite n y * Real.exp (-p * y ^ 2)) from by rw [hRHS]]
  rw [integral_const_mul]
  ring

/-- Two-step recurrence: `I_{n+2}(p) = 2(n+1)(1−p)/p · I_n(p)`. -/
lemma integral_physHermite_two_step {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ∫ y : ℝ, physHermite (n + 2) y * Real.exp (- p * y ^ 2)
      = 2 * (n + 1 : ℝ) * (1 - p) / p *
          ∫ y : ℝ, physHermite n y * Real.exp (- p * y ^ 2) := by
  have hsubst : ∀ y : ℝ,
      physHermite (n + 2) y * Real.exp (-p * y ^ 2)
        = 2 * (physHermite (n + 1) y * y * Real.exp (-p * y ^ 2))
          - 2 * (n + 1 : ℝ) * (physHermite n y * Real.exp (-p * y ^ 2)) := by
    intro y
    have h' := congr_fun (physHermite_succ_fun' (n + 1)) y
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul] at h'
    push_cast at h'
    linear_combination Real.exp (-p * y ^ 2) * h'
  have hint_left :
      Integrable (fun y : ℝ => 2 * (physHermite (n + 1) y * y * Real.exp (-p * y ^ 2))) := by
    have h := (integrable_polynomial_apply_mul_gaussian hp
                  (Polynomial.X * physHermite (n + 1))).const_mul 2
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro y
    show 2 * ((Polynomial.X * physHermite (n + 1)).aeval y * Real.exp (-p * y ^ 2))
        = 2 * (physHermite (n + 1) y * y * Real.exp (-p * y ^ 2))
    rw [map_mul, aeval_X]; ring
  have hint_right :
      Integrable (fun y : ℝ => 2 * (n + 1 : ℝ) * (physHermite n y * Real.exp (-p * y ^ 2))) :=
    (integrable_polynomial_apply_mul_gaussian hp (physHermite n)).const_mul (2 * (n + 1))
  simp_rw [hsubst]
  rw [integral_sub hint_left hint_right, integral_const_mul, integral_const_mul,
      integral_y_mul_physHermite_succ_mul_gaussian hp n]
  field_simp

/-- Odd-index integrals vanish: `∫ H_{2k+1}(y)·exp(-py²) dy = 0`. -/
lemma integral_physHermite_odd_gaussian {p : ℝ} (hp : 0 < p) (k : ℕ) :
    ∫ y : ℝ, physHermite (2 * k + 1) y * Real.exp (- p * y ^ 2) = 0 := by
  induction k with
  | zero => simpa using integral_physHermite_one_gaussian p
  | succ k ih =>
    have hidx : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [hidx, integral_physHermite_two_step hp (2 * k + 1), ih]
    ring

/-- Even-index integrals:
`∫ H_{2k}(y)·exp(-py²) dy = √(π/p) · (2k)!/k! · ((1-p)/p)^k`. -/
lemma integral_physHermite_even_gaussian {p : ℝ} (hp : 0 < p) (k : ℕ) :
    ∫ y : ℝ, physHermite (2 * k) y * Real.exp (- p * y ^ 2)
      = Real.sqrt (Real.pi / p) *
          (((2 * k).factorial : ℝ) / (k.factorial : ℝ)) *
          ((1 - p) / p) ^ k := by
  induction k with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, mul_one]
    simp only [physHermite_zero_apply, one_mul]
    simpa [neg_mul] using integral_gaussian p
  | succ k ih =>
    have hidx : 2 * (k + 1) = (2 * k) + 2 := by ring
    rw [hidx, integral_physHermite_two_step hp (2 * k), ih]
    have hkfact_ne : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hk1fact_ne : ((k + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast (k + 1).factorial_ne_zero
    have hp_ne : p ≠ 0 := ne_of_gt hp
    have hfact2 : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      rw [show 2 * k + 2 = (2 * k + 1) + 1 from rfl,
          Nat.factorial_succ, show (2*k+1) = (2*k) + 1 from rfl, Nat.factorial_succ]
      ring
    have hfact1 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
    rw [hfact2, hfact1]
    push_cast
    have hsplit : ((2 * (k : ℝ) + 2) * (2 * k + 1) * (((2 * k).factorial : ℝ))) /
                  (((k : ℝ) + 1) * (k.factorial : ℝ))
                = 2 * (2 * k + 1) * (((2 * k).factorial : ℝ) / k.factorial) := by
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by
        have : 0 < (k : ℝ) + 1 := by positivity
        linarith
      field_simp
    rw [hsplit]
    ring

/-- Closed form for the integral of `Hₙ(y)·exp(-p y²)` for `p > 0`. -/
theorem integral_physHermite_gaussian (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ∫ y : ℝ, physHermite n y * Real.exp (- p * y ^ 2) =
      if Even n then
        Real.sqrt (Real.pi / p) *
          ((n.factorial : ℝ) / ((n / 2).factorial : ℝ)) *
          ((1 - p) / p) ^ (n / 2)
      else 0 := by
  by_cases h : Even n
  · obtain ⟨k, hk⟩ := h
    have hn : n = 2 * k := by omega
    rw [if_pos ⟨k, hk⟩, hn, integral_physHermite_even_gaussian hp k]
    have hdiv : (2 * k) / 2 = k := by omega
    rw [hdiv]
  · rw [if_neg h]
    rw [Nat.not_even_iff_odd] at h
    obtain ⟨k, hk⟩ := h
    rw [hk]
    exact integral_physHermite_odd_gaussian hp k

/-! ## The ground-state wavefunction. -/

/-- The QHO ground-state wavefunction with frequency parameter `α = mω/ℏ`. -/
noncomputable def psi0 (α : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (α / Real.pi)) * Real.exp (- α * x ^ 2 / 2)

/-- `psi0` is normalized: `∫ |ψ₀|² dx = 1`. -/
theorem psi0_normalized {α : ℝ} (hα : 0 < α) :
    ∫ x : ℝ, psi0 α x ^ 2 = 1 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hαπ : 0 ≤ α / Real.pi := le_of_lt (div_pos hα hπ)
  have hpoint : ∀ x, psi0 α x ^ 2 = Real.sqrt (α / Real.pi) * Real.exp (- α * x ^ 2) := by
    intro x
    unfold psi0
    rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    rw [show Real.exp (- α * x ^ 2 / 2) ^ 2
          = Real.exp (- α * x ^ 2 / 2) * Real.exp (- α * x ^ 2 / 2) from sq _]
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint, integral_const_mul, integral_gaussian]
  rw [← Real.sqrt_mul hαπ]
  rw [show (α / Real.pi) * (Real.pi / α) = 1 from by field_simp]
  exact Real.sqrt_one

/-- `psi0` is an eigenfunction of the (dimensionless) QHO Hamiltonian
`H = -½ d²/dx² + ½ α² x²` with eigenvalue `α/2`, equivalently
`ψ₀''(x) = (α² x² − α) · ψ₀(x)`. -/
theorem psi0_satisfies_TISE (α : ℝ) (x : ℝ) :
    deriv (deriv (psi0 α)) x = (α ^ 2 * x ^ 2 - α) * psi0 α x := by
  set C := Real.sqrt (Real.sqrt (α / Real.pi))
  have hpsi0 : psi0 α = fun y => C * Real.exp (- α * y ^ 2 / 2) := rfl
  have hd1 : ∀ y, HasDerivAt (psi0 α) (-α * y * psi0 α y) y := by
    intro y
    rw [hpsi0]
    have hexp_inner : HasDerivAt (fun z : ℝ => - α * z ^ 2 / 2) (-α * y) y := by
      have hpow : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
        simpa using (hasDerivAt_pow 2 y)
      have := (hpow.const_mul (-α)).div_const 2
      convert this using 1
      ring
    have hexp : HasDerivAt (fun y => Real.exp (- α * y ^ 2 / 2))
                  (Real.exp (- α * y ^ 2 / 2) * (-α * y)) y :=
      hexp_inner.exp
    have := hexp.const_mul C
    convert this using 1
    ring
  have hderiv_eq : deriv (psi0 α) = fun y => -α * y * psi0 α y := by
    funext y; exact (hd1 y).deriv
  rw [hderiv_eq]
  have hg : HasDerivAt (fun y => -α * y * psi0 α y)
              (-α * psi0 α x + (-α * x) * (-α * x * psi0 α x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -α * y) (-α) x := by
      simpa using ((hasDerivAt_id x).const_mul (-α))
    exact h1.mul (hd1 x)
  rw [hg.deriv]
  ring

/-! ## The sudden-frequency-change survival probability. -/

/-- **Ground-state survival probability after a sudden frequency change.**

  If a quantum harmonic oscillator is prepared in the ground state of the
  Hamiltonian with frequency `ω` (i.e. `α = mω/ℏ`), and the frequency is
  suddenly changed to `ω'` (i.e. `β = mω'/ℏ`), the probability of finding
  the system in the new ground state is

  `P₀ = 2 √(αβ) / (α + β)`.

  Reference: A. G. Abanov, *Landau's Theoretical Minimum: Quantum Mechanics*,
  <https://people.tamu.edu/~abanov/QE/TM-QM.pdf>. -/
theorem survival_probability {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ x : ℝ, psi0 β x * psi0 α x) ^ 2 = 2 * Real.sqrt (α * β) / (α + β) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hαπ : 0 ≤ α / Real.pi := le_of_lt (div_pos hα hπ)
  have hβπ : 0 ≤ β / Real.pi := le_of_lt (div_pos hβ hπ)
  have hαβ : 0 < α + β := by linarith
  have hαβ_half : 0 < (α + β) / 2 := by linarith
  have hpoint : ∀ x : ℝ,
      psi0 β x * psi0 α x
        = (Real.sqrt (Real.sqrt (β / Real.pi)) *
          Real.sqrt (Real.sqrt (α / Real.pi))) *
            Real.exp (- ((α + β) / 2) * x ^ 2) := by
    intro x
    unfold psi0
    rw [show Real.sqrt (Real.sqrt (β / Real.pi)) * Real.exp (- β * x ^ 2 / 2) *
            (Real.sqrt (Real.sqrt (α / Real.pi)) * Real.exp (- α * x ^ 2 / 2))
          = Real.sqrt (Real.sqrt (β / Real.pi)) * Real.sqrt (Real.sqrt (α / Real.pi)) *
            (Real.exp (- β * x ^ 2 / 2) * Real.exp (- α * x ^ 2 / 2)) from by ring,
        ← Real.exp_add]
    congr 1
    ring
  have hint : ∫ x : ℝ, psi0 β x * psi0 α x
      = (Real.sqrt (Real.sqrt (β / Real.pi)) *
        Real.sqrt (Real.sqrt (α / Real.pi))) *
          Real.sqrt (Real.pi / ((α + β) / 2)) := by
    simp_rw [hpoint, integral_const_mul, integral_gaussian]
  rw [hint, mul_pow]
  rw [mul_pow]
  rw [Real.sq_sqrt (Real.sqrt_nonneg (β / Real.pi))]
  rw [Real.sq_sqrt (Real.sqrt_nonneg (α / Real.pi))]
  rw [Real.sq_sqrt (le_of_lt (div_pos hπ hαβ_half))]
  rw [← Real.sqrt_mul hβπ (α / Real.pi)]
  rw [show (β / Real.pi) * (α / Real.pi) = (α * β) / (Real.pi * Real.pi) from by ring]
  rw [Real.sqrt_div (mul_nonneg hα.le hβ.le)]
  rw [show Real.sqrt (Real.pi * Real.pi) = Real.pi by
    rw [← sq, Real.sqrt_sq hπ.le]]
  field_simp

end Physlib.QuantumMechanics.HarmonicOscillator
