/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Calculus.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!

# Multivariable Wirtinger calculus and Schwarz's theorem

## i. Overview

This module is the **foundation** of physlib's Wirtinger calculus. It defines the
**directional Wirtinger derivatives** of `f : V → ℂ` on a complex vector space
`V`, along a direction vector `d : V` (a complex number when `V = ℂ`, a vector in
general):

  `∂f/∂d  = (1/2)(∂_d f − i ∂_{i·d} f)`     (`dWirtingerDir`)
  `∂f/∂d̄ = (1/2)(∂_d f + i ∂_{i·d} f)`     (`dWirtingerAntiDir`)

Here `∂_d` and `∂_{i·d}` are the real Fréchet derivatives of `f` along the
*vectors* `d` and `i·d` in `V` (not coordinate symbols). For `V = ℂ` and
`d = 1`, `d` is the real-axis vector and `i·d = i` is the imaginary-axis
vector, so `∂_d f = ∂f/∂x` and `∂_{i·d} f = ∂f/∂y`; the formulas reduce to
the textbook `∂f/∂z = (1/2)(∂_x − i ∂_y)f` and
`∂f/∂z̄ = (1/2)(∂_x + i ∂_y)f`. For general `d`, multiplication by `i` is the
90° rotation supplied by the complex structure on `V`, so `(d, i·d)` is a
rotated copy of the real/imaginary axes.

Everything is built on `fderiv ℝ` and the algebraic lemmas of
`Wirtinger.Basic`, not on any lower Wirtinger layer.

On these operators the module builds the **full directional calculus**:

* real-linearity, the Leibniz rule, and the finite-sum rule (§B);
* the inner-field conjugation lemmas and the two-term chain rule for an outer
  `g : ℂ → ℂ` (§C);
* domain conjugation: precomposing with a conjugate-linear map swaps the two
  operators (§D);
* the holomorphic / anti-holomorphic collapse, keyed on `ℂ`-linearity or
  conjugate-linearity of the real derivative along `d` (§E);
* differentiability and locality of the operators on a `C²` field (§G).

The capstone (§H) is **Schwarz's theorem** in Wirtinger form. On a `C²` field the
holomorphic and anti-holomorphic derivatives in any two directions commute:

  `∂_d ∂_ē f = ∂_ē ∂_d f`     (`dWirtingerDir_dWirtingerAntiDir_comm`)

It is no new analytic fact: it reduces to the symmetry of the second real Fréchet
derivative (`ContDiffAt.isSymmSndFDerivAt`), carried out via the `weightedDirDeriv` bridge
of §F.

## ii. Key results

- `Physlib.Wirtinger.dWirtingerDir` / `dWirtingerAntiDir` : directional Wirtinger
    derivatives of `f : V → ℂ` along `d`.
- `Physlib.Wirtinger.dWirtingerDir_add` / `dWirtingerDir_smul` /
    `dWirtingerDir_mul` / `dWirtingerDir_fun_sum` : real-linearity, the Leibniz
    rule, and the finite-sum rule (each with an anti-holomorphic dual).
- `Physlib.Wirtinger.dWirtingerDir_star_comp` / `dWirtingerAntiDir_star_comp` :
    conjugating the inner field swaps the holomorphic and anti-holomorphic operators.
- `Physlib.Wirtinger.dWirtingerDir_comp` / `dWirtingerAntiDir_comp` : the two-term
    Wirtinger chain rule for an outer `g : ℂ → ℂ`.
- `Physlib.Wirtinger.dWirtingerDir_comp_conjLinear` /
    `dWirtingerAntiDir_comp_conjLinear` : precomposing with a conjugate-`ℂ`-linear
    map swaps the two operators (with the base point and direction transported
    through the map).
- `Physlib.Wirtinger.dWirtingerDir_eq_of_clinear` /
    `dWirtingerAntiDir_eq_zero_of_clinear` : the holomorphic collapse, keyed on
    `ℂ`-linearity of the real derivative along the direction (each with a
    conjugate-`ℂ`-linear dual).
- `Physlib.Wirtinger.differentiableAt_dWirtingerDir` /
    `differentiableAt_dWirtingerAntiDir` : the directional derivative of a `C²`
    field is itself real-differentiable.
- `Physlib.Wirtinger.dWirtingerDir_congr_of_eventuallyEq` /
    `dWirtingerAntiDir_congr_of_eventuallyEq` : the directional derivative depends
    only on the field near the point.
- `Physlib.Wirtinger.dWirtingerDir_dWirtingerAntiDir_comm` : Schwarz's theorem,
    `∂_d ∂_ē f = ∂_ē ∂_d f` for a `C²` `f`.

## iii. Table of contents

- A. The directional Wirtinger operators
- B. Real-linearity and the Leibniz rule
- C. Conjugation and the Wirtinger chain rule
- D. Domain conjugation
- E. The holomorphic collapse
- F. The second-derivative bridge
- G. Differentiability and locality
- H. Schwarz's theorem

## iv. References

- Kreutz-Delgado, *The Complex Gradient Operator and the CR-Calculus*,
  arXiv:0906.4835 — directional/multivariable formulation and two-term chain
  rule (§C); second-order theory behind §F–H.
- Mortini & Rupp, *The Clairaut–Schwarz Theorem for Mixed Wirtinger
  Derivatives*, Bull. Iranian Math. Soc. 48 (2022), 2643–2647 — the mixed
  holomorphic/anti-holomorphic symmetry of §H under the same `C²` hypothesis,
  with the same reduction to real Schwarz used here.
- Koor, Qiu, Kwek & Rebentrost, *A short tutorial on Wirtinger Calculus with
  applications in quantum information*, arXiv:2312.04858 — companion
  exposition of the scalar single/multivariable calculus and sign conventions.

-/

@[expose] public section

noncomputable section

namespace Physlib.Wirtinger

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V}

/-!

## A. The directional Wirtinger operators

The directional operators repackage the real Fréchet derivative of `f` along
the two directions `d` and `i·d` into a holomorphic and an anti-holomorphic
combination — the directional `∂f/∂d`, whose `V = ℂ`, `d = 1` case is the
classical one-variable Wirtinger derivative `∂g/∂z`.

-/

/-- The holomorphic directional Wirtinger derivative `∂f/∂d = (1/2)(∂_d f − i ∂_{i·d} f)`
of `f : V → ℂ` along the direction vector `d : V`. -/
def dWirtingerDir (f : V → ℂ) (d : V) (u : V) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f u d - Complex.I * fderiv ℝ f u (Complex.I • d))

/-- The anti-holomorphic directional Wirtinger derivative
`∂f/∂d̄ = (1/2)(∂_d f + i ∂_{i·d} f)` of `f : V → ℂ` along the direction vector `d : V`. -/
def dWirtingerAntiDir (f : V → ℂ) (d : V) (u : V) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f u d + Complex.I * fderiv ℝ f u (Complex.I • d))

/-- Definitional unfolding of `dWirtingerDir`, used to expand the outer operator
of a composition without touching the inner one. -/
lemma dWirtingerDir_apply (g : V → ℂ) (d u : V) :
    dWirtingerDir g d u
      = (1 / 2 : ℂ) * (fderiv ℝ g u d - Complex.I * fderiv ℝ g u (Complex.I • d)) :=
  rfl

/-- Definitional unfolding of `dWirtingerAntiDir`. -/
lemma dWirtingerAntiDir_apply (g : V → ℂ) (d u : V) :
    dWirtingerAntiDir g d u
      = (1 / 2 : ℂ) * (fderiv ℝ g u d + Complex.I * fderiv ℝ g u (Complex.I • d)) :=
  rfl

/-!

## B. Real-linearity and the Leibniz rule

The directional operators are built from `fderiv ℝ`, so they inherit its
vanishing on constants, additivity, negation, complex-scalar compatibility, the
finite-sum rule, and — through the Fréchet product rule — a Wirtinger Leibniz
rule.

-/

/-- Constants have zero holomorphic directional Wirtinger derivative. -/
@[simp] lemma dWirtingerDir_const (c : ℂ) (d u : V) :
    dWirtingerDir (fun _ : V => c) d u = 0 := by
  simp [dWirtingerDir, fderiv_const_apply]

/-- Constants have zero anti-holomorphic directional Wirtinger derivative. -/
@[simp] lemma dWirtingerAntiDir_const (c : ℂ) (d u : V) :
    dWirtingerAntiDir (fun _ : V => c) d u = 0 := by
  simp [dWirtingerAntiDir, fderiv_const_apply]

/-- `dWirtingerDir` of a negated function. Holds with no differentiability
hypothesis, since `fderiv` of a negation is unconditional. -/
@[simp] lemma dWirtingerDir_neg (g : V → ℂ) (d u : V) :
    dWirtingerDir (fun v => -(g v)) d u = -(dWirtingerDir g d u) := by
  simp only [dWirtingerDir, fderiv_fun_neg, ContinuousLinearMap.neg_apply]; ring

/-- `dWirtingerAntiDir` of a negated function. -/
@[simp] lemma dWirtingerAntiDir_neg (g : V → ℂ) (d u : V) :
    dWirtingerAntiDir (fun v => -(g v)) d u = -(dWirtingerAntiDir g d u) := by
  simp only [dWirtingerAntiDir, fderiv_fun_neg, ContinuousLinearMap.neg_apply]; ring

/-- Additivity of `dWirtingerDir`. -/
lemma dWirtingerDir_add {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (d : V) :
    dWirtingerDir (g + h) d u = dWirtingerDir g d u + dWirtingerDir h d u := by
  simp only [dWirtingerDir, fderiv_add hg hh, ContinuousLinearMap.add_apply]; ring

/-- Additivity of `dWirtingerAntiDir`. -/
lemma dWirtingerAntiDir_add {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (d : V) :
    dWirtingerAntiDir (g + h) d u = dWirtingerAntiDir g d u + dWirtingerAntiDir h d u := by
  simp only [dWirtingerAntiDir, fderiv_add hg hh, ContinuousLinearMap.add_apply]; ring

/-- Compatibility of `dWirtingerDir` with complex scalar multiplication. -/
lemma dWirtingerDir_smul (c : ℂ) {g : V → ℂ} (hg : DifferentiableAt ℝ g u) (d : V) :
    dWirtingerDir (c • g) d u = c • dWirtingerDir g d u := by
  simp only [dWirtingerDir, fderiv_const_smul hg c, ContinuousLinearMap.smul_apply,
    smul_eq_mul]; ring

/-- Compatibility of `dWirtingerAntiDir` with complex scalar multiplication. -/
lemma dWirtingerAntiDir_smul (c : ℂ) {g : V → ℂ} (hg : DifferentiableAt ℝ g u) (d : V) :
    dWirtingerAntiDir (c • g) d u = c • dWirtingerAntiDir g d u := by
  simp only [dWirtingerAntiDir, fderiv_const_smul hg c, ContinuousLinearMap.smul_apply,
    smul_eq_mul]; ring

omit [NormedSpace ℂ V] in
/-- The real Fréchet derivative of a product, evaluated at a tangent `d`. -/
private lemma fderiv_mul_apply {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (d : V) :
    fderiv ℝ (g * h) u d = g u * fderiv ℝ h u d + h u * fderiv ℝ g u d := by
  simpa using DFunLike.congr_fun (fderiv_mul hg hh) d

/-- The Wirtinger Leibniz rule for `dWirtingerDir`. -/
lemma dWirtingerDir_mul {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (d : V) :
    dWirtingerDir (g * h) d u = dWirtingerDir g d u * h u + g u * dWirtingerDir h d u := by
  simp only [dWirtingerDir, fderiv_mul_apply hg hh]; ring

/-- The Wirtinger Leibniz rule for `dWirtingerAntiDir`. -/
lemma dWirtingerAntiDir_mul {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (d : V) :
    dWirtingerAntiDir (g * h) d u =
      dWirtingerAntiDir g d u * h u + g u * dWirtingerAntiDir h d u := by
  simp only [dWirtingerAntiDir, fderiv_mul_apply hg hh]; ring

/-- Finite-sum rule for `dWirtingerDir`. -/
lemma dWirtingerDir_fun_sum {α : Type*} {s : Finset α} {F : α → V → ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (d : V) :
    dWirtingerDir (fun v => ∑ a ∈ s, F a v) d u = ∑ a ∈ s, dWirtingerDir (F a) d u := by
  simp only [dWirtingerDir, fderiv_fun_sum hF, ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]

/-- Finite-sum rule for `dWirtingerAntiDir`. -/
lemma dWirtingerAntiDir_fun_sum {α : Type*} {s : Finset α} {F : α → V → ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (d : V) :
    dWirtingerAntiDir (fun v => ∑ a ∈ s, F a v) d u = ∑ a ∈ s, dWirtingerAntiDir (F a) d u := by
  simp only [dWirtingerAntiDir, fderiv_fun_sum hF, ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]

/-!

## C. Conjugation and the Wirtinger chain rule

Conjugating the function swaps the two operators up to an outer conjugation (via
`fderiv_star_eq`); composing with an outer `g : ℂ → ℂ` gives the two-term
Wirtinger chain rule, with the real-linear decomposition
`realLinear_apply_eq_wirtinger` supplying the holomorphic / anti-holomorphic
split. The only one-variable object is the outer `g`, entering only through its
own directional derivatives `dWirtingerDir g 1` / `dWirtingerAntiDir g 1`.

-/

/-- Conjugating the function swaps the operators up to an outer conjugation:
`∂(f̄)/∂d = conj (∂f/∂d̄)`. -/
lemma dWirtingerDir_star_comp (hf : DifferentiableAt ℝ f u) (d : V) :
    dWirtingerDir (fun v => star (f v)) d u = star (dWirtingerAntiDir f d u) := by
  simp only [dWirtingerDir, dWirtingerAntiDir]
  rw [fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, Complex.star_def, map_mul, map_add, map_div₀, map_one,
    map_ofNat, Complex.conj_I]
  ring

/-- Conjugating the function swaps the operators up to an outer conjugation:
`∂(f̄)/∂d̄ = conj (∂f/∂d)`. Dual of `dWirtingerDir_star_comp`. -/
lemma dWirtingerAntiDir_star_comp (hf : DifferentiableAt ℝ f u) (d : V) :
    dWirtingerAntiDir (fun v => star (f v)) d u = star (dWirtingerDir f d u) := by
  simp only [dWirtingerDir, dWirtingerAntiDir]
  rw [fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, Complex.star_def, map_mul, map_sub, map_div₀, map_one,
    map_ofNat, Complex.conj_I]
  ring

/-- The two-term Wirtinger chain rule for an outer `g : ℂ → ℂ`, proved for both
operators at once: after unfolding, the real chain rule plus the Wirtinger
decomposition of `fderiv ℝ g (f u)` close the goal by `ring`. Re-exposed as
`dWirtingerDir_comp` / `dWirtingerAntiDir_comp`. -/
private lemma dWirtingerDir_comp_aux {g : ℂ → ℂ} (hg : DifferentiableAt ℝ g (f u))
    (hf : DifferentiableAt ℝ f u) (d : V) :
    dWirtingerDir (fun v => g (f v)) d u =
        dWirtingerDir g 1 (f u) * dWirtingerDir f d u
          + dWirtingerAntiDir g 1 (f u) * dWirtingerDir (fun v => star (f v)) d u
      ∧ dWirtingerAntiDir (fun v => g (f v)) d u =
        dWirtingerDir g 1 (f u) * dWirtingerAntiDir f d u
          + dWirtingerAntiDir g 1 (f u) * dWirtingerAntiDir (fun v => star (f v)) d u := by
  constructor <;>
  · simp only [dWirtingerDir, dWirtingerAntiDir, smul_eq_mul, mul_one]
    rw [show (fun v => g (f v)) = g ∘ f from rfl, fderiv_comp u hg hf, fderiv_star_eq hf]
    simp only [ContinuousLinearMap.comp_apply]
    have hA := realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u d)
    have hB := realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u (Complex.I • d))
    rw [hA, hB]
    simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, Complex.star_def]
    ring

/-- The two-term Wirtinger chain rule for `dWirtingerDir`. Writing `z = f`, the
composite `g(z, z̄)` depends on `d` through both `z` and `z̄`, so `∂(g∘f)/∂d` is a
sum of two channels — the holomorphic `(∂g/∂z)·(∂f/∂d)` and the anti-holomorphic
`(∂g/∂z̄)·(∂(f̄)/∂d)`. The outer `g` enters at direction `1` (its single variable),
the inner `f` at `d`. -/
lemma dWirtingerDir_comp {g : ℂ → ℂ} (hg : DifferentiableAt ℝ g (f u))
    (hf : DifferentiableAt ℝ f u) (d : V) :
    dWirtingerDir (fun v => g (f v)) d u =
      dWirtingerDir g 1 (f u) * dWirtingerDir f d u
        + dWirtingerAntiDir g 1 (f u) * dWirtingerDir (fun v => star (f v)) d u :=
  (dWirtingerDir_comp_aux hg hf d).1

/-- The two-term Wirtinger chain rule for `dWirtingerAntiDir`, the `∂/∂d̄` dual of
`dWirtingerDir_comp`: the same two channels, with the inner derivative now taken
along `d̄`, `(∂g/∂z)·(∂f/∂d̄) + (∂g/∂z̄)·(∂(f̄)/∂d̄)`. -/
lemma dWirtingerAntiDir_comp {g : ℂ → ℂ} (hg : DifferentiableAt ℝ g (f u))
    (hf : DifferentiableAt ℝ f u) (d : V) :
    dWirtingerAntiDir (fun v => g (f v)) d u =
      dWirtingerDir g 1 (f u) * dWirtingerAntiDir f d u
        + dWirtingerAntiDir g 1 (f u) * dWirtingerAntiDir (fun v => star (f v)) d u :=
  (dWirtingerDir_comp_aux hg hf d).2

/-!

## D. Domain conjugation

The §C lemmas conjugate a function's *output*; this section conjugates its
*input*. Precomposing `g` with a domain map `L` — forming `g ∘ L` — relates the
directional derivatives of the composite to those of `g`.

The map `L : V → V'` is **conjugate-`ℂ`-linear**: real-linear and continuous, but
anti-commuting with multiplication by `i`,

  `L (i · x) = −(i · L x)`,

the abstract form of complex conjugation (`conj (i·x) = −i · conj x`). That sign
flip is what turns a holomorphic derivative into an anti-holomorphic one: in the holomorphic
combination `(1/2)(∂_d − i ∂_{i·d})`, the `i·d` term picks up the minus from `L`,
converting it into the anti-holomorphic combination. So precomposition **swaps** the
two operators and transports the base point and direction through `L`:

  `∂(g ∘ L)/∂d`  at `u`  =  `∂g/∂d̄`  at `L u`, along `L d`

(`dWirtingerDir_comp_conjLinear`, with the dual `∂(g ∘ L)/∂d̄ = ∂g/∂d`).

Use it to differentiate a function whose input has been conjugated (`g ∘ L`, e.g.
`g(z̄)`). The swap rewrites that derivative as the *other* operator on the plain
`g`, exposing it for the §E collapse: for a holomorphic `g`, `g ∘ L` then has
vanishing holomorphic derivative and an anti-holomorphic derivative equal to the complex
derivative of `g` — the Cauchy–Riemann split for anti-holomorphic dependence. It
is the input-side counterpart of §C's output conjugation, the two together fixing
how the operators behave under conjugation on either side. The proof is
`restrictScalars`-free (only the anti-commutation of `L` enters) and holds over
any complex `V`, `V'`.

-/

section DomainConjugation

variable {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedSpace ℂ V']

omit [NormedSpace ℂ V] [NormedSpace ℂ V'] in
/-- The real Fréchet derivative of `g ∘ L` at `u`, applied to `x`, is the
derivative of `g` at `L u` applied to `L x` — the chain rule for an inner
continuous linear map. -/
private lemma fderiv_comp_clm_apply {g : V' → ℂ} {L : V →L[ℝ] V'} {u : V}
    (hg : DifferentiableAt ℝ g (L u)) (x : V) :
    fderiv ℝ (fun v => g (L v)) u x = fderiv ℝ g (L u) (L x) := by
  rw [show (fun v => g (L v)) = g ∘ (L : V → V') from rfl,
    fderiv_comp u hg L.differentiableAt, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply]

/-- Precomposing with a conjugate-`ℂ`-linear `L` turns the holomorphic directional
derivative into the anti-holomorphic one at the transported point and direction. -/
lemma dWirtingerDir_comp_conjLinear {g : V' → ℂ} {L : V →L[ℝ] V'} {u : V}
    (hL : ∀ x : V, L (Complex.I • x) = -(Complex.I • L x))
    (hg : DifferentiableAt ℝ g (L u)) (d : V) :
    dWirtingerDir (fun v => g (L v)) d u = dWirtingerAntiDir g (L d) (L u) := by
  simp only [dWirtingerDir, dWirtingerAntiDir, fderiv_comp_clm_apply hg, hL, map_neg]; ring

/-- Dual of `dWirtingerDir_comp_conjLinear`. -/
lemma dWirtingerAntiDir_comp_conjLinear {g : V' → ℂ} {L : V →L[ℝ] V'} {u : V}
    (hL : ∀ x : V, L (Complex.I • x) = -(Complex.I • L x))
    (hg : DifferentiableAt ℝ g (L u)) (d : V) :
    dWirtingerAntiDir (fun v => g (L v)) d u = dWirtingerDir g (L d) (L u) := by
  simp only [dWirtingerDir, dWirtingerAntiDir, fderiv_comp_clm_apply hg, hL, map_neg]; ring

end DomainConjugation

/-!

## E. The holomorphic collapse

When the real Fréchet derivative is `ℂ`-linear along the chosen direction
(`Df(i·d) = i·Df(d)` — the Cauchy–Riemann content), `dWirtingerDir` returns the
full derivative and `dWirtingerAntiDir` vanishes; dually for a conjugate-linear
derivative. The hypothesis is `restrictScalars`-free, so this collapse is
domain-general and proven once here; producing the hypothesis from holomorphy is
the only step that meets the `ℝ`/`ℂ` `restrictScalars` diamond, and is done per
concrete domain by the consumers.

-/

/-- Holomorphic collapse: along a direction where `Df` is `ℂ`-linear, the holomorphic
derivative is the full real derivative. -/
lemma dWirtingerDir_eq_of_clinear {d : V}
    (h : fderiv ℝ f u (Complex.I • d) = Complex.I • fderiv ℝ f u d) :
    dWirtingerDir f d u = fderiv ℝ f u d := by
  simp only [dWirtingerDir, h, smul_eq_mul]; rw [← mul_assoc, Complex.I_mul_I]; ring

/-- Holomorphic collapse: the anti-holomorphic derivative vanishes along a direction
of `ℂ`-linearity. -/
lemma dWirtingerAntiDir_eq_zero_of_clinear {d : V}
    (h : fderiv ℝ f u (Complex.I • d) = Complex.I • fderiv ℝ f u d) :
    dWirtingerAntiDir f d u = 0 := by
  simp only [dWirtingerAntiDir, h, smul_eq_mul]; rw [← mul_assoc, Complex.I_mul_I]; ring

/-- Anti-holomorphic collapse: a direction of conjugate-`ℂ`-linearity kills the
holomorphic derivative. -/
lemma dWirtingerDir_eq_zero_of_antilinear {d : V}
    (h : fderiv ℝ f u (Complex.I • d) = -(Complex.I • fderiv ℝ f u d)) :
    dWirtingerDir f d u = 0 := by
  simp only [dWirtingerDir, h, smul_eq_mul, mul_neg]; rw [← mul_assoc, Complex.I_mul_I]; ring

/-- Anti-holomorphic collapse: the anti-holomorphic derivative is the full real
derivative along a direction of conjugate-`ℂ`-linearity. -/
lemma dWirtingerAntiDir_eq_of_antilinear {d : V}
    (h : fderiv ℝ f u (Complex.I • d) = -(Complex.I • fderiv ℝ f u d)) :
    dWirtingerAntiDir f d u = fderiv ℝ f u d := by
  simp only [dWirtingerAntiDir, h, smul_eq_mul, mul_neg]; rw [← mul_assoc, Complex.I_mul_I]; ring

/-!

## F. The second-derivative bridge

Each directional operator is, definitionally, the combination
`(1/2)(∂_d f + c · ∂_{i·d} f)` of the real Fréchet derivative along a
direction `d` and its `i`-rotation `i·d` (`c = −i` holomorphic, `c = +i`
anti-holomorphic) — so the two directions are not independent: `b₂ = i·b₁`.
The `weightedDirDeriv` records this combination as a function of the base
point, generalised to two free directions `b₁`, `b₂`; that relation plays no
role in differentiating the combination, so it is dropped here. Differentiating
a `weightedDirDeriv` once more sends each first derivative to the second real
Fréchet derivative `fderiv ℝ (fderiv ℝ f) u`, evaluated on two slots.

Because `weightedDirDeriv` and the bridge (`fderiv_weightedDirDeriv`) are
generic in the weight `c` and the two directions `b₁`, `b₂`, one lemma serves
*every* second-order combination. The four pairings —
holomorphic∘holomorphic, holomorphic∘anti-holomorphic,
anti-holomorphic∘holomorphic, anti-holomorphic∘anti-holomorphic — are just four
instantiations of the same bridge, differing only in the complex coefficients;
each reduces to the same `fderiv ℝ (fderiv ℝ f) u` on the four directions `d`,
`i·d`, `e`, `i·e`. §H discharges the mixed pairing (the one Kähler geometry
needs); the other three would follow from this bridge with no new plumbing — a
different choice of `(c, b₁, b₂)`, then `ContDiffAt.isSymmSndFDerivAt` and
`ring`.

-/

/-- The combination `v ↦ (1/2)(∂f/∂b₁ + c · ∂f/∂b₂)` of the real Fréchet
derivative of `f` along two directions. `dWirtingerDir f d` is this with
`c = -i`, `b₁ = d`, `b₂ = i·d`; `dWirtingerAntiDir f d` with `c = i`. -/
private def weightedDirDeriv (f : V → ℂ) (c : ℂ) (b₁ b₂ : V) : V → ℂ :=
  fun v => (1 / 2 : ℂ) * (fderiv ℝ f v b₁ + c * fderiv ℝ f v b₂)

omit [NormedSpace ℂ V] in
/-- `f` is `C¹` in its first derivative, so `fderiv ℝ f` is differentiable at
`u` — the regularity that makes a `weightedDirDeriv` (hence a directional derivative)
differentiable. -/
private lemma differentiableAt_fderiv (hf2 : ContDiffAt ℝ 2 f u) :
    DifferentiableAt ℝ (fderiv ℝ f) u :=
  (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

omit [NormedSpace ℂ V] in
/-- The field `v ↦ ∂f/∂b` is the evaluation map `· b` composed with `fderiv ℝ f`,
so when `fderiv ℝ f` is differentiable its derivative is `fderiv ℝ (fderiv ℝ f) u`
post-composed with that evaluation. -/
private lemma hasFDerivAt_fderiv_apply (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (b : V) :
    HasFDerivAt (fun v => fderiv ℝ f v b)
      ((ContinuousLinearMap.apply ℝ ℂ b).comp (fderiv ℝ (fderiv ℝ f) u)) u :=
  (ContinuousLinearMap.apply ℝ ℂ b).hasFDerivAt.comp u hf'.hasFDerivAt

omit [NormedSpace ℂ V] in
/-- The `weightedDirDeriv` is differentiable wherever `fderiv ℝ f` is. -/
private lemma hasFDerivAt_weightedDirDeriv (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (c : ℂ) (b₁ b₂ : V) :
    HasFDerivAt (weightedDirDeriv f c b₁ b₂)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ b₁).comp (fderiv ℝ (fderiv ℝ f) u)
        + c • (ContinuousLinearMap.apply ℝ ℂ b₂).comp (fderiv ℝ (fderiv ℝ f) u))) u :=
  ((hasFDerivAt_fderiv_apply hf' b₁).add
    ((hasFDerivAt_fderiv_apply hf' b₂).const_mul c)).const_mul (1 / 2)

omit [NormedSpace ℂ V] in
/-- The bridge: differentiating a `weightedDirDeriv` along a third direction `a`
lands on the second real Fréchet derivative `fderiv ℝ (fderiv ℝ f) u a b` in the
two slots. -/
private lemma fderiv_weightedDirDeriv (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (c : ℂ) (b₁ b₂ a : V) :
    fderiv ℝ (weightedDirDeriv f c b₁ b₂) u a
      = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) u a b₁
          + c * fderiv ℝ (fderiv ℝ f) u a b₂) := by
  rw [(hasFDerivAt_weightedDirDeriv hf' c b₁ b₂).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply,
    smul_eq_mul, mul_add]

/-- A directional derivative is a `weightedDirDeriv`: anti-holomorphic with `c = i`. -/
private lemma dWirtingerAntiDir_eq_weightedDirDeriv (e : V) :
    (fun v => dWirtingerAntiDir f e v) = weightedDirDeriv f Complex.I e (Complex.I • e) :=
  rfl

/-- A directional derivative is a `weightedDirDeriv`: holomorphic with `c = -i`. -/
private lemma dWirtingerDir_eq_weightedDirDeriv (d : V) :
    (fun v => dWirtingerDir f d v) = weightedDirDeriv f (-Complex.I) d (Complex.I • d) := by
  funext v; simp only [dWirtingerDir, weightedDirDeriv]; ring

/-- Differentiating the anti-holomorphic directional derivative lands on the second
real Fréchet derivative in the two slots. -/
private lemma fderiv_dWirtingerAntiDir (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (e a : V) :
    fderiv ℝ (fun v => dWirtingerAntiDir f e v) u a
      = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) u a e
          + Complex.I * fderiv ℝ (fderiv ℝ f) u a (Complex.I • e)) := by
  rw [dWirtingerAntiDir_eq_weightedDirDeriv, fderiv_weightedDirDeriv hf']

/-- Differentiating the holomorphic directional derivative lands on the second real
Fréchet derivative in the two slots. -/
private lemma fderiv_dWirtingerDir (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (d a : V) :
    fderiv ℝ (fun v => dWirtingerDir f d v) u a
      = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) u a d
          - Complex.I * fderiv ℝ (fderiv ℝ f) u a (Complex.I • d)) := by
  rw [dWirtingerDir_eq_weightedDirDeriv, fderiv_weightedDirDeriv hf']; ring

/-!

## G. Differentiability and locality

Two regularity facts about the operators viewed as fields in the base point.
**Differentiability**: on a `C²` field the directional derivative `v ↦ ∂f/∂d (v)`
is itself real-differentiable (`differentiableAt_dWirtingerDir`) — by §F it is a
`weightedDirDeriv`, and `fderiv ℝ f` is differentiable for a `C²` `f`. This is the
regularity §H needs to differentiate a Wirtinger derivative a second time.
**Locality**: each operator depends only on `f` near `u`, inherited from
`fderiv ℝ` — fields agreeing on a neighbourhood of `u` have equal directional
derivative there (`dWirtingerDir_congr_of_eventuallyEq`).

-/

/-- On a `C²` field the holomorphic directional derivative is itself
real-differentiable. -/
lemma differentiableAt_dWirtingerDir (hf2 : ContDiffAt ℝ 2 f u) (d : V) :
    DifferentiableAt ℝ (fun v => dWirtingerDir f d v) u := by
  rw [dWirtingerDir_eq_weightedDirDeriv]
  exact (hasFDerivAt_weightedDirDeriv (differentiableAt_fderiv hf2) _ _ _).differentiableAt

/-- On a `C²` field the anti-holomorphic directional derivative is itself
real-differentiable. -/
lemma differentiableAt_dWirtingerAntiDir (hf2 : ContDiffAt ℝ 2 f u) (e : V) :
    DifferentiableAt ℝ (fun v => dWirtingerAntiDir f e v) u := by
  rw [dWirtingerAntiDir_eq_weightedDirDeriv]
  exact (hasFDerivAt_weightedDirDeriv (differentiableAt_fderiv hf2) _ _ _).differentiableAt

/-- The holomorphic directional derivative depends only on the field near the point:
fields agreeing on a neighbourhood have equal derivative. -/
lemma dWirtingerDir_congr_of_eventuallyEq {f₁ f₂ : V → ℂ} {u : V}
    (h : f₁ =ᶠ[nhds u] f₂) (d : V) :
    dWirtingerDir f₁ d u = dWirtingerDir f₂ d u := by
  simp only [dWirtingerDir, h.fderiv_eq]

/-- The anti-holomorphic directional derivative depends only on the field near the
point; dual of `dWirtingerDir_congr_of_eventuallyEq`. -/
lemma dWirtingerAntiDir_congr_of_eventuallyEq {f₁ f₂ : V → ℂ} {u : V}
    (h : f₁ =ᶠ[nhds u] f₂) (d : V) :
    dWirtingerAntiDir f₁ d u = dWirtingerAntiDir f₂ d u := by
  simp only [dWirtingerAntiDir, h.fderiv_eq]

/-!

## H. Schwarz's theorem

-/

/-- **Schwarz's theorem** for the directional Wirtinger operators: on a `C²`
field the holomorphic and anti-holomorphic directional derivatives in any two directions
commute, `∂_d ∂_ē f = ∂_ē ∂_d f`.

Both orders expand, through the bridge, into a real-linear combination of
the second real Fréchet derivative `fderiv ℝ (fderiv ℝ f) u` on the four
directions `d`, `i·d`, `e`, `i·e`; the two orders differ only by transposing the
two slots of that second derivative, which `ContDiffAt.isSymmSndFDerivAt`
equates. -/
theorem dWirtingerDir_dWirtingerAntiDir_comm (hf2 : ContDiffAt ℝ 2 f u) (d e : V) :
    dWirtingerDir (fun v => dWirtingerAntiDir f e v) d u
      = dWirtingerAntiDir (fun v => dWirtingerDir f d v) e u := by
  have hf' := differentiableAt_fderiv hf2
  have hsymm : IsSymmSndFDerivAt ℝ f u := hf2.isSymmSndFDerivAt (by simp)
  rw [dWirtingerDir_apply (fun v => dWirtingerAntiDir f e v) d u,
    dWirtingerAntiDir_apply (fun v => dWirtingerDir f d v) e u,
    fderiv_dWirtingerAntiDir hf', fderiv_dWirtingerAntiDir hf',
    fderiv_dWirtingerDir hf', fderiv_dWirtingerDir hf',
    hsymm.eq e d, hsymm.eq e (Complex.I • d),
    hsymm.eq (Complex.I • e) d, hsymm.eq (Complex.I • e) (Complex.I • d)]
  ring

end Physlib.Wirtinger

end

end
