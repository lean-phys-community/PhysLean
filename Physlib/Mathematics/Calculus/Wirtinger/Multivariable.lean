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

## Notation

* The direction is a *subscript*: `d_v f` is the derivative in direction `v` of `f` at the
  (implicit) base point `u`.
* Three operators share this form — the total real derivative `d_v f`, and its holomorphic
  and anti-holomorphic Wirtinger parts `∂_v f`, `∂̄_v f` (straight `d` for the total, `∂`/`∂̄`
  for the parts).
* A `/∂` fraction differentiates with respect to a *variable* (not a direction): either a
  real coordinate, `∂f/∂x`, `∂f/∂z` (the `V = ℂ` case below), or the single argument of a
  one-variable function in the chain rule, `∂g/∂f`, `∂g/∂f̄` (outer `g : ℂ → ℂ`, inner
  `f : V → ℂ`; Leibniz form, §D).
* For iterated derivatives (§I) the operators compose, `∂_v ∂̄_w f`.
* `f̄` is the pointwise conjugate `p ↦ conj (f p)`.
* `v`, `w` are directions in `V`.
* `u : V` is the *fixed* base point a derivative is evaluated at — the implicit point in the
  subscript notation.
* `p : V` is the *bound* base-point variable when a derivative is repackaged as a function of
  position: the inner field of an iterated operator (`fun p => dWirtingerAntiDir f w p`, §I),
  or the composite in the chain rule (`fun p => g (f p)`, §D).

Base points (`u`, `p`) and directions (`v`, `w`) all live in `V`: a vector space is its own
tangent space, so a displacement from a point is again an element of `V` (`u + t·v`).

## i. Overview

This module is the **foundation** of physlib's Wirtinger calculus. It defines the
**directional Wirtinger derivatives** of `f : V → ℂ` on a complex vector space `V`, along a
direction `v : V` (a complex number when `V = ℂ`, a vector in general):

  `∂_v f  = (1/2)(d_v f − i·d_{i·v} f)`     (`dWirtingerDir`)
  `∂̄_v f = (1/2)(d_v f + i·d_{i·v} f)`     (`dWirtingerAntiDir`)

**Real derivative.** `d_v f = fderiv ℝ f u v` is the real Fréchet derivative along `v`: the
limit `lim_{t→0} (f(u + t·v) − f(u)) / t` over real `t`. So "real" names the scalar `t`, not
the direction `v`; over all `v` these limits form the `ℝ`-linear map `fderiv ℝ f u : V → ℂ`.

**Rotation.** `i·v` is `v` turned 90° by the complex structure on `V`; `(v, i·v)` is an
orthogonal frame in `v`'s own (arbitrary) direction, a rotated, rescaled copy of the axes
`(1, i)`. For `V = ℂ` take `v = 1`: then `d_v f = ∂f/∂x`, `d_{i·v} f = ∂f/∂y`, and with
`z = x + i y`, `z̄ = x − i y` the formulas recover the classical
`∂f/∂z = (1/2)(∂_x − i ∂_y)f`, `∂f/∂z̄ = (1/2)(∂_x + i ∂_y)f`.

**Holomorphy.** `ℝ`-linearity commutes with real scaling and addition; `ℂ`-linearity adds
commuting with `i`, i.e. `d_{i·v} f = i·d_v f`. The real derivative always has the first;
the gap `d_{i·v} f − i·d_v f` to the second is exactly `−2i·∂̄_v f`. So `∂̄_v f` is the
obstruction to `ℂ`-linearity — it vanishes iff `f` is holomorphic.

**Splitting.** The two operators split the real derivative into holomorphic and
anti-holomorphic parts — the directional form of `d = ∂ + ∂̄` (Dolbeault) — summing back to

  `d_v f = ∂_v f + ∂̄_v f`.

This is the coordinate-free form of treating `z` and `z̄` as independent (the `V = ℂ` case
above). When `f` is holomorphic the anti-holomorphic half drops and `∂_v f` is the ordinary
complex derivative (§F). Everything rests on `fderiv ℝ` and `Wirtinger.Basic`, no lower
Wirtinger layer.

On these operators the module builds the **full directional calculus**:

* real-linearity, the Leibniz rule, and the finite-sum rule (§B);
* the inner-field conjugation lemmas, swapping the two operators (§C);
* the two-term Wirtinger chain rule for an outer `g : ℂ → ℂ` (§D);
* domain conjugation: precomposing with a conjugate-linear map swaps the two
  operators (§E);
* the holomorphic / anti-holomorphic collapse, keyed on `ℂ`-linearity or
  conjugate-linearity of the real derivative along `v` (§F);
* differentiability and locality of the operators on a `C²` field (§H).

The capstone (§I) is **Schwarz's theorem** in Wirtinger form. On a `C²` field the
holomorphic and anti-holomorphic derivatives in any two directions commute:

  `∂_v ∂̄_w f = ∂̄_w ∂_v f`     (`dWirtingerDir_dWirtingerAntiDir_comm`)

It is no new analytic fact: it reduces to the symmetry of the second real Fréchet
derivative (`ContDiffAt.isSymmSndFDerivAt`), carried out via the `weightedDirDeriv` bridge
of §G.

## ii. Key results

- `Physlib.Wirtinger.dWirtingerDir` / `dWirtingerAntiDir` : directional Wirtinger
    derivatives of `f : V → ℂ` along `v`.
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
    `∂_v ∂̄_w f = ∂̄_w ∂_v f` for a `C²` `f`.

## iii. Table of contents

- A. The directional Wirtinger operators
- B. Real-linearity and the Leibniz rule
- C. Conjugation
- D. The Wirtinger chain rule
- E. Domain conjugation
- F. The holomorphic collapse
- G. The second-derivative bridge
- H. Differentiability and locality
- I. Schwarz's theorem

## iv. References

- Kreutz-Delgado, *The Complex Gradient Operator and the CR-Calculus*,
  arXiv:0906.4835 — directional/multivariable formulation and two-term chain
  rule (§D); second-order theory behind §G–I.
- Mortini & Rupp, *The Clairaut–Schwarz Theorem for Mixed Wirtinger
  Derivatives*, Bull. Iranian Math. Soc. 48 (2022), 2643–2647 — the mixed
  holomorphic/anti-holomorphic symmetry of §I under the same `C²` hypothesis,
  with the same reduction to real Schwarz used here.
- Koor, Qiu, Kwek & Rebentrost, *A short tutorial on Wirtinger Calculus with
  applications in quantum information*, arXiv:2312.04858 — companion
  exposition of the scalar single/multivariable calculus and sign conventions.
- *Complex differential form*, Wikipedia (section "The Dolbeault operators") — the
  `d = ∂ + ∂̄` splitting and the `∂`/`∂̄` notation this module's operators are named after.

-/

@[expose] public section

noncomputable section

namespace Physlib.Wirtinger

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V}

/-!

## A. The directional Wirtinger operators

The two directional operators repackage the real Fréchet derivative of `f` along
`v` and `i·v` into a holomorphic part `∂_v f` and an anti-holomorphic part `∂̄_v f`,
the combinations `(1/2)(d_v f ∓ i·d_{i·v} f)`. Both are `ℂ`-valued and depend on the
base point `u`.

-/

/-- The holomorphic directional Wirtinger derivative `∂_v f = (1/2)(d_v f − i·d_{i·v} f)`
of `f : V → ℂ` along the direction vector `v : V`. -/
def dWirtingerDir (f : V → ℂ) (v : V) (u : V) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f u v - Complex.I * fderiv ℝ f u (Complex.I • v))

/-- The anti-holomorphic directional Wirtinger derivative
`∂̄_v f = (1/2)(d_v f + i·d_{i·v} f)` of `f : V → ℂ` along the direction vector `v : V`. -/
def dWirtingerAntiDir (f : V → ℂ) (v : V) (u : V) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f u v + Complex.I * fderiv ℝ f u (Complex.I • v))

/-- Definitional unfolding of `dWirtingerDir`, used to expand the outer operator
of a composition without touching the inner one. -/
lemma dWirtingerDir_apply (g : V → ℂ) (v u : V) :
    dWirtingerDir g v u
      = (1 / 2 : ℂ) * (fderiv ℝ g u v - Complex.I * fderiv ℝ g u (Complex.I • v)) :=
  rfl

/-- Definitional unfolding of `dWirtingerAntiDir`. -/
lemma dWirtingerAntiDir_apply (g : V → ℂ) (v u : V) :
    dWirtingerAntiDir g v u
      = (1 / 2 : ℂ) * (fderiv ℝ g u v + Complex.I * fderiv ℝ g u (Complex.I • v)) :=
  rfl

/-!

## B. Real-linearity and the Leibniz rule

The directional operators are built from `fderiv ℝ`, so they inherit its
vanishing on constants, additivity, negation, complex-scalar compatibility, the
finite-sum rule, and — through the Fréchet product rule — a Wirtinger Leibniz
rule.

-/

/-- Constants have zero holomorphic directional Wirtinger derivative, `∂_v c = 0`. -/
@[simp] lemma dWirtingerDir_const (c : ℂ) (v u : V) :
    dWirtingerDir (fun _ : V => c) v u = 0 := by
  simp [dWirtingerDir, fderiv_const_apply]

/-- Constants have zero anti-holomorphic directional Wirtinger derivative, `∂̄_v c = 0`. -/
@[simp] lemma dWirtingerAntiDir_const (c : ℂ) (v u : V) :
    dWirtingerAntiDir (fun _ : V => c) v u = 0 := by
  simp [dWirtingerAntiDir, fderiv_const_apply]

/-- `dWirtingerDir` of a negated function, `∂_v(−g) = −∂_v g`. Holds with no
differentiability hypothesis, since `fderiv` of a negation is unconditional. -/
@[simp] lemma dWirtingerDir_neg (g : V → ℂ) (v u : V) :
    dWirtingerDir (fun p => -(g p)) v u = -(dWirtingerDir g v u) := by
  simp only [dWirtingerDir, fderiv_fun_neg, ContinuousLinearMap.neg_apply]; ring

/-- `dWirtingerAntiDir` of a negated function, `∂̄_v(−g) = −∂̄_v g`. -/
@[simp] lemma dWirtingerAntiDir_neg (g : V → ℂ) (v u : V) :
    dWirtingerAntiDir (fun p => -(g p)) v u = -(dWirtingerAntiDir g v u) := by
  simp only [dWirtingerAntiDir, fderiv_fun_neg, ContinuousLinearMap.neg_apply]; ring

/-- Additivity of `dWirtingerDir`, `∂_v(g + h) = ∂_v g + ∂_v h`. -/
lemma dWirtingerDir_add {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (v : V) :
    dWirtingerDir (g + h) v u = dWirtingerDir g v u + dWirtingerDir h v u := by
  simp only [dWirtingerDir, fderiv_add hg hh, ContinuousLinearMap.add_apply]; ring

/-- Additivity of `dWirtingerAntiDir`, `∂̄_v(g + h) = ∂̄_v g + ∂̄_v h`. -/
lemma dWirtingerAntiDir_add {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (v : V) :
    dWirtingerAntiDir (g + h) v u = dWirtingerAntiDir g v u + dWirtingerAntiDir h v u := by
  simp only [dWirtingerAntiDir, fderiv_add hg hh, ContinuousLinearMap.add_apply]; ring

/-- Compatibility of `dWirtingerDir` with complex scalar multiplication,
`∂_v(c·g) = c·∂_v g`. -/
lemma dWirtingerDir_smul (c : ℂ) {g : V → ℂ} (hg : DifferentiableAt ℝ g u) (v : V) :
    dWirtingerDir (c • g) v u = c • dWirtingerDir g v u := by
  simp only [dWirtingerDir, fderiv_const_smul hg c, ContinuousLinearMap.smul_apply,
    smul_eq_mul]; ring

/-- Compatibility of `dWirtingerAntiDir` with complex scalar multiplication,
`∂̄_v(c·g) = c·∂̄_v g`. -/
lemma dWirtingerAntiDir_smul (c : ℂ) {g : V → ℂ} (hg : DifferentiableAt ℝ g u) (v : V) :
    dWirtingerAntiDir (c • g) v u = c • dWirtingerAntiDir g v u := by
  simp only [dWirtingerAntiDir, fderiv_const_smul hg c, ContinuousLinearMap.smul_apply,
    smul_eq_mul]; ring

omit [NormedSpace ℂ V] in
/-- The real Fréchet derivative of a product, evaluated at a tangent `v`. -/
private lemma fderiv_mul_apply {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (v : V) :
    fderiv ℝ (g * h) u v = g u * fderiv ℝ h u v + h u * fderiv ℝ g u v := by
  simpa using DFunLike.congr_fun (fderiv_mul hg hh) v

/-- The Wirtinger Leibniz rule for `dWirtingerDir`,
`∂_v(g·h) = ∂_v g·h + g·∂_v h`. -/
lemma dWirtingerDir_mul {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (v : V) :
    dWirtingerDir (g * h) v u = dWirtingerDir g v u * h u + g u * dWirtingerDir h v u := by
  simp only [dWirtingerDir, fderiv_mul_apply hg hh]; ring

/-- The Wirtinger Leibniz rule for `dWirtingerAntiDir`,
`∂̄_v(g·h) = ∂̄_v g·h + g·∂̄_v h`. -/
lemma dWirtingerAntiDir_mul {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (v : V) :
    dWirtingerAntiDir (g * h) v u =
      dWirtingerAntiDir g v u * h u + g u * dWirtingerAntiDir h v u := by
  simp only [dWirtingerAntiDir, fderiv_mul_apply hg hh]; ring

/-- Finite-sum rule for `dWirtingerDir`, `∂_v(∑ₐ Fₐ) = ∑ₐ ∂_v Fₐ`. -/
lemma dWirtingerDir_fun_sum {α : Type*} {s : Finset α} {F : α → V → ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (v : V) :
    dWirtingerDir (fun p => ∑ a ∈ s, F a p) v u = ∑ a ∈ s, dWirtingerDir (F a) v u := by
  simp only [dWirtingerDir, fderiv_fun_sum hF, ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]

/-- Finite-sum rule for `dWirtingerAntiDir`, `∂̄_v(∑ₐ Fₐ) = ∑ₐ ∂̄_v Fₐ`. -/
lemma dWirtingerAntiDir_fun_sum {α : Type*} {s : Finset α} {F : α → V → ℂ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (v : V) :
    dWirtingerAntiDir (fun p => ∑ a ∈ s, F a p) v u = ∑ a ∈ s, dWirtingerAntiDir (F a) v u := by
  simp only [dWirtingerAntiDir, fderiv_fun_sum hF, ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]

/-!

## C. Conjugation

Conjugating the inner field `f` swaps the two operators, up to an outer conjugation on the
value (`fderiv_star_eq`):

  `∂_v f̄ = conj (∂̄_v f)`,     `∂̄_v f̄ = conj (∂_v f)`.

Each operator applied to the conjugate field `f̄` returns the *other* operator on `f`,
conjugated — the bar exchanges holomorphic and anti-holomorphic dependence. Concretely, on
`V = ℂ` take the holomorphic `f(z) = z`, with `∂_z z = 1`, `∂̄_z z = 0`:

* `∂_v f̄ = conj (∂̄_v f)` reads `∂_z z̄ = conj 0 = 0` — the conjugate `z̄` has no
  holomorphic part;
* the dual `∂̄_v f̄ = conj (∂_v f)` reads `∂̄_z z̄ = conj 1 = 1` — all of `z̄`'s dependence
  sits in the anti-holomorphic operator.

The chain rule of §D builds on these to handle a conjugated inner argument.

-/

/-- Conjugating the function swaps the operators up to an outer conjugation:
`∂_v f̄ = conj (∂̄_v f)`. -/
lemma dWirtingerDir_star_comp (hf : DifferentiableAt ℝ f u) (v : V) :
    dWirtingerDir (fun p => star (f p)) v u = star (dWirtingerAntiDir f v u) := by
  simp only [dWirtingerDir, dWirtingerAntiDir]
  rw [fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, Complex.star_def, map_mul, map_add, map_div₀, map_one,
    map_ofNat, Complex.conj_I]
  ring

/-- Conjugating the function swaps the operators up to an outer conjugation:
`∂̄_v f̄ = conj (∂_v f)`. Dual of `dWirtingerDir_star_comp`. -/
lemma dWirtingerAntiDir_star_comp (hf : DifferentiableAt ℝ f u) (v : V) :
    dWirtingerAntiDir (fun p => star (f p)) v u = star (dWirtingerDir f v u) := by
  simp only [dWirtingerDir, dWirtingerAntiDir]
  rw [fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, Complex.star_def, map_mul, map_sub, map_div₀, map_one,
    map_ofNat, Complex.conj_I]
  ring

/-!

## D. The Wirtinger chain rule

Composing with an outer `g : ℂ → ℂ` gives a **two-term** chain rule:

  `∂_v(g∘f) = (∂g/∂f)·∂_v f + (∂g/∂f̄)·∂_v f̄`.

A non-holomorphic `g` depends on both its argument and its conjugate, so both channels
contribute: the holomorphic `∂g/∂f` and the anti-holomorphic `∂g/∂f̄`, each times the
matching inner derivative — two terms where the complex-analytic rule has one. The two
coefficients come from `realLinear_apply_eq_wirtinger`: every `ℝ`-linear `L : ℂ → ℂ`
splits as `L w = a·w + b·conj w`, and on the outer real derivative `L = fderiv ℝ g (f u)`
that gives `a = ∂g/∂f`, `b = ∂g/∂f̄`. The proof applies this split to the outer factor and
reuses the §C conjugation lemmas for the `∂_v f̄` term.

-/

/-- The two-term Wirtinger chain rule for `dWirtingerDir`, outer `g : ℂ → ℂ` and inner
`f : V → ℂ`:

  `∂_v(g∘f) = (∂g/∂f)·∂_v f + (∂g/∂f̄)·∂_v f̄`.

`realLinear_apply_eq_wirtinger` splits the chain rule's outer `ℝ`-linear factor into the
`∂g/∂f`, `∂g/∂f̄` coefficients, each multiplying its inner directional derivative `∂_v f`,
`∂_v f̄`. -/
lemma dWirtingerDir_comp {g : ℂ → ℂ} (hg : DifferentiableAt ℝ g (f u))
    (hf : DifferentiableAt ℝ f u) (v : V) :
    dWirtingerDir (fun p => g (f p)) v u =
      dWirtingerDir g 1 (f u) * dWirtingerDir f v u
        + dWirtingerAntiDir g 1 (f u) * dWirtingerDir (fun p => star (f p)) v u := by
  simp only [dWirtingerDir, dWirtingerAntiDir, smul_eq_mul, mul_one]
  rw [show (fun p => g (f p)) = g ∘ f from rfl, fderiv_comp u hg hf, fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply]
  have hA := realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u v)
  have hB := realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u (Complex.I • v))
  rw [hA, hB]
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, Complex.star_def]
  ring

/-- The two-term Wirtinger chain rule for `dWirtingerAntiDir`, the anti-holomorphic dual of
`dWirtingerDir_comp`:

  `∂̄_v(g∘f) = (∂g/∂f)·∂̄_v f + (∂g/∂f̄)·∂̄_v f̄`.

Same outer `∂g/∂f`, `∂g/∂f̄` coefficients, now each multiplying its anti-holomorphic inner
derivative `∂̄_v f`, `∂̄_v f̄`; same proof as `dWirtingerDir_comp`. -/
lemma dWirtingerAntiDir_comp {g : ℂ → ℂ} (hg : DifferentiableAt ℝ g (f u))
    (hf : DifferentiableAt ℝ f u) (v : V) :
    dWirtingerAntiDir (fun p => g (f p)) v u =
      dWirtingerDir g 1 (f u) * dWirtingerAntiDir f v u
        + dWirtingerAntiDir g 1 (f u) * dWirtingerAntiDir (fun p => star (f p)) v u := by
  simp only [dWirtingerDir, dWirtingerAntiDir, smul_eq_mul, mul_one]
  rw [show (fun p => g (f p)) = g ∘ f from rfl, fderiv_comp u hg hf, fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply]
  have hA := realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u v)
  have hB := realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u (Complex.I • v))
  rw [hA, hB]
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, Complex.star_def]
  ring

/-!

## E. Domain conjugation

The §C lemmas conjugate a function's *output*; this section conjugates its
*input*. Precomposing `g` with a domain map `L` — forming `g ∘ L` — relates the
directional derivatives of the composite to those of `g`.

The map `L : V → V'` is **conjugate-`ℂ`-linear**: real-linear and continuous, but
anti-commuting with multiplication by `i`,

  `L (i · x) = −(i · L x)`,

the abstract form of complex conjugation (`conj (i·x) = −i · conj x`). That sign
flip is what turns a holomorphic derivative into an anti-holomorphic one: in the holomorphic
combination `(1/2)(d_v f − i·d_{i·v} f)`, the `d_{i·v} f` term picks up the minus from
`L`, converting it into the anti-holomorphic combination. So precomposition **swaps** the
two operators and transports the base point and direction through `L`:

  `∂_v(g ∘ L)`  at `u`  =  `∂̄_{L v} g`  at `L u`

(`dWirtingerDir_comp_conjLinear`, with the dual `∂̄_v(g ∘ L) = ∂_{L v} g`).

Use it to differentiate a function whose input has been conjugated (`g ∘ L`, e.g.
`g(z̄)`). The swap rewrites that derivative as the *other* operator on the plain
`g`, exposing it for the §F collapse: for a holomorphic `g`, `g ∘ L` then has
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
    fderiv ℝ (fun p => g (L p)) u x = fderiv ℝ g (L u) (L x) := by
  rw [show (fun p => g (L p)) = g ∘ (L : V → V') from rfl,
    fderiv_comp u hg L.differentiableAt, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply]

/-- Precomposing with a conjugate-`ℂ`-linear `L` turns the holomorphic directional
derivative into the anti-holomorphic one at the transported point and direction. -/
lemma dWirtingerDir_comp_conjLinear {g : V' → ℂ} {L : V →L[ℝ] V'} {u : V}
    (hL : ∀ x : V, L (Complex.I • x) = -(Complex.I • L x))
    (hg : DifferentiableAt ℝ g (L u)) (v : V) :
    dWirtingerDir (fun p => g (L p)) v u = dWirtingerAntiDir g (L v) (L u) := by
  simp only [dWirtingerDir, dWirtingerAntiDir, fderiv_comp_clm_apply hg, hL, map_neg]; ring

/-- Dual of `dWirtingerDir_comp_conjLinear`. -/
lemma dWirtingerAntiDir_comp_conjLinear {g : V' → ℂ} {L : V →L[ℝ] V'} {u : V}
    (hL : ∀ x : V, L (Complex.I • x) = -(Complex.I • L x))
    (hg : DifferentiableAt ℝ g (L u)) (v : V) :
    dWirtingerAntiDir (fun p => g (L p)) v u = dWirtingerDir g (L v) (L u) := by
  simp only [dWirtingerDir, dWirtingerAntiDir, fderiv_comp_clm_apply hg, hL, map_neg]; ring

end DomainConjugation

/-!

## F. The holomorphic collapse

When the real Fréchet derivative is `ℂ`-linear along the chosen direction
(`d_{i·v} f = i·d_v f` — the Cauchy–Riemann content), `dWirtingerDir` returns the
full derivative and `dWirtingerAntiDir` vanishes; dually for a conjugate-linear
derivative. The hypothesis is `restrictScalars`-free, so this collapse is
domain-general and proven once here; producing the hypothesis from holomorphy is
the only step that meets the `ℝ`/`ℂ` `restrictScalars` diamond, and is done per
concrete domain by the consumers.

-/

/-- Holomorphic collapse: along a direction where the real derivative is `ℂ`-linear, the
holomorphic derivative is the full real derivative, `∂_v f = d_v f`. -/
lemma dWirtingerDir_eq_of_clinear {v : V}
    (h : fderiv ℝ f u (Complex.I • v) = Complex.I • fderiv ℝ f u v) :
    dWirtingerDir f v u = fderiv ℝ f u v := by
  simp only [dWirtingerDir, h, smul_eq_mul]; rw [← mul_assoc, Complex.I_mul_I]; ring

/-- Holomorphic collapse: the anti-holomorphic derivative vanishes along a direction
of `ℂ`-linearity, `∂̄_v f = 0`. -/
lemma dWirtingerAntiDir_eq_zero_of_clinear {v : V}
    (h : fderiv ℝ f u (Complex.I • v) = Complex.I • fderiv ℝ f u v) :
    dWirtingerAntiDir f v u = 0 := by
  simp only [dWirtingerAntiDir, h, smul_eq_mul]; rw [← mul_assoc, Complex.I_mul_I]; ring

/-- Anti-holomorphic collapse: a direction of conjugate-`ℂ`-linearity kills the
holomorphic derivative, `∂_v f = 0`. -/
lemma dWirtingerDir_eq_zero_of_antilinear {v : V}
    (h : fderiv ℝ f u (Complex.I • v) = -(Complex.I • fderiv ℝ f u v)) :
    dWirtingerDir f v u = 0 := by
  simp only [dWirtingerDir, h, smul_eq_mul, mul_neg]; rw [← mul_assoc, Complex.I_mul_I]; ring

/-- Anti-holomorphic collapse: the anti-holomorphic derivative is the full real
derivative along a direction of conjugate-`ℂ`-linearity, `∂̄_v f = d_v f`. -/
lemma dWirtingerAntiDir_eq_of_antilinear {v : V}
    (h : fderiv ℝ f u (Complex.I • v) = -(Complex.I • fderiv ℝ f u v)) :
    dWirtingerAntiDir f v u = fderiv ℝ f u v := by
  simp only [dWirtingerAntiDir, h, smul_eq_mul, mul_neg]; rw [← mul_assoc, Complex.I_mul_I]; ring

/-!

## G. The second-derivative bridge

Each directional operator is, definitionally, the combination
`(1/2)(d_v f + c·d_{i·v} f)` of the real Fréchet derivative along a
direction `v` and its `i`-rotation `i·v` (`c = −i` holomorphic, `c = +i`
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
each reduces to the same `fderiv ℝ (fderiv ℝ f) u` on the four directions `v`,
`i·v`, `w`, `i·w`. §I discharges the mixed pairing (the one Kähler geometry
needs); the other three would follow from this bridge with no new plumbing — a
different choice of `(c, b₁, b₂)`, then `ContDiffAt.isSymmSndFDerivAt` and
`ring`.

-/

/-- The combination `p ↦ (1/2)(d_{b₁} f + c·d_{b₂} f)` of the real Fréchet
derivative of `f` along two directions. `dWirtingerDir f v` is this with
`c = -i`, `b₁ = v`, `b₂ = i·v`; `dWirtingerAntiDir f v` with `c = i`. -/
private def weightedDirDeriv (f : V → ℂ) (c : ℂ) (b₁ b₂ : V) : V → ℂ :=
  fun p => (1 / 2 : ℂ) * (fderiv ℝ f p b₁ + c * fderiv ℝ f p b₂)

omit [NormedSpace ℂ V] in
/-- `f` is `C¹` in its first derivative, so `fderiv ℝ f` is differentiable at
`u` — the regularity that makes a `weightedDirDeriv` (hence a directional derivative)
differentiable. -/
private lemma differentiableAt_fderiv (hf2 : ContDiffAt ℝ 2 f u) :
    DifferentiableAt ℝ (fderiv ℝ f) u :=
  (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

omit [NormedSpace ℂ V] in
/-- The field `p ↦ d_b f` is the evaluation map `· b` composed with `fderiv ℝ f`,
so when `fderiv ℝ f` is differentiable its derivative is `fderiv ℝ (fderiv ℝ f) u`
post-composed with that evaluation. -/
private lemma hasFDerivAt_fderiv_apply (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (b : V) :
    HasFDerivAt (fun p => fderiv ℝ f p b)
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
private lemma dWirtingerAntiDir_eq_weightedDirDeriv (w : V) :
    (fun p => dWirtingerAntiDir f w p) = weightedDirDeriv f Complex.I w (Complex.I • w) :=
  rfl

/-- A directional derivative is a `weightedDirDeriv`: holomorphic with `c = -i`. -/
private lemma dWirtingerDir_eq_weightedDirDeriv (v : V) :
    (fun p => dWirtingerDir f v p) = weightedDirDeriv f (-Complex.I) v (Complex.I • v) := by
  funext p; simp only [dWirtingerDir, weightedDirDeriv]; ring

/-- Differentiating the anti-holomorphic directional derivative lands on the second
real Fréchet derivative in the two slots. -/
private lemma fderiv_dWirtingerAntiDir (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (w a : V) :
    fderiv ℝ (fun p => dWirtingerAntiDir f w p) u a
      = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) u a w
          + Complex.I * fderiv ℝ (fderiv ℝ f) u a (Complex.I • w)) := by
  rw [dWirtingerAntiDir_eq_weightedDirDeriv, fderiv_weightedDirDeriv hf']

/-- Differentiating the holomorphic directional derivative lands on the second real
Fréchet derivative in the two slots. -/
private lemma fderiv_dWirtingerDir (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (v a : V) :
    fderiv ℝ (fun p => dWirtingerDir f v p) u a
      = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) u a v
          - Complex.I * fderiv ℝ (fderiv ℝ f) u a (Complex.I • v)) := by
  rw [dWirtingerDir_eq_weightedDirDeriv, fderiv_weightedDirDeriv hf']; ring

/-!

## H. Differentiability and locality

Two regularity facts about the operators viewed as fields in the base point.
**Differentiability**: on a `C²` field the directional derivative `p ↦ ∂_v f`
is itself real-differentiable (`differentiableAt_dWirtingerDir`) — by §G it is a
`weightedDirDeriv`, and `fderiv ℝ f` is differentiable for a `C²` `f`. This is the
regularity §I needs to differentiate a Wirtinger derivative a second time.
**Locality**: each operator depends only on `f` near `u`, inherited from
`fderiv ℝ` — fields agreeing on a neighbourhood of `u` have equal directional
derivative there (`dWirtingerDir_congr_of_eventuallyEq`).

-/

/-- On a `C²` field the holomorphic directional derivative is itself
real-differentiable. -/
lemma differentiableAt_dWirtingerDir (hf2 : ContDiffAt ℝ 2 f u) (v : V) :
    DifferentiableAt ℝ (fun p => dWirtingerDir f v p) u := by
  rw [dWirtingerDir_eq_weightedDirDeriv]
  exact (hasFDerivAt_weightedDirDeriv (differentiableAt_fderiv hf2) _ _ _).differentiableAt

/-- On a `C²` field the anti-holomorphic directional derivative is itself
real-differentiable. -/
lemma differentiableAt_dWirtingerAntiDir (hf2 : ContDiffAt ℝ 2 f u) (w : V) :
    DifferentiableAt ℝ (fun p => dWirtingerAntiDir f w p) u := by
  rw [dWirtingerAntiDir_eq_weightedDirDeriv]
  exact (hasFDerivAt_weightedDirDeriv (differentiableAt_fderiv hf2) _ _ _).differentiableAt

/-- The holomorphic directional derivative depends only on the field near the point:
fields agreeing on a neighbourhood have equal derivative. -/
lemma dWirtingerDir_congr_of_eventuallyEq {f₁ f₂ : V → ℂ} {u : V}
    (h : f₁ =ᶠ[nhds u] f₂) (v : V) :
    dWirtingerDir f₁ v u = dWirtingerDir f₂ v u := by
  simp only [dWirtingerDir, h.fderiv_eq]

/-- The anti-holomorphic directional derivative depends only on the field near the
point; dual of `dWirtingerDir_congr_of_eventuallyEq`. -/
lemma dWirtingerAntiDir_congr_of_eventuallyEq {f₁ f₂ : V → ℂ} {u : V}
    (h : f₁ =ᶠ[nhds u] f₂) (v : V) :
    dWirtingerAntiDir f₁ v u = dWirtingerAntiDir f₂ v u := by
  simp only [dWirtingerAntiDir, h.fderiv_eq]

/-!

## I. Schwarz's theorem

-/

/-- **Schwarz's theorem** for the directional Wirtinger operators: on a `C²`
field the holomorphic and anti-holomorphic directional derivatives in any two directions
commute, `∂_v ∂̄_w f = ∂̄_w ∂_v f`.

Both orders expand, through the bridge, into a real-linear combination of
the second real Fréchet derivative `fderiv ℝ (fderiv ℝ f) u` on the four
directions `v`, `i·v`, `w`, `i·w`; the two orders differ only by transposing the
two slots of that second derivative, which `ContDiffAt.isSymmSndFDerivAt`
equates. -/
theorem dWirtingerDir_dWirtingerAntiDir_comm (hf2 : ContDiffAt ℝ 2 f u) (v w : V) :
    dWirtingerDir (fun p => dWirtingerAntiDir f w p) v u
      = dWirtingerAntiDir (fun p => dWirtingerDir f v p) w u := by
  have hf' := differentiableAt_fderiv hf2
  have hsymm : IsSymmSndFDerivAt ℝ f u := hf2.isSymmSndFDerivAt (by simp)
  rw [dWirtingerDir_apply (fun p => dWirtingerAntiDir f w p) v u,
    dWirtingerAntiDir_apply (fun p => dWirtingerDir f v p) w u,
    fderiv_dWirtingerAntiDir hf', fderiv_dWirtingerAntiDir hf',
    fderiv_dWirtingerDir hf', fderiv_dWirtingerDir hf',
    hsymm.eq w v, hsymm.eq w (Complex.I • v),
    hsymm.eq (Complex.I • w) v, hsymm.eq (Complex.I • w) (Complex.I • v)]
  ring

end Physlib.Wirtinger

end

end
