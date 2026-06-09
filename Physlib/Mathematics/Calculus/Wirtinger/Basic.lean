/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic

/-!

# Wirtinger calculus

## Notation

* The differentiation direction is a *subscript*: `∂_v f` and `∂̄_v f` are the holomorphic and
  anti-holomorphic Wirtinger derivatives of `f` in direction `v`, splitting the total real
  derivative `d_v f` (straight `d` for the total, `∂`/`∂̄` for the parts).
* A `/∂` fraction differentiates with respect to a *variable*, not a direction: a real
  coordinate `∂f/∂x`, or the argument of a one-variable function in the chain rule, `∂g/∂f`,
  `∂g/∂f̄` (outer `g : ℂ → ℂ`, inner `f : V → ℂ`).
* `f̄` is the pointwise conjugate `p ↦ conj (f p)`.

## i. Overview

The **Wirtinger calculus** differentiates complex functions `f` that need not
be holomorphic, treating a variable and its conjugate as independent and
replacing the complex derivative with a pair:

- `∂_v f`  (`dWirtingerDir`), the holomorphic part along `v`;
- `∂̄_v f` (`dWirtingerAntiDir`), the anti-holomorphic part along `v`,

obtained by splitting the real derivative of `f` along `v` into its
`ℂ`-linear and conjugate-linear parts. The split detects holomorphy:
`∂̄_v f = 0` ⟺ Cauchy–Riemann holds along `v`, and then `∂_v f` is the ordinary
complex derivative. The guiding example is a Kähler potential `K(φ, φ̄)`:
real, non-holomorphic, no complex derivative, yet `∂K/∂φ` and `∂K/∂φ̄` are
exactly what physics uses.

The folder has three layers:

- `Wirtinger.Basic` (this file), two algebraic lemmas feeding the calculus:
  `realLinear_apply_eq_wirtinger` (the real-linear Wirtinger split) and
  `fderiv_star_eq` (differentiation commutes with conjugation). Mathlib has
  `fderiv ℂ` and `fderiv ℝ` but no Wirtinger pair, which is built on `fderiv ℝ`.
- `Wirtinger.Multivariable`, the foundation: directional operators
  `∂_v`, `∂̄_v` on `f : V → ℂ` for arbitrary `v : V`, with linearity,
  Leibniz, chain rule, conjugations, holomorphic collapse, and **Schwarz's
  theorem** `∂_v ∂̄_w f = ∂̄_w ∂_v f` (reduced to Mathlib's
  `ContDiffAt.isSymmSndFDerivAt`). The directional form is forced by
  Schwarz, which relates two *distinct* directions.
- `Wirtinger.Coordinate`, the coordinate specialization to `V = ℂⁿ`
  (spelled `ι → ℂ`, `n = |ι|`) along `v = Pi.single I 1`. Packages
  `dWirtingerCoord`, `dWirtingerAntiCoord`, the projection/conjugation CLMs
  (`coordProjCLM`, `conjCoordCLM`, `conjCLM`), the Pi-domain
  `restrictScalars` bridge, and the coordinate forms of every result from
  `Multivariable`, including Schwarz `∂_I ∂_J̄ f = ∂_J̄ ∂_I f`.

The anti-holomorphic variable is written with `star`, matching Mathlib's
`StarRing ℂ`.

## ii. Key results

- `Physlib.Wirtinger.realLinear_apply_eq_wirtinger` : the real-linear Wirtinger
    decomposition `L w = a * w + b * star w` of any `L : ℂ →L[ℝ] ℂ`, the
    key algebraic identity behind the Wirtinger chain rule.
- `Physlib.Wirtinger.fderiv_star_eq` : the real derivative of a pointwise
    conjugate `p ↦ star (f p)` is `conjCLE` composed with `fderiv ℝ f`.

-/

@[expose] public section

noncomputable section

namespace Physlib.Wirtinger

/-!

## A. The real-linear Wirtinger decomposition

Any real-linear map `ℂ →L[ℝ] ℂ` splits into a holomorphic and an
anti-holomorphic part, with the Wirtinger coefficients as weights. Together
with the derivative of a pointwise conjugate (`fderiv_star_eq`), this is the
algebraic input to the chain rules. Both sit here, *below* the foundation, so
the multivariable calculus can consume them directly.

-/

/-- Split a real-linear map `ℂ → ℂ` into its Wirtinger components. Any
real-linear `L : ℂ →L[ℝ] ℂ` splits into a holomorphic and an anti-holomorphic part
with the Wirtinger coefficients `a = ½(L 1 - i * L i)`, `b = ½(L 1 + i * L i)` as
weights:

  `L w = a * w + b * star w`.

This is purely algebraic: `L` is an arbitrary real-linear map, no derivative
involved. Its use is the Wirtinger chain rule (`dWirtingerDir_comp`, §D in
`Multivariable`), where the weights of the outer differential `L = fderiv ℝ g (f u)`
are the coefficients `∂g/∂f`, `∂g/∂f̄`. -/
lemma realLinear_apply_eq_wirtinger (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w =
      ((1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I)) * w
        + ((1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)) * star w := by
  calc
    L w = L ((w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I) := by
              congr 1; apply Complex.ext <;> simp
    _ = (w.re : ℝ) • L 1 + (w.im : ℝ) • L Complex.I := by
          rw [map_add, map_smul, map_smul]
    _ = ((1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I)) * w
          + ((1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)) * star w := by
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.I_re, Complex.I_im] <;>
        ring

/-- Differentiation commutes with conjugation: the real Fréchet derivative of the
pointwise conjugate `p ↦ star (f p)` is `conjCLE` (conjugation on `ℂ`) composed with
`fderiv ℝ f u`; in physicists' notation, `d f̄ = conj(d f)`. Conjugation is `ℝ`-linear,
so it slides through the real derivative unchanged, whereas it does *not* commute with
the holomorphic Wirtinger derivative `∂_v`. The `star` conjugates the *output* `f p`,
so this is not a derivative in a conjugate variable.

This is the analytic core of the downstream conjugation lemmas
(`dWirtingerDir_star_comp` and variants in `Multivariable`): distributed over the
Wirtinger split of `fderiv ℝ f u` (`realLinear_apply_eq_wirtinger`), the outer `conjCLE`
conjugates the two coefficients and swaps the holomorphic and anti-holomorphic parts. -/
lemma fderiv_star_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {u : E} (hf : DifferentiableAt ℝ f u) :
    fderiv ℝ (fun p : E => star (f p)) u =
      Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f u) := by
  rw [show (fun p : E => star (f p)) = Complex.conjCLE.toContinuousLinearMap ∘ f from rfl,
    fderiv_comp u Complex.conjCLE.toContinuousLinearMap.differentiableAt hf,
    ContinuousLinearMap.fderiv]

end Physlib.Wirtinger

end

end
