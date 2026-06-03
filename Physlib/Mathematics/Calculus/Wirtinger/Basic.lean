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

## i. Overview

The **Wirtinger calculus** differentiates complex functions `f` that need not
be holomorphic, by treating `z` and `z̄` as independent and replacing the
complex derivative with a pair:

- `∂f/∂d`  (`dWirtingerDir`) — holomorphic part along `d`;
- `∂f/∂d̄` (`dWirtingerAntiDir`) — anti-holomorphic part along `d`,

obtained by splitting the real derivative of `f` along `d` into its
`ℂ`-linear and conjugate-linear parts. The split detects holomorphy:
`∂f/∂d̄ = 0` ⟺ Cauchy–Riemann holds at `d`, and then `∂f/∂d` is the ordinary
complex derivative. The guiding example is a Kähler potential `K(φ, φ̄)`:
real, non-holomorphic, no complex derivative — but `∂K/∂φ` and `∂K/∂φ̄` are
exactly what physics uses.

The folder has three layers:

- `Wirtinger.Basic` (this file) — two algebraic lemmas feeding the calculus:
  `realLinear_apply_eq_wirtinger` (the real-linear Wirtinger split) and
  `fderiv_star_eq` (differentiation commutes with conjugation). Mathlib has
  `fderiv ℂ` and `fderiv ℝ` but no Wirtinger pair, which is built on `fderiv ℝ`.
- `Wirtinger.Multivariable` — the foundation: directional operators
  `∂/∂d`, `∂/∂d̄` on `f : V → ℂ` for arbitrary `d : V`, with linearity,
  Leibniz, chain rule, conjugations, holomorphic collapse, and **Schwarz's
  theorem** `∂_d ∂_ē f = ∂_ē ∂_d f` (reduced to Mathlib's
  `ContDiffAt.isSymmSndFDerivAt`). The directional form is forced by
  Schwarz, which relates two *distinct* directions.
- `Wirtinger.Coordinate` — the coordinate specialization to `V = ℂ^n`
  (spelled `ι → ℂ`, `n = |ι|`) along `d = Pi.single I 1`. Packages
  `dWirtingerCoord`, `dWirtingerAntiCoord`, the projection/conjugation CLMs
  (`coordProjCLM`, `conjCoordCLM`, `conjCLM`), the Pi-domain
  `restrictScalars` bridge, and the coordinate forms of every result from
  `Multivariable` — including Schwarz `∂_I ∂_J̄ f = ∂_J̄ ∂_I f`.

The anti-holomorphic variable is written with `star`, matching Mathlib's
`StarRing ℂ`.

## ii. Key results

- `Physlib.Wirtinger.realLinear_apply_eq_wirtinger` : the real-linear Wirtinger
    decomposition `L w = a * w + b * star w` of any `L : ℂ →L[ℝ] ℂ`, the
    key algebraic identity behind the Wirtinger chain rule.
- `Physlib.Wirtinger.fderiv_star_eq` : the real derivative of a pointwise
    conjugate `v ↦ star (f v)` is `conjCLE` composed with `fderiv ℝ f`.

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

/-- Reconstruct a real-linear map `ℂ → ℂ` from its Wirtinger components. Any
real-linear `L : ℂ →L[ℝ] ℂ` splits into a holomorphic and an anti-holomorphic part
with the Wirtinger coefficients `a = ½(L 1 - i * L i)`, `b = ½(L 1 + i * L i)` as
weights:

  `L w = a * w + b * star w`.

This is purely algebraic: `L` is an arbitrary real-linear map, no derivative
involved. Its use is the Wirtinger chain rule.

For instance, differentiate a composite `g(f(v))` — a configuration `v ∈ ℂⁿ`, a
complex inner field `f(v) ∈ ℂ`, and an outer `g : ℂ → ℂ` (though `f` may have any
complex vector space domain). The outer real differential `L = fderiv ℝ g (f u)` is
such a real-linear map, with Wirtinger coefficients the derivatives `a = ∂g/∂f`,
`b = ∂g/∂f̄`; in Leibniz form `dg = (∂g/∂f) df + (∂g/∂f̄) df̄`, collapsing to
`dg = g' df` for holomorphic `g`. A non-holomorphic `g` depends on its argument and
its conjugate independently, so the inner field enters through both slots — `f`
through `∂/∂f`, `f̄` through `∂/∂f̄` — each contributing a term to the derivative. With
`a = dWirtingerDir g 1 (f u)`, `b = dWirtingerAntiDir g 1 (f u)`, the split becomes
the two-term chain rule `dWirtingerDir_comp`:

  `∂(g∘f)/∂d = (∂g/∂f)·(∂f/∂d) + (∂g/∂f̄)·(∂f̄/∂d)`. -/
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
pointwise conjugate `v ↦ star (f v)` is `conjCLE` (conjugation on `ℂ`) composed
with `fderiv ℝ f u`. In physicists' notation, writing `f̄ = star ∘ f`, this is
`∂(f̄) = conj(∂f)`, where `∂` differentiates along a *real* direction: the variable
is real, only the output `f v` is complex. Realness is the point — conjugation is
`ℝ`-linear, so it slides through a real derivative unchanged, whereas it does *not*
commute with a complex `∂/∂z` (where `z̄` is the canonical non-holomorphic example).
The `star` conjugates the *output* `f v`, so this is also not a derivative with
respect to a conjugate variable.

This is the analytic core of the downstream conjugation lemmas, where conjugating
the inner field swaps the holomorphic and anti-holomorphic operators
(`dWirtingerDir_star_comp` and variants in `Multivariable`): the single outer
`conjCLE`, distributed over the Wirtinger split of `fderiv ℝ f u`
(`realLinear_apply_eq_wirtinger`), conjugates the two coefficients and exchanges
the holomorphic and anti-holomorphic parts. -/
lemma fderiv_star_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {u : E} (hf : DifferentiableAt ℝ f u) :
    fderiv ℝ (fun v : E => star (f v)) u =
      Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f u) := by
  rw [show (fun v : E => star (f v)) = Complex.conjCLE.toContinuousLinearMap ∘ f from rfl,
    fderiv_comp u Complex.conjCLE.toContinuousLinearMap.differentiableAt hf,
    ContinuousLinearMap.fderiv]

end Physlib.Wirtinger

end

end
