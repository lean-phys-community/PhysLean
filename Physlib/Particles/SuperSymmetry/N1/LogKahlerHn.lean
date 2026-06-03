/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Particles.SuperSymmetry.N1.KahlerMetric
public import Physlib.Mathematics.Calculus.Wirtinger.UpperHalfPlane
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!

# SUSY N=1 — the multi-field log Kähler potential on `H^n`

## i. Overview

The multi-field upper-half-plane log Kähler potential

  `K(u) = -∑_I log(2 Im u^I)`

on the chiral scalars indexed by `C`, as the concrete
`KahlerPotential C` instance of the
abstract machinery in `Particles/SuperSymmetry/N1/KahlerPotential.lean` and
`Particles/SuperSymmetry/N1/KahlerMetric.lean`. The moduli space `H^n` sits inside
`ChiralScalarConfiguration C` through the slit-set of
`Mathematics/Calculus/Wirtinger/UpperHalfPlane.lean`
(the open set on which every `imArgCLM I` lies in `Complex.slitPlane`); on
it `2 Im u^I > 0`, so each `log` is real and the leading minus sign yields
a positive-definite Kähler metric.

`K` is genuinely real, so it lives in the `ℝ`-codomain `KahlerPotential`;
the Wirtinger operators act on its ℂ-lift `K.lift`. In chiral coordinates
the equivalent complex form `K = -∑_I log(i (φ̄^I − φ^I))` is the one in
which the closed forms proved here — `∂K/∂φ^J = -1/(φ^J − φ̄^J)`,
`∂K/∂φ̄^J = 1/(φ^J − φ̄^J)`, and the diagonal Poincaré metric
`g_{IJ̄} = -δ_{IJ}/(φ^I − φ̄^I)²` — fall out cleanly. Hermiticity is not
re-proven: it is the `K`-instance of the abstract
`KahlerPotential.metric_hermitian`.

## ii. Key results

- `SUSY.N1.K` : the multi-field log Kähler potential, as a `KahlerPotential C`.
- `SUSY.N1.dChiralScalar_K`, `SUSY.N1.dAntiChiralScalar_K` :
    closed-form chiral / anti-chiral derivatives of `K.lift`.
- `SUSY.N1.kahlerMetric` : the Kähler metric `g_{IJ̄}(u) = ∂²K / (∂φ^I ∂φ̄^J)`,
    defined as the abstract `K.metric`.
- `SUSY.N1.kahlerMetric_apply` : closed-form diagonal Poincaré
    metric `g_{IJ̄}(u) = -δ_{IJ} / (z^I − z̄^I)²`, i.e. the Poincaré metric
    `δ_{IJ} / (2 Im z^I)²` (positive-definite on `H^n`, though positivity is
    not formalised here).
- `SUSY.N1.kahlerMetric_hermitian` : hermiticity `star (g_{IJ̄}) = g_{JĪ}`,
    the concrete instance of `KahlerPotential.metric_hermitian`.

## iii. Table of contents

- A. The log Kähler potential as a `KahlerPotential`
- B. The chain rule for `log ∘ imArgCLM`
- C. Closed-form Wirtinger derivatives of `K`
- D. The Kähler metric and its hermiticity

-/

@[expose] public section

noncomputable section

namespace SUSY.N1

open Physlib.Wirtinger

variable {C : Type*} [Fintype C] [DecidableEq C]

/-!

## A. The log Kähler potential as a `KahlerPotential`

The `H^n` log potential `-∑_I log(2 Im u^I)` is a genuine real observable, so it
is packaged as a `KahlerPotential C` on the open slit-set of
`Mathematics/Calculus/Wirtinger/UpperHalfPlane.lean`. Its ℂ-lift `K.lift` is what the Wirtinger
operators consume; on the domain it equals the complex form
`-∑_I log(imArgCLM I ·)` (via `Complex.ofReal_log` on the positive reals),
the bridge `K_lift_eq` through which §C evaluates the derivatives.

-/

/-- The multi-field upper-half-plane log Kähler potential as a `KahlerPotential`:
the real observable `K(u) = -∑_I log(2 Im u^I)`, regular on the open slit-set
realising `H^n` as moduli space. Reality is by construction from the `ℝ`
codomain; the Wirtinger operators consume the ℂ-lift `K.lift`. -/
def K : KahlerPotential C where
  toFun := fun u => -∑ I, Real.log (2 * (u I).im)
  domain := {v | ∀ I, imArgCLM I v ∈ Complex.slitPlane}
  domain_open := isOpen_slitSet
  contDiffOn := by
    have hsmooth : ∀ I : C,
        ContDiff ℝ 2 (fun v : ChiralScalarConfiguration C => 2 * (v I).im) :=
      fun I => contDiff_const.mul ((Complex.imCLM.comp (coordProjCLM I)).contDiff)
    intro u hu
    have hne : ∀ I : C, (2 * (u I).im : ℝ) ≠ 0 := fun I => by
      have := im_pos_of_mem_slitPlane (hu I)
      have hpos : (0 : ℝ) < 2 * (u I).im := by linarith
      exact hpos.ne'
    exact (ContDiffAt.sum fun I _ => (hsmooth I).contDiffAt.log (hne I)).neg.contDiffWithinAt

omit [DecidableEq C] in
/-- On the slit domain the ℂ-lift of `K` is the familiar complex log form
`-∑_I log(imArgCLM I u)`: the inner argument `imArgCLM I u = ↑(2 Im u^I)` is a
positive real, so `Complex.log ↑r = ↑(Real.log r)` (`Complex.ofReal_log`). -/
private lemma K_lift_eq {u : ChiralScalarConfiguration C}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) :
    (K : KahlerPotential C).lift u = -∑ I, Complex.log (imArgCLM I u) := by
  have hcast : (K : KahlerPotential C).lift u
      = ((-∑ I, Real.log (2 * (u I).im) : ℝ) : ℂ) := rfl
  rw [hcast]
  push_cast
  refine congrArg Neg.neg (Finset.sum_congr rfl fun I _ => ?_)
  have hpos : (0 : ℝ) < 2 * (u I).im := by linarith [im_pos_of_mem_slitPlane (h I)]
  rw [Complex.ofReal_log hpos.le, ← imArgCLM_eq_ofReal]

omit [DecidableEq C] in
/-- Near any slit-domain point the ℂ-lift of `K` agrees with the complex log
form, so the Wirtinger derivatives may be taken on the latter inside the
calculus. -/
private lemma K_lift_eventuallyEq {u : ChiralScalarConfiguration C}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) :
    (K : KahlerPotential C).lift =ᶠ[nhds u]
      (fun v => -∑ I, Complex.log (imArgCLM I v)) := by
  filter_upwards [isOpen_slitSet.mem_nhds h] with v hv
  exact K_lift_eq hv

/-!

## C. Closed-form Wirtinger derivatives of `K`

Applying the holomorphic-outer chain rule to each summand of the complex log
form (which the lift equals near a domain point, `K_lift_eq`) yields the
closed-form expressions `∂K/∂φ^J = -1/(z^J − z̄^J)` and
`∂K/∂φ̄^J = 1/(z^J − z̄^J)`.

-/

/-- The conjugation model for the single-type `Hⁿ` example: chiral and anti-chiral
indices coincide, so `equiv` is the identity. -/
def model : Model C C := ⟨Equiv.refl _⟩

/-- Closed form of the chiral derivative `∂_J K = -1 / (z^J - z̄^J)` of the
multi-field upper-half-plane log Kähler potential. Near `u` the lift equals
`-∑_I log(imArgCLM I ·)`; `∂_J` passes the negation, the sum collapses to its
diagonal term, and the slit-plane non-vanishing facts close the algebra. -/
theorem dChiralScalar_K {u : ChiralScalarConfiguration C}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) (J : C) :
    model.dChiralScalar (K : KahlerPotential C).lift J u = -(1 / (u J - conjConfig u J)) := by
  show dWirtingerCoord (K : KahlerPotential C).lift J u = -(1 / (u J - conjConfig u J))
  have _ : u J - star (u J) ≠ 0 := sub_star_ne_zero (h J)
  have _ : star (u J) - u J ≠ 0 := star_sub_ne_zero (h J)
  rw [dWirtingerCoord_congr_of_eventuallyEq_apply (K_lift_eventuallyEq h) J,
    dWirtingerCoord_neg_apply,
    dWirtingerCoord_sum_log_comp_imArgCLM h J, imArgCLM_apply]
  simp only [conjConfig_apply]
  field_simp
  ring

/-- Closed form of the anti-chiral derivative `∂_J̄ K = 1 / (z^J - z̄^J)` of the
multi-field upper-half-plane log Kähler potential (barred index via the identity
`model`). Mirror of `dChiralScalar_K`. -/
theorem dAntiChiralScalar_K {u : ChiralScalarConfiguration C}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) (J : C) :
    model.dAntiChiralScalar (K : KahlerPotential C).lift J u =
      1 / (u J - conjConfig u J) := by
  simp only [Model.dAntiChiralScalar, model, Equiv.refl_symm, Equiv.coe_refl, id_eq]
  have _ : u J - star (u J) ≠ 0 := sub_star_ne_zero (h J)
  have _ : star (u J) - u J ≠ 0 := star_sub_ne_zero (h J)
  rw [dWirtingerAntiCoord_congr_of_eventuallyEq_apply (K_lift_eventuallyEq h) J,
    dWirtingerAntiCoord_neg_apply,
    dWirtingerAntiCoord_sum_log_comp_imArgCLM h J, imArgCLM_apply]
  simp only [conjConfig_apply]
  field_simp
  ring

/-!

## D. The Kähler metric and its hermiticity

The mixed second Wirtinger derivative `g_{IJ̄}(u) = ∂²K/(∂φ^I ∂φ̄^J)`
is the Kähler metric, here the abstract `K.metric` of the `KahlerPotential`
`K`. Its closed form on `H^n` is the diagonal Poincaré-metric
`-δ_{IJ} / (z^I − z̄^I)²`, the positive-definite metric
`δ_{IJ} / (2 Im z^I)²`. Hermiticity is the `K`-instance of
`KahlerPotential.metric_hermitian`.

-/

/-- On a neighbourhood of any point where the slit-plane hypothesis holds,
`dWirtingerAntiCoord K.lift J` agrees with its closed form `(φ^J − φ̄^J)⁻¹`. Feeds
`dWirtingerCoord_congr_of_eventuallyEq_apply` in `kahlerMetric_apply`, letting the second
Wirtinger derivative be taken on the closed form inside the calculus. -/
private lemma dWirtingerAntiCoord_K_eventuallyEq {u : ChiralScalarConfiguration C}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) (J : C) :
    (fun v : ChiralScalarConfiguration C =>
        dWirtingerAntiCoord (K : KahlerPotential C).lift J v) =ᶠ[nhds u]
      (fun v => (v J - conjConfig v J)⁻¹) := by
  filter_upwards [isOpen_slitSet.mem_nhds h] with v hv
  rw [show dWirtingerAntiCoord (K : KahlerPotential C).lift J v
        = model.dAntiChiralScalar (K : KahlerPotential C).lift J v from rfl,
    dAntiChiralScalar_K hv J, one_div]

/-- The Kähler metric `g_{IJ̄}(u) = ∂²K / (∂φ^I ∂φ̄^J)` of the multi-field
upper-half-plane log Kähler potential — the abstract `K.metric` at the identity
`model`. -/
def kahlerMetric (I J : C) (u : ChiralScalarConfiguration C) : ℂ :=
  (K : KahlerPotential C).metric model I J u

/-- Closed form of the Kähler metric on `H^n`: diagonal Poincaré-metric on
each factor, `g_{IJ̄}(u) = -δ_{IJ} / (z^I − z̄^I)²`. Since `z^I − z̄^I = 2i Im z^I`,
this is the Poincaré metric `δ_{IJ} / (2 Im z^I)²`, positive-definite on `H^n`
(positivity is not formalised here). -/
theorem kahlerMetric_apply {u : ChiralScalarConfiguration C}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) (I J : C) :
    kahlerMetric I J u =
      if I = J then -(1 / (u I - conjConfig u I) ^ 2) else 0 := by
  have hw : u J - conjConfig u J ≠ 0 := by
    have := sub_star_ne_zero (h J)
    rwa [conjConfig_apply]
  have hcomp : dWirtingerCoord (fun v : ChiralScalarConfiguration C =>
        (v J - conjConfig v J)⁻¹) I u
      = deriv (fun w : ℂ => w⁻¹) (u J - conjConfig u J)
        * dWirtingerCoord (fun v : ChiralScalarConfiguration C =>
            v J - conjConfig v J) I u :=
    dWirtingerCoord_comp_holomorphic_apply (differentiableAt_inv hw)
      (differentiable_coordDiff J u) I
  simp only [kahlerMetric, KahlerPotential.metric, Model.dChiralScalar, Model.dAntiChiralScalar,
    model, Equiv.refl_symm, Equiv.coe_refl, id_eq]
  rw [dWirtingerCoord_congr_of_eventuallyEq_apply (dWirtingerAntiCoord_K_eventuallyEq h J) I, hcomp,
    (hasDerivAt_inv hw).deriv, dWirtingerCoord_coordDiff]
  by_cases hIJ : I = J
  · subst hIJ; simp
  · simp [hIJ]

/-- **Hermiticity** of the `H^n` Kähler metric: `star (g_{IJ̄}) = g_{JĪ}` on the
slit domain. Not re-proven here — it is the `K`-instance of the abstract
`KahlerPotential.metric_hermitian`, whose proof is reality of `K` (free from the
`ℝ` codomain) plus Schwarz's theorem. -/
theorem kahlerMetric_hermitian {u : ChiralScalarConfiguration C}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) (I J : C) :
    star (kahlerMetric I J u) = kahlerMetric J I u := by
  have h2 := (K : KahlerPotential C).metric_hermitian model h I J
  simpa only [kahlerMetric, model, Equiv.refl_symm, Equiv.coe_refl, id_eq] using h2

end SUSY.N1

end

end
