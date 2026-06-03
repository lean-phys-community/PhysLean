/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Calculus.Wirtinger.Multivariable
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Data.Fintype.Defs

/-!

# Wirtinger calculus in a complex coordinate basis

## i. Overview

This module is the **coordinate specialization** of `Wirtinger.Multivariable` to
`V = ℂ^n` (spelled `ι → ℂ`, `n = |ι|` for a `Fintype` index `ι`), with the
direction `d` fixed to the I-th standard basis vector `Pi.single I 1`:

  `∂f/∂z^I  := ∂f/∂d`   along `d = Pi.single I 1`   (`dWirtingerCoord`)
  `∂f/∂z̄^I := ∂f/∂d̄`  along `d = Pi.single I 1`   (`dWirtingerAntiCoord`)

These are the partial Wirtinger derivatives w.r.t. coordinate `I` with the
others fixed — the form physics uses, and the form the N=1 SUSY layer consumes
downstream (with `ι` its chiral index type). The `I = J` Kronecker behaviour
`∂z^J/∂z^I = δ_IJ`, `∂z̄^J/∂z̄^I = δ_IJ`, `∂z^J/∂z̄^I = ∂z̄^J/∂z^I = 0`
holds.

The file packages:

- the **coordinate operators** `dWirtingerCoord`, `dWirtingerAntiCoord` and
  their real-Fréchet unfolding (§A);
- the **projection / conjugation CLMs** `coordProjCLM`, `conjCoordCLM`,
  `conjCLM`, with `conjCLM` conjugate-`ℂ`-linear (`conjCLM_smul_I`);
- the **`ℝ`/`ℂ` `restrictScalars` bridges**: `hasFDerivAt_restrictScalarsℝℂ` for a
  holomorphic outer `g : ℂ → ℂ`, and the Pi-domain bridge (§B) for the `(ι → ℂ)`
  domain — both pay the codomain `IsScalarTower ℝ ℂ ℂ` diamond once, the latter
  packaged so its projections keep `restrictScalars` out of every lemma type;
- the **coordinate forms** of every result from `Multivariable`:
  pointwise additivity, scalar compatibility, the Leibniz product rule,
  finite-sum rule,
  conjugation lemmas, the holomorphic / anti-holomorphic collapse, the
  outer-function chain rules, and coordinate-difference helpers for
  `z^J − z̄^J` (§C–E);
- **Schwarz's theorem** for the coordinate operators (§F):

      `∂_I ∂_J̄ f = ∂_J̄ ∂_I f`     (`dWirtingerCoord_dWirtingerAntiCoord_comm`)

  the keystone of Kähler-metric hermiticity: with `K` real,
  `g_{IJ̄} = ∂_I ∂_J̄ K` and `star (g_{JĪ}) = ∂_J̄ ∂_I K`, so hermiticity
  *is* this commutation.

Hypothesis-bearing rules are stated **pointwise** (at `u`, with
`DifferentiableAt`) — the weakest form, suitable for functions differentiable
only on a proper subdomain (e.g. a slit-domain log Kähler potential); a
consumer wanting a function-level equation `funext`s locally. The
hypothesis-free constant and coordinate facts are stated as function
equalities.

## ii. Key results

- `Physlib.Wirtinger.dWirtingerCoord` / `dWirtingerAntiCoord` : the
    coordinate Wirtinger operators, definitionally the directional operators
    along `Pi.single I 1`.
- `Physlib.Wirtinger.coordProjCLM` / `conjCoordCLM` / `conjCLM` : the
    coordinate projection, the conjugated coordinate, and pointwise
    conjugation as `ℝ`-linear CLMs; `conjCLM` is conjugate-`ℂ`-linear
    (`conjCLM_smul_I`).
- `Physlib.Wirtinger.hasFDerivAt_restrictScalarsℝℂ` : restrict a complex 1-D
    Fréchet derivative on `ℂ → ℂ` to `ℝ`-scalars — the codomain bridge feeding a
    holomorphic outer `g : ℂ → ℂ` into the chain rules.
- `Physlib.Wirtinger.differentiableAt_real_of_complex` /
    `fderivReal_apply_eq_complex` : the `ℝ`/`ℂ` `restrictScalars` Pi-domain
    bridge, projected so no lemma type carries `restrictScalars`.
- `Physlib.Wirtinger.dWirtingerCoord_coordProj` /
    `dWirtingerAntiCoord_coordProj` / `dWirtingerCoord_conjCoord` /
    `dWirtingerAntiCoord_conjCoord` : the four Kronecker coordinate values
    `∂z^J/∂z^I = δ_IJ`, `∂z̄^J/∂z̄^I = δ_IJ`, `∂z^J/∂z̄^I = ∂z̄^J/∂z^I = 0`.
- `Physlib.Wirtinger.dWirtingerCoord_eq_complex_fderiv` /
    `dWirtingerAntiCoord_eq_zero_of_holomorphic` : holomorphic collapse for
    the coordinate operators (with anti-holomorphic duals).
- `Physlib.Wirtinger.dWirtingerCoord_comp_apply` /
    `dWirtingerCoord_comp_holomorphic_apply` (and their anti-holomorphic duals): the
    two-term Wirtinger chain rule for an outer `g : ℂ → ℂ`, collapsing to
    the single-term `deriv g · ∂_I f` for holomorphic `g`.
- `Physlib.Wirtinger.dWirtingerCoord_coordDiff` /
    `dWirtingerAntiCoord_coordDiff` : Wirtinger derivatives of the
    coordinate difference `z^J − z̄^J`.
- `Physlib.Wirtinger.dWirtingerCoord_dWirtingerAntiCoord_comm` : Schwarz's
    theorem for the coordinate operators, `∂_I ∂_J̄ f = ∂_J̄ ∂_I f` on
    `C²` `f`.

## iii. Table of contents

- A. The coordinate Wirtinger operators
- B. The Pi-domain `restrictScalars` bridge
- C. Properties of `dWirtingerCoord`
- D. Properties of `dWirtingerAntiCoord`
- E. Wirtinger chain rules for an outer function
- F. Schwarz's theorem for the coordinate operators

-/

@[expose] public section
noncomputable section

namespace Physlib.Wirtinger

variable {ι : Type*}

/-- Restrict a complex 1-D Fréchet derivative on `ℂ → ℂ` to `ℝ`-scalars: the
codomain half of the `ℝ`/`ℂ` `restrictScalars` bridge, used to feed a holomorphic
outer function `g : ℂ → ℂ` into the real-derivative chain rules (§E). -/
lemma hasFDerivAt_restrictScalarsℝℂ {f : ℂ → ℂ} {f' : ℂ →L[ℂ] ℂ}
    {z : ℂ} (hf : HasFDerivAt f f' z) :
    HasFDerivAt f (f'.restrictScalars ℝ) z :=
  -- The `@`-application is required: the shorthand `hf.restrictScalars ℝ` fails with
  -- `failed to synthesize IsScalarTower ℝ ℂ ℂ`. There are two routes to `SMul ℝ ℂ`,
  -- via `Algebra ℝ ℂ` and via `NormedSpace ℝ ℂ`; `restrictScalars` demands the
  -- `NormedSpace` spelling while `IsScalarTower.right` supplies the `Algebra` one.
  -- They are defeq but not syntactically equal, and instance search matches only
  -- shallowly, so it fails; passing `IsScalarTower.right` positionally via `@` routes
  -- the slot through unification, which sees the defeq and succeeds.
  @HasFDerivAt.restrictScalars ℝ _ ℂ _ _
    ℂ _ _ _ (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
    ℂ _ _ _ (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
    _ _ _ hf

/-- The I-th coordinate `z^I = u I` as an ℝ-linear CLM on `ι → ℂ`. -/
def coordProjCLM (I : ι) : (ι → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) I

@[simp] lemma coordProjCLM_apply (I : ι) (u : ι → ℂ) : coordProjCLM I u = u I := rfl

/-- The conjugated I-th coordinate `z̄^I = star (u I)` as an ℝ-linear CLM (not ℂ-linear). -/
def conjCoordCLM (I : ι) : (ι → ℂ) →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp (coordProjCLM I)

@[simp] lemma conjCoordCLM_apply (I : ι) (u : ι → ℂ) : conjCoordCLM I u = star (u I) := rfl

/-- Pointwise conjugation of a point of `ι → ℂ`, as a plain function. -/
def conjConfig (u : ι → ℂ) : ι → ℂ := fun I => star (u I)

@[simp] lemma conjConfig_apply (u : ι → ℂ) (I : ι) : conjConfig u I = star (u I) := rfl

/-- Pointwise conjugation bundled as an ℝ-linear CLM (conjugate-ℂ-linear). -/
def conjCLM : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi (fun I => conjCoordCLM I)

@[simp] lemma conjCLM_apply (u : ι → ℂ) : conjCLM u = conjConfig u := rfl

/-- `conjCLM` is conjugate-ℂ-linear: `conj (i·d) = -(i · conj d)`. -/
lemma conjCLM_smul_I (d : ι → ℂ) :
    conjCLM (Complex.I • d) = -(Complex.I • conjCLM (ι := ι) d) := by
  funext I
  simp only [conjCLM_apply, conjConfig_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, star_mul', Complex.star_def, Complex.conj_I]
  ring

/-!

## A. The coordinate Wirtinger operators

The two coordinate Wirtinger operators are the directional Wirtinger derivatives
of `Wirtinger.Multivariable` along the I-th coordinate direction `Pi.single I 1`:

  dWirtingerCoord f I    = (1/2) · (∂_x − i · ∂_y) f
  dWirtingerAntiCoord f I = (1/2) · (∂_x + i · ∂_y) f

where `∂_x` and `∂_y` are the real Fréchet derivatives of `f` along the slot-I
real and imaginary coordinate directions `Pi.single I 1` and
`Pi.single I Complex.I` (the latter is `Complex.I • Pi.single I 1`). The sign on
the imaginary-direction term is the only difference, making the two operators
dual on (anti)holomorphic functions (§C, §D).

-/

variable [Fintype ι] [DecidableEq ι]

/-- Holomorphic Wirtinger derivative along the I-th coordinate of `ι → ℂ`. -/
def dWirtingerCoord (f : (ι → ℂ) → ℂ) (I : ι) : (ι → ℂ) → ℂ :=
  fun u => dWirtingerDir f (Pi.single I 1) u

/-- Anti-holomorphic Wirtinger derivative along the I-th coordinate of `ι → ℂ`. -/
def dWirtingerAntiCoord (f : (ι → ℂ) → ℂ) (I : ι) : (ι → ℂ) → ℂ :=
  fun u => dWirtingerAntiDir f (Pi.single I 1) u

omit [Fintype ι] in
/-- `c • Pi.single I 1 = Pi.single I c`: in particular the imaginary coordinate
direction `Pi.single I i` is `i` times the real one. -/
private lemma smul_single_one (I : ι) (c : ℂ) :
    c • (Pi.single I 1 : (ι → ℂ)) = Pi.single I c := by
  rw [← Pi.single_smul', smul_eq_mul, mul_one]

/-- The coordinate operators are the directional Wirtinger derivatives along the
coordinate direction `Pi.single I 1` (definitional). -/
lemma dWirtingerCoord_eq_dWirtingerDir (f : (ι → ℂ) → ℂ) (I : ι)
    (u : (ι → ℂ)) :
    dWirtingerCoord f I u = dWirtingerDir f (Pi.single I 1) u := rfl

/-- The anti-holomorphic coordinate operator is the anti-holomorphic directional Wirtinger
derivative along `Pi.single I 1` (definitional). -/
lemma dWirtingerAntiCoord_eq_dWirtingerAntiDir (f : (ι → ℂ) → ℂ)
    (I : ι)
    (u : (ι → ℂ)) :
    dWirtingerAntiCoord f I u = dWirtingerAntiDir f (Pi.single I 1) u := rfl

/-- Real-Fréchet form of `dWirtingerCoord`:
`dWirtingerCoord f I u = (1/2)(∂_x − i · ∂_y) f`,
the derivatives along the slot-I real and imaginary coordinate directions.
Unconditional — the directional definition makes it definitional
(`Complex.I • Pi.single I 1 = Pi.single I Complex.I`); no differentiability
hypothesis is needed. -/
lemma dWirtingerCoord_apply {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (I : ι) :
    dWirtingerCoord f I u = (1 / 2 : ℂ) * (fderiv ℝ f u (Pi.single I 1)
      - Complex.I * fderiv ℝ f u (Pi.single I Complex.I)) := by
  simp only [dWirtingerCoord, dWirtingerDir, smul_single_one]

/-- Real-Fréchet form of `dWirtingerAntiCoord`; mirror of `dWirtingerCoord_apply` with the
sign flip on the imaginary-direction term. Unconditional, as for `dWirtingerCoord_apply`. -/
lemma dWirtingerAntiCoord_apply {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (I : ι) :
    dWirtingerAntiCoord f I u = (1 / 2 : ℂ) * (fderiv ℝ f u (Pi.single I 1)
      + Complex.I * fderiv ℝ f u (Pi.single I Complex.I)) := by
  simp only [dWirtingerAntiCoord, dWirtingerAntiDir, smul_single_one]

/-!

## B. The Pi-domain restrictScalars bridge

The holomorphic collapse needs `ℂ`-linearity of the *real* Fréchet derivative,
which on the `ι → ℂ` domain meets the `ℝ`/`ℂ` `restrictScalars` diamond. The
private bridge `differentiableAt_real_and_fderiv_eq` pays the `@`-application
ceremony once, with clean conclusions (no `restrictScalars` in any lemma type).

-/

omit [DecidableEq ι] in
/-- The `ℝ`/`ℂ` `restrictScalars` bridge on the `ι → ℂ` domain, paid once and
packaged so that `restrictScalars` stays out of every lemma *type*: stating it in
a type re-triggers the codomain `IsScalarTower ℝ ℂ ℂ` module diamond (see
`hasFDerivAt_restrictScalarsℝℂ`), and only a `have`-inferred occurrence is diamond-free. The
`@`-application ceremony lives here; `differentiableAt_real_of_complex` and
`fderivReal_apply_eq_complex` project out its two halves. -/
private lemma differentiableAt_real_and_fderiv_eq {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (hf : DifferentiableAt ℂ f u) :
    DifferentiableAt ℝ f u ∧ ∀ d, fderiv ℝ f u d = fderiv ℂ f u d := by
  have hfr := @HasFDerivAt.restrictScalars ℝ _ ℂ _ _
    ((ι → ℂ)) _ _ _
      (inferInstance : IsScalarTower ℝ ℂ ((ι → ℂ)))
    ℂ _ _ _ (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ) _ _ _ hf.hasFDerivAt
  exact ⟨hfr.differentiableAt,
    fun d => by simp only [hfr.fderiv, ContinuousLinearMap.coe_restrictScalars']⟩

omit [DecidableEq ι] in
/-- A `ℂ`-differentiable function on `(ι → ℂ)` is
`ℝ`-differentiable. -/
lemma differentiableAt_real_of_complex {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (hf : DifferentiableAt ℂ f u) :
    DifferentiableAt ℝ f u :=
  (differentiableAt_real_and_fderiv_eq hf).1

omit [DecidableEq ι] in
/-- The real Fréchet derivative of a holomorphic function equals its complex one,
pointwise — the single rewrite the collapse-family lemmas consume. -/
lemma fderivReal_apply_eq_complex {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (hf : DifferentiableAt ℂ f u)
    (d : (ι → ℂ)) :
    fderiv ℝ f u d = fderiv ℂ f u d :=
  (differentiableAt_real_and_fderiv_eq hf).2 d

omit [DecidableEq ι] in
/-- The real derivative of a holomorphic function is `ℂ`-linear along every
direction — the hypothesis the foundation collapse `dWirtingerDir_eq_of_clinear`
consumes, produced at the `ι → ℂ` domain through the bridge. -/
private lemma clinear_of_holomorphic {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (hf : DifferentiableAt ℂ f u)
    (d : (ι → ℂ)) :
    fderiv ℝ f u (Complex.I • d) = Complex.I • fderiv ℝ f u d := by
  rw [fderivReal_apply_eq_complex hf (Complex.I • d), fderivReal_apply_eq_complex hf d, map_smul]

omit [Fintype ι] in
/-- `conjConfig` fixes the real coordinate direction `Pi.single I 1` (since `star 1 = 1`). -/
private lemma conjConfig_single_one (I : ι) :
    conjConfig (Pi.single I (1 : ℂ)) = Pi.single I 1 := by
  funext J
  rw [conjConfig_apply]
  rcases eq_or_ne J I with h | h
  · subst h; rw [Pi.single_eq_same]; exact star_one ℂ
  · rw [Pi.single_eq_of_ne h]; exact star_zero ℂ

omit [DecidableEq ι] [Fintype ι] in
/-- The real Fréchet derivative of the J-th coordinate projection `v ↦ v J`. -/
private lemma fderiv_coordProj (J : ι) (u d : (ι → ℂ)) :
    fderiv ℝ (fun v : (ι → ℂ) => v J) u d = d J := by
  have h : HasFDerivAt (fun v : (ι → ℂ) => v J)
      (coordProjCLM J) u :=
    (coordProjCLM J).hasFDerivAt
  rw [h.fderiv, coordProjCLM_apply]

/-!

## C. Properties of `dWirtingerCoord`

Each rule is the `d = Pi.single I 1` specialisation of its `Wirtinger`
foundation analogue. Rules carrying a differentiability hypothesis are stated
**pointwise** (at `u`, hypothesis `DifferentiableAt`) — the weakest form, and the
one to reach for on a function differentiable only on a proper domain (e.g. the
`Hⁿ` log Kähler potential, regular only on its slit domain); a consumer wanting
a function-level equation `funext`s locally. The hypothesis-free constant and
coordinate facts are stated as function equalities — the constant and
holomorphic-coordinate ones (`dWirtingerCoord_const`, `dWirtingerCoord_coordProj`) `@[simp]`.

-/

section

variable {f g : (ι → ℂ) → ℂ}

/-- `dWirtingerCoord` is local: functions agreeing on a neighbourhood of `u` have equal
holomorphic Wirtinger derivative at `u`. -/
lemma dWirtingerCoord_congr_of_eventuallyEq_apply {f₁ f₂ : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (h : f₁ =ᶠ[nhds u] f₂) (I : ι) :
    dWirtingerCoord f₁ I u = dWirtingerCoord f₂ I u :=
  dWirtingerDir_congr_of_eventuallyEq h (Pi.single I 1)

/-- Constants have zero coordinate derivative. -/
@[simp] lemma dWirtingerCoord_const (c : ℂ) (I : ι) :
    dWirtingerCoord (fun _ : (ι → ℂ) => c) I = 0 := by
  funext u; exact dWirtingerDir_const c (Pi.single I 1) u

/-- The zero function has zero coordinate derivative. -/
@[simp] lemma dWirtingerCoord_zero (I : ι) :
    dWirtingerCoord (0 : (ι → ℂ) → ℂ) I = 0 :=
  dWirtingerCoord_const 0 I

/-- Pointwise negation rule for the holomorphic coordinate derivative at `u`. -/
lemma dWirtingerCoord_neg_apply {u : (ι → ℂ)} (I : ι) :
    dWirtingerCoord (fun v => -(f v)) I u = -(dWirtingerCoord f I u) :=
  dWirtingerDir_neg f (Pi.single I 1) u

/-- `∂z^J / ∂z^I = δ_IJ`. -/
@[simp] lemma dWirtingerCoord_coordProj (I J : ι) :
    dWirtingerCoord (fun u : (ι → ℂ) => u J) I =
      fun _ => if I = J then 1 else 0 := by
  funext u
  rw [dWirtingerCoord_apply I, fderiv_coordProj, fderiv_coordProj]
  by_cases h : I = J
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, if_pos rfl, Complex.I_mul_I]; ring
  · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h), if_neg h,
      mul_zero, sub_zero, mul_zero]

/-- Pointwise additivity of the holomorphic coordinate derivative at `u`. -/
lemma dWirtingerCoord_add_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerCoord (f + g) I u = dWirtingerCoord f I u + dWirtingerCoord g I u :=
  dWirtingerDir_add hf hg (Pi.single I 1)

/-- Pointwise compatibility with complex scalar multiplication at `u`. -/
lemma dWirtingerCoord_smul_apply {u : (ι → ℂ)}
    (c : ℂ) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerCoord (c • f) I u = c • dWirtingerCoord f I u :=
  dWirtingerDir_smul c hf (Pi.single I 1)

/-- Pointwise Leibniz rule for the holomorphic coordinate derivative at `u`. -/
lemma dWirtingerCoord_mul_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerCoord (f * g) I u =
      dWirtingerCoord f I u * g u + f u * dWirtingerCoord g I u :=
  dWirtingerDir_mul hf hg (Pi.single I 1)

/-- Pointwise finite-sum rule for holomorphic coordinate derivatives at `u`. -/
lemma dWirtingerCoord_fun_sum_apply {α : Type*} {s : Finset α}
    {F : α → (ι → ℂ) → ℂ} {u : (ι → ℂ)}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (I : ι) :
    dWirtingerCoord (fun v => ∑ a ∈ s, F a v) I u =
      ∑ a ∈ s, dWirtingerCoord (F a) I u :=
  dWirtingerDir_fun_sum hF (Pi.single I 1)

/-- For a holomorphic function, `dWirtingerCoord` is the complex Fréchet derivative in
the corresponding coordinate direction. -/
lemma dWirtingerCoord_eq_complex_fderiv_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℂ f u) (I : ι) :
    dWirtingerCoord f I u = fderiv ℂ f u (Pi.single I 1) := by
  show dWirtingerDir f (Pi.single I 1) u = fderiv ℂ f u (Pi.single I 1)
  rw [dWirtingerDir_eq_of_clinear (clinear_of_holomorphic hf _), fderivReal_apply_eq_complex hf]

/-- Global version of `dWirtingerCoord_eq_complex_fderiv_apply`. -/
lemma dWirtingerCoord_eq_complex_fderiv (hf : Differentiable ℂ f) (I : ι) :
    dWirtingerCoord f I = fun u => fderiv ℂ f u (Pi.single I 1) := by
  funext u; exact dWirtingerCoord_eq_complex_fderiv_apply (hf u) I

/-- An antiholomorphic function — a ℂ-differentiable `g` precomposed with
`conjConfig` — has zero holomorphic Wirtinger derivative at `u`. -/
lemma dWirtingerCoord_eq_zero_of_antiHolomorphic_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (conjConfig u)) (I : ι) :
    dWirtingerCoord (fun v : (ι → ℂ) => g (conjConfig v)) I u = 0 := by
  have hgr : DifferentiableAt ℝ g (conjCLM u) := by
    rw [conjCLM_apply]; exact differentiableAt_real_of_complex hg
  show dWirtingerDir (fun v : (ι → ℂ) => g (conjConfig v))
      (Pi.single I 1) u = 0
  rw [show (fun v : (ι → ℂ) => g (conjConfig v))
      = fun v => g (conjCLM v) from by funext v; rw [conjCLM_apply],
    dWirtingerDir_comp_conjLinear conjCLM_smul_I hgr]
  simp only [conjCLM_apply]
  exact dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic hg _)

/-- Antiholomorphic functions have zero holomorphic Wirtinger derivative. -/
lemma dWirtingerCoord_eq_zero_of_antiHolomorphic (hg : Differentiable ℂ g) (I : ι) :
    dWirtingerCoord (fun u : (ι → ℂ) => g (conjConfig u)) I = 0 := by
  funext u; exact dWirtingerCoord_eq_zero_of_antiHolomorphic_apply (hg (conjConfig u)) I

end

/-!

## D. Properties of `dWirtingerAntiCoord`

`dWirtingerAntiCoord` mirrors `dWirtingerCoord` with `z` and `z̄` swapped. The two anti-coordinate
values `∂z̄^J/∂z^I` (`dWirtingerCoord_conjCoord`) and `∂z̄^J/∂z̄^I`
(`dWirtingerAntiCoord_conjCoord`) are collected here — one for each operator — since
both are conjugates of the §C holomorphic-coordinate values (`z̄^J = star z^J`), read
off through `dWirtingerDir` / `dWirtingerAntiDir_star_comp`.

-/

section

variable {f g : (ι → ℂ) → ℂ}

/-- `dWirtingerAntiCoord` is local. -/
lemma dWirtingerAntiCoord_congr_of_eventuallyEq_apply {f₁ f₂ : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (h : f₁ =ᶠ[nhds u] f₂) (I : ι) :
    dWirtingerAntiCoord f₁ I u = dWirtingerAntiCoord f₂ I u :=
  dWirtingerAntiDir_congr_of_eventuallyEq h (Pi.single I 1)

/-- Constants have zero anti-holomorphic coordinate derivative. -/
@[simp] lemma dWirtingerAntiCoord_const (c : ℂ) (I : ι) :
    dWirtingerAntiCoord (fun _ : (ι → ℂ) => c) I = 0 := by
  funext u; exact dWirtingerAntiDir_const c (Pi.single I 1) u

/-- The zero function has zero anti-holomorphic coordinate derivative. -/
@[simp] lemma dWirtingerAntiCoord_zero (I : ι) :
    dWirtingerAntiCoord (0 : (ι → ℂ) → ℂ) I = 0 :=
  dWirtingerAntiCoord_const 0 I

/-- Pointwise negation rule for the anti-holomorphic coordinate derivative at `u`. -/
lemma dWirtingerAntiCoord_neg_apply {u : (ι → ℂ)} (I : ι) :
    dWirtingerAntiCoord (fun v => -(f v)) I u = -(dWirtingerAntiCoord f I u) :=
  dWirtingerAntiDir_neg f (Pi.single I 1) u

/-- `∂z^J / ∂z̄^I = 0`. -/
@[simp] lemma dWirtingerAntiCoord_coordProj (I J : ι) :
    dWirtingerAntiCoord (fun u : (ι → ℂ) => u J) I = 0 := by
  funext u
  simp only [Pi.zero_apply]
  rw [dWirtingerAntiCoord_apply I, fderiv_coordProj, fderiv_coordProj]
  by_cases h : I = J
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, Complex.I_mul_I]; ring
  · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h),
      mul_zero, add_zero, mul_zero]

/-- `∂z̄^J / ∂z^I = 0`. The conjugate of `dWirtingerAntiCoord_coordProj` (`z̄^J = star z^J`),
read off through `dWirtingerDir_star_comp` rather than recomputed. -/
lemma dWirtingerCoord_conjCoord (I J : ι) :
    dWirtingerCoord (fun u : (ι → ℂ) => conjConfig u J) I = 0 := by
  funext u
  have hd : DifferentiableAt ℝ (fun w : (ι → ℂ) => w J) u :=
    (coordProjCLM J).differentiableAt
  change dWirtingerDir (fun v => star ((fun w : (ι → ℂ) => w J) v))
      (Pi.single I 1) u = 0
  rw [dWirtingerDir_star_comp hd (Pi.single I 1), ← dWirtingerAntiCoord_eq_dWirtingerAntiDir,
    dWirtingerAntiCoord_coordProj, Pi.zero_apply, star_zero]

/-- `∂z̄^J / ∂z̄^I = δ_IJ`. The conjugate of `dWirtingerCoord_coordProj`, read off through
`dWirtingerAntiDir_star_comp` rather than recomputed. -/
lemma dWirtingerAntiCoord_conjCoord (I J : ι) :
    dWirtingerAntiCoord (fun u : (ι → ℂ) => conjConfig u J) I =
      fun _ => if I = J then 1 else 0 := by
  funext u
  have hd : DifferentiableAt ℝ (fun w : (ι → ℂ) => w J) u :=
    (coordProjCLM J).differentiableAt
  change dWirtingerAntiDir (fun v => star ((fun w : (ι → ℂ) => w J) v))
      (Pi.single I 1) u = if I = J then 1 else 0
  rw [dWirtingerAntiDir_star_comp hd (Pi.single I 1), ← dWirtingerCoord_eq_dWirtingerDir,
    dWirtingerCoord_coordProj]
  simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero]

/-- Pointwise additivity of the anti-holomorphic coordinate derivative at `u`. -/
lemma dWirtingerAntiCoord_add_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerAntiCoord (f + g) I u = dWirtingerAntiCoord f I u + dWirtingerAntiCoord g I u :=
  dWirtingerAntiDir_add hf hg (Pi.single I 1)

/-- Pointwise compatibility with complex scalar multiplication at `u`. -/
lemma dWirtingerAntiCoord_smul_apply {u : (ι → ℂ)}
    (c : ℂ) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (c • f) I u = c • dWirtingerAntiCoord f I u :=
  dWirtingerAntiDir_smul c hf (Pi.single I 1)

/-- Pointwise Leibniz rule for the anti-holomorphic coordinate derivative at `u`. -/
lemma dWirtingerAntiCoord_mul_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerAntiCoord (f * g) I u =
      dWirtingerAntiCoord f I u * g u + f u * dWirtingerAntiCoord g I u :=
  dWirtingerAntiDir_mul hf hg (Pi.single I 1)

/-- Pointwise finite-sum rule for anti-holomorphic coordinate derivatives at `u`. -/
lemma dWirtingerAntiCoord_fun_sum_apply {α : Type*} {s : Finset α}
    {F : α → (ι → ℂ) → ℂ} {u : (ι → ℂ)}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (I : ι) :
    dWirtingerAntiCoord (fun v => ∑ a ∈ s, F a v) I u =
      ∑ a ∈ s, dWirtingerAntiCoord (F a) I u :=
  dWirtingerAntiDir_fun_sum hF (Pi.single I 1)

/-!

### Coordinate-difference Wirtinger derivatives

The Wirtinger derivatives of the coordinate difference `z^J − z̄^J`. This
expression is the imaginary part of a coordinate up to a factor of
`i`: `z^J − z̄^J = 2 i Im(u^J)`, so any function built from `Im` of the
coordinates eventually differentiates against it. Collecting the four lemmas
here saves every such consumer from re-running the same additivity chain by hand
— `{dWirtingerCoord,dWirtingerAntiCoord}_add_apply`, the pointwise
`{dWirtingerCoord,dWirtingerAntiCoord}_neg_apply`, and the §C/§D coordinate values
(`dWirtingerCoord_coordProj` / `dWirtingerCoord_conjCoord` and their anti-holomorphic duals).

-/

omit [DecidableEq ι] in
/-- The coordinate-difference function `v ↦ z^J − z̄^J` is real-differentiable:
the difference of the coordinate CLMs `coordProjCLM J` and `conjCoordCLM J`. -/
lemma differentiable_coordDiff (J : ι) :
    Differentiable ℝ (fun v : (ι → ℂ) => v J - conjConfig v J) :=
  (coordProjCLM J).differentiable.sub (conjCoordCLM J).differentiable

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinate difference `z^J − z̄^J` as a sum of the holomorphic coordinate
and the negated conjugate coordinate — the form on which the `dWirtingerCoord` /
`dWirtingerAntiCoord` additivity rules apply. -/
private lemma coordDiff_eq_add_neg (J : ι) :
    (fun v : (ι → ℂ) => v J - conjConfig v J)
      = (fun v => v J) + (fun v => -(conjConfig v J)) := by
  funext v; simp [sub_eq_add_neg]

/-- `∂(z^J − z̄^J) / ∂z^I = δ_IJ`, from `∂z^J/∂z^I = δ_IJ` and
`∂z̄^J/∂z^I = 0`. -/
lemma dWirtingerCoord_coordDiff (I J : ι) :
    dWirtingerCoord (fun v : (ι → ℂ) => v J - conjConfig v J) I
      = fun _ => if I = J then 1 else 0 := by
  funext u
  have hchi : DifferentiableAt ℝ (fun v : (ι → ℂ) => v J) u :=
    (coordProjCLM J).differentiableAt
  have hneganti : DifferentiableAt ℝ
      (fun v : (ι → ℂ) => -(conjConfig v J)) u :=
    (conjCoordCLM J).differentiableAt.neg
  rw [coordDiff_eq_add_neg, dWirtingerCoord_add_apply hchi hneganti I, dWirtingerCoord_neg_apply I,
    dWirtingerCoord_coordProj, dWirtingerCoord_conjCoord]
  simp

/-- `∂(z^J − z̄^J) / ∂z̄^I = −δ_IJ`, from `∂z^J/∂z̄^I = 0` and
`∂z̄^J/∂z̄^I = δ_IJ`. -/
lemma dWirtingerAntiCoord_coordDiff (I J : ι) :
    dWirtingerAntiCoord (fun v : (ι → ℂ) => v J - conjConfig v J) I
      = fun _ => if I = J then -1 else 0 := by
  funext u
  have hchi : DifferentiableAt ℝ (fun v : (ι → ℂ) => v J) u :=
    (coordProjCLM J).differentiableAt
  have hneganti : DifferentiableAt ℝ
      (fun v : (ι → ℂ) => -(conjConfig v J)) u :=
    (conjCoordCLM J).differentiableAt.neg
  rw [coordDiff_eq_add_neg, dWirtingerAntiCoord_add_apply hchi hneganti I,
    dWirtingerAntiCoord_neg_apply I, dWirtingerAntiCoord_coordProj, dWirtingerAntiCoord_conjCoord]
  by_cases h : I = J <;> simp [h]

/-- For an antiholomorphic function the anti-holomorphic Wirtinger derivative equals
the complex Fréchet derivative of `g` at `conjConfig u` along the slot-I real
coordinate direction. Dual of `dWirtingerCoord_eq_complex_fderiv_apply`. -/
lemma dWirtingerAntiCoord_eq_complex_fderiv_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (conjConfig u)) (I : ι) :
    dWirtingerAntiCoord (fun v : (ι → ℂ) => g (conjConfig v)) I u =
      fderiv ℂ g (conjConfig u) (Pi.single I 1) := by
  have hgr : DifferentiableAt ℝ g (conjCLM u) := by
    rw [conjCLM_apply]; exact differentiableAt_real_of_complex hg
  show dWirtingerAntiDir (fun v : (ι → ℂ) => g (conjConfig v))
      (Pi.single I 1) u = fderiv ℂ g (conjConfig u) (Pi.single I 1)
  rw [show (fun v : (ι → ℂ) => g (conjConfig v))
      = fun v => g (conjCLM v) from by funext v; rw [conjCLM_apply],
    dWirtingerAntiDir_comp_conjLinear conjCLM_smul_I hgr]
  simp only [conjCLM_apply, conjConfig_single_one]
  rw [dWirtingerDir_eq_of_clinear (clinear_of_holomorphic hg _), fderivReal_apply_eq_complex hg]

/-- Global version of `dWirtingerAntiCoord_eq_complex_fderiv_apply`. -/
lemma dWirtingerAntiCoord_eq_complex_fderiv (hg : Differentiable ℂ g) (I : ι) :
    dWirtingerAntiCoord (fun u : (ι → ℂ) => g (conjConfig u)) I =
      fun u => fderiv ℂ g (conjConfig u) (Pi.single I 1) := by
  funext u; exact dWirtingerAntiCoord_eq_complex_fderiv_apply (hg (conjConfig u)) I

/-- Holomorphic functions have zero anti-holomorphic coordinate derivative. -/
lemma dWirtingerAntiCoord_eq_zero_of_holomorphic_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℂ f u) (I : ι) :
    dWirtingerAntiCoord f I u = 0 := by
  show dWirtingerAntiDir f (Pi.single I 1) u = 0
  exact dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic hf _)

/-- Global version of `dWirtingerAntiCoord_eq_zero_of_holomorphic_apply`. -/
lemma dWirtingerAntiCoord_eq_zero_of_holomorphic (hf : Differentiable ℂ f) (I : ι) :
    dWirtingerAntiCoord f I = 0 := by
  funext u; exact dWirtingerAntiCoord_eq_zero_of_holomorphic_apply (hf u) I

end

/-!

## E. Wirtinger chain rules for an outer function

The Wirtinger chain rules for the coordinate operators composed with a complex outer
function `g : ℂ → ℂ`, each the `d = Pi.single I 1` case of the foundation chain
rule. The outer `g` enters only through its directional derivatives
`dWirtingerDir g 1` / `dWirtingerAntiDir g 1`.

Those two numbers are the holomorphic and anti-holomorphic parts of `g`'s real Fréchet
derivative: every real-linear map `ℂ → ℂ` decomposes uniquely as
`h ↦ a · h + b · star h`, and at `z = f u` (the image of `u` under the inner
function, where the chain rule evaluates `g`'s derivatives) the pair `(a, b)` is
exactly `(dWirtingerDir g 1 z, dWirtingerAntiDir g 1 z)`. The universal two-term
chain rule is this decomposition substituted into the real chain rule. For
holomorphic `g` the anti-holomorphic part vanishes and the holomorphic part collapses to
`deriv g z`, turning the universal form into the single-term rule
`deriv g (f u) · ∂_I f(u)`.

-/

/-- The real Fréchet derivative of a holomorphic outer `g : ℂ → ℂ` is `ℝ`-linear
multiplication by `deriv g z`. -/
private lemma outerHolo_fderiv_restrictScalars {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) :
    fderiv ℝ g z =
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv g z)).restrictScalars ℝ :=
  (hasFDerivAt_restrictScalarsℝℂ hg.hasDerivAt.hasFDerivAt).fderiv

/-- The real derivative of a holomorphic outer `g` is `ℂ`-linear along every
direction — the hypothesis the foundation collapse consumes at `V = ℂ`. -/
private lemma outerHolo_clinear {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (d : ℂ) :
    fderiv ℝ g z (Complex.I • d) = Complex.I • fderiv ℝ g z d := by
  rw [outerHolo_fderiv_restrictScalars hg]
  simp only [ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- On a holomorphic outer `g`, the holomorphic directional derivative along `1`
collapses to the ordinary complex derivative `deriv g`. -/
private lemma dWirtingerDir_one_eq_deriv {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) :
    dWirtingerDir g 1 z = deriv g z := by
  rw [dWirtingerDir_eq_of_clinear (outerHolo_clinear hg 1), outerHolo_fderiv_restrictScalars hg]
  simp only [ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- On a holomorphic outer `g`, the anti-holomorphic directional derivative along `1`
vanishes. -/
private lemma dWirtingerAntiDir_one_eq_zero {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) :
    dWirtingerAntiDir g 1 z = 0 :=
  dWirtingerAntiDir_eq_zero_of_clinear (outerHolo_clinear hg 1)

section

variable {g : ℂ → ℂ} {f : (ι → ℂ) → ℂ}

/-- Full pointwise chain rule for a real-differentiable outer function. -/
lemma dWirtingerCoord_comp_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℝ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerCoord (fun v => g (f v)) I u =
      dWirtingerDir g 1 (f u) * dWirtingerCoord f I u
        + dWirtingerAntiDir g 1 (f u) *
          dWirtingerCoord (fun v : (ι → ℂ) => star (f v)) I u :=
  dWirtingerDir_comp hg hf (Pi.single I 1)

/-- Pointwise chain rule for a holomorphic outer function. -/
lemma dWirtingerCoord_comp_holomorphic_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerCoord (fun v => g (f v)) I u =
      deriv g (f u) * dWirtingerCoord f I u := by
  rw [dWirtingerCoord_comp_apply
      (Physlib.Wirtinger.hasFDerivAt_restrictScalarsℝℂ hg.hasFDerivAt).differentiableAt hf I,
    dWirtingerDir_one_eq_deriv hg, dWirtingerAntiDir_one_eq_zero hg, zero_mul, add_zero]

/-- Conjugating the inner expression: `∂(f̄)/∂z^I = conj (∂f/∂z̄^I)`. -/
lemma dWirtingerCoord_star_comp_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerCoord (fun v : (ι → ℂ) => star (f v)) I u =
      star (dWirtingerAntiCoord f I u) :=
  dWirtingerDir_star_comp hf (Pi.single I 1)

/-- Full pointwise chain rule for a real-differentiable outer function,
anti-holomorphic version. -/
lemma dWirtingerAntiCoord_comp_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℝ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (fun v => g (f v)) I u =
      dWirtingerDir g 1 (f u) * dWirtingerAntiCoord f I u
        + dWirtingerAntiDir g 1 (f u) *
          dWirtingerAntiCoord (fun v : (ι → ℂ) => star (f v)) I u :=
  dWirtingerAntiDir_comp hg hf (Pi.single I 1)

/-- Pointwise chain rule for a holomorphic outer function, anti-holomorphic version. -/
lemma dWirtingerAntiCoord_comp_holomorphic_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (fun v => g (f v)) I u =
      deriv g (f u) * dWirtingerAntiCoord f I u := by
  rw [dWirtingerAntiCoord_comp_apply
      (Physlib.Wirtinger.hasFDerivAt_restrictScalarsℝℂ hg.hasFDerivAt).differentiableAt hf I,
    dWirtingerDir_one_eq_deriv hg, dWirtingerAntiDir_one_eq_zero hg, zero_mul, add_zero]

/-- Conjugating the inner expression: `∂(f̄)/∂z̄^I = conj (∂f/∂z^I)`. -/
lemma dWirtingerAntiCoord_star_comp_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (fun v : (ι → ℂ) => star (f v)) I u =
      star (dWirtingerCoord f I u) :=
  dWirtingerAntiDir_star_comp hf (Pi.single I 1)

end

/-!

## F. Schwarz's theorem for the coordinate operators

The headline second-order results, immediate specialisations of the
multivariable theory along the coordinate directions `Pi.single I 1`:
differentiability of a first coordinate Wirtinger derivative, and **Schwarz's
theorem** for the mixed second derivative on a `C²` function,

  `∂_I ∂_J̄ f = ∂_J̄ ∂_I f`     (`dWirtingerCoord_dWirtingerAntiCoord_comm`)

This commutativity is the keystone of Kähler-metric hermiticity: with `K` real,
`g_{IJ̄} = ∂_I ∂_J̄ K` and `star (g_{JĪ}) = ∂_J̄ ∂_I K`, so hermiticity is
exactly this commutation.

-/

section

variable {f : (ι → ℂ) → ℂ} {u : (ι → ℂ)}

/-- On a `C²` function the holomorphic coordinate Wirtinger derivative is itself
real-differentiable — the `d = Pi.single I 1` case of
`differentiableAt_dWirtingerDir`. -/
lemma differentiableAt_dWirtingerCoord (hf2 : ContDiffAt ℝ 2 f u) (I : ι) :
    DifferentiableAt ℝ (fun v => dWirtingerCoord f I v) u :=
  differentiableAt_dWirtingerDir hf2 (Pi.single I 1)

/-- On a `C²` function the anti-holomorphic coordinate Wirtinger derivative is itself
real-differentiable; dual of `differentiableAt_dWirtingerCoord`. -/
lemma differentiableAt_dWirtingerAntiCoord (hf2 : ContDiffAt ℝ 2 f u) (J : ι) :
    DifferentiableAt ℝ (fun v => dWirtingerAntiCoord f J v) u :=
  differentiableAt_dWirtingerAntiDir hf2 (Pi.single J 1)

/-- **Schwarz's theorem** for the coordinate Wirtinger operators: on a `C²` function the
holomorphic and anti-holomorphic derivatives commute, `∂_I ∂_J̄ f = ∂_J̄ ∂_I f`. The
`d = Pi.single I 1`, `e = Pi.single J 1` case of the general
`dWirtingerDir_dWirtingerAntiDir_comm`. -/
theorem dWirtingerCoord_dWirtingerAntiCoord_comm (hf2 : ContDiffAt ℝ 2 f u) (I J : ι) :
    dWirtingerCoord (fun v => dWirtingerAntiCoord f J v) I u
      = dWirtingerAntiCoord (fun v => dWirtingerCoord f I v) J u :=
  dWirtingerDir_dWirtingerAntiDir_comm hf2 (Pi.single I 1) (Pi.single J 1)

end

end Physlib.Wirtinger
end
end
