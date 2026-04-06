/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.VariationalCalculus.IsTestFunction
/-!

# Fundamental lemma of the calculus of variations

The key took in variational calculus is:
```
∀ h, ∫ x, f x * h x = 0 → f = 0
```
which allows use to go from reasoning about integrals to reasoning about functions.

## Overview of variational calculus

The variational calculus API in Physlib is designed to match and formalize the physicists intuition
of variational calculus. It is not designed to be a general API for variational calculus.

Within variational caclulus we are interested in function transformations, `F : (X → U) → (Y → V)`.
In physics this functional is often of the form `L : (Time → U) → Time → ℝ`,
which represents the Lagrangian of a system. We will use this to explain the formalization
within this API.

The action is nominally given by
$$S[u] = \int L(u, t) dt,$$
however it is convenient to
introduce another function `φ` and define the action as
$$S[u] = \int φ(t)  L(u, t) dt.$$
In the end we will set `φ := fun _ => 1`.

We now consider $$\frac{\partial}{\partial s} S[u + s * \delta u]$$ at `s = 0`,
which is the variational derivative of `S` at `u` in the direction `δu`.
This is equal to
$$
\int φ(t) * \left. \frac{\partial}{\partial s} L(u + s * \delta u, t)\right|_{s = 0}dt
$$
Let us denote the function
$$
\delta u,\, t \mapsto \left. \frac{\partial}{\partial s} L(u + s * \delta u, t)\right|_{s = 0}
$$ as `Lᵤ : (Time → U) → (Time → ℝ)`.
Then the variational derivative is
$$\int φ (t) Lᵤ(δu, t) dt.$$

It may then be possible to find a function `Gᵤ : (Time → ℝ) → Time → U`
such that
$$
\int φ(t) Lᵤ(δu, t) dt = \int \langle Gᵤ(φ, t), δu(t)\rangle dt
$$
This is usually done by integration by parts.

We now set `φ := fun _ => 1` and get `grad u := Gᵤ (fun _ => 1)`, which is the
variational gradient at `u`. The Euler–Lagrange equations, for example, are then `grad u = 0`.

In our API, the relationship between
- `Lᵤ` and `Gᵤ` is captured by the `HasVarAdjoint`.
- `L` and  `Gᵤ` by `HasVarAdjDeriv`.
- `L` and `grad u` by `HasVarGradientAt`.

In practice we assume that `L` has a certain locality property
`IsLocalizedFunctionTransform`, which allows us to work with functions
`φ` and `δu` which have compact support.

This API assumes that `U` is an inner-product space. This can be considered as the full
configuration space, or a local chart thereof.

## References

- https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/Variational.20Calculus/with/529022834

-/

@[expose] public section

open MeasureTheory InnerProductSpace InnerProductSpace'

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace' ℝ V]
  {Y} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y][MeasurableSpace Y]

/-- A version of `fundamental_theorem_of_variational_calculus'` for `Continuous f`.
The proof uses assumption that source of `f` is finite-dimensional
inner-product space, so that a bump function with compact support exists via
`ContDiffBump.hasCompactSupport` from `Analysis.Calculus.BumpFunction.Basic`.

The proof is by contradiction, assume that there is `x₀` such that `f x₀ ≠ 0` then one construct
construct `g` test function *supported* on the neighborhood of `x₀` such that `⟪f x, g x⟫ ≥ 0`
and `⟪f x, g x⟫ > 0` on a neighborhood of x₀.

Using `Y` for the theorem below to make use of bump functions in InnerProductSpaces. `Y` is
a finite dimensional measurable space over `ℝ` with (standard) inner product.
-/

lemma fundamental_theorem_of_variational_calculus' {f : Y → V}
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace Y]
    (hf : Continuous f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0 := by
  -- assume ¬(f = 0)
    rw [funext_iff]; by_contra h₀
    obtain ⟨x₀, hx0⟩ := not_forall.1 h₀
    simp at hx0 -- hx0 : f x₀ ≠ 0

  -- [1] Proof that `f` is continuous at `x₀`.
  -- Embed into the true IP-space `WithLp 2 V`.
    let f₂ : Y → WithLp 2 V := toL2 ℝ ∘ f
    let x₂ := f₂ x₀
  -- x₂ ≠ 0 because `fromL2 (toL2 (f x₀)) = f x₀`
    have hx2 : x₂ ≠ 0 := by
      intro h; apply hx0; simpa [fromL2_toL2, LinearMap.map_zero] using congrArg (fromL2 ℝ) h
  -- continuity of f₂ at x₀
    have f₂_cont : Continuous f₂ := (toL2 ℝ).continuous.comp hf
    have hcont₂₀ : ∀ x, ContinuousAt f₂ x := by
    -- turn `Continuous f₂` into `∀ x, ContinuousAt f₂ x`
      rwa [continuous_iff_continuousAt] at f₂_cont
  -- now apply it at x₀
    have hcont₂ : ContinuousAt f₂ x₀ := hcont₂₀ x₀

  -- [2] find open neighborhood guaranteeing positive inner product with the center, based on
  -- which the test function `g` will be constructed.
  -- pick δ₂ so that on B(x₀, δ₂), ‖f₂ x - x₂‖ < ‖x₂‖/2
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
    Metric.continuousAt_iff.mp hcont₂ (‖x₂‖ / 2)
      (by simpa [half_pos] using (norm_pos_iff.mpr hx2))
  -- now the usual “add & subtract” proof inside WithLp 2 V
    have inner_pos₂ : ∀ x (hx : x ∈ Metric.ball x₀ δ₂), 0 < (⟪f₂ x, x₂⟫_ℝ : ℝ) := by
      intros x hx
    -- hx : x ∈ ball x₀ δ₂, so dist x x₀ < δ₂, hence
    -- this is |⟪u,v⟫| ≤ ‖u‖ * ‖v‖, in the genuine InnerProductSpace on WithLp 2 V
      have hclose : ‖f₂ x - x₂‖ < ‖x₂‖ / 2 := hδ₂ hx
      have hself : ⟪x₂, x₂⟫_ℝ = ‖x₂‖^2 := real_inner_self_eq_norm_sq (x₂ : WithLp 2 V)

      let u := f₂ x - x₂
      let v := x₂
      have hlow : -‖u‖ * ‖v‖ ≤ ⟪u, v⟫_ℝ := by
        have hpos' : ⟪-u, v⟫_ℝ ≤ ‖-u‖ * ‖v‖ := real_inner_le_norm (-u) v
        rw [norm_neg] at hpos'
        rw [inner_neg_left] at hpos'
        linarith [hpos']
      calc
      -- start with the raw inner product
        ⟪f₂ x, x₂⟫_ℝ = ⟪x₂ + (f₂ x - x₂), x₂⟫_ℝ := by simp
        _ = ⟪x₂, x₂⟫_ℝ + ⟪f₂ x - x₂, x₂⟫_ℝ := inner_add_left x₂ (f₂ x - x₂) x₂
        _ = ‖x₂‖^2 + ⟪f₂ x - x₂, x₂⟫_ℝ := by rw [hself]
        _ ≥ ‖x₂‖^2 - ‖f₂ x - x₂‖ * ‖x₂‖ := by
              -- Cauchy–Schwarz in WithLp 2 V
              linarith [hlow]
        _ > ‖x₂‖^2 - (‖x₂‖ / 2) * ‖x₂‖ := by
              -- subtract a strictly smaller term
              have hmul := mul_lt_mul_of_pos_left hclose (norm_pos_iff.mpr hx2)
              linarith [sub_lt_sub_left hmul (‖x₂‖^2)]
        _ = ‖x₂‖^2 / 2 := by ring
        _ > 0 := by positivity
  -- pull `inner_pos₂` back to V via `fromL2`:
    have inner_pos_V : ∀ x ∈ Metric.ball x₀ δ₂, 0 < ⟪f x, f x₀⟫_ℝ := by
      rintro x hx
      apply inner_pos₂ x hx
    -- now we have a genuine positive integrand on a set of positive measure.

  -- [3] `g` construction using bump function.
    have bump_exists : ∃ φ : Y → ℝ, IsTestFunction φ ∧ φ x₀ > 0 ∧
        (∀ x ∈ Function.support φ, 0 ≤ φ x) ∧
        Function.support φ ⊆ Metric.ball x₀ (δ₂/2) ∧
        (∀ x ∈ Metric.closedBall x₀ (δ₂/4), 0 < φ x) := by
        -- use `hasContDiffBump_of_innerProductSpace`, leveraging `[innerProductSpace Y]`
          haveI : HasContDiffBump Y := hasContDiffBump_of_innerProductSpace Y
          let rIn : ℝ := δ₂ / 4
          let rOut : ℝ := δ₂ / 2
          have h_rIn_pos : 0 < rIn := by
            dsimp [rIn]
            apply div_pos hδ₂_pos
            linarith
          have h_rIn_lt_rOut : rIn < rOut := by
              have : (1 : ℝ) / 4 < 1 / 2 := by norm_num
              simpa [rIn, rOut] using mul_lt_mul_of_pos_left this hδ₂_pos
          let φ1 : ContDiffBump x₀ := ⟨rIn, rOut, h_rIn_pos, h_rIn_lt_rOut⟩
          let φ : Y → ℝ := φ1.toFun
        -- Show the five required properties.
          use φ
          constructor
          · -- `ϕ` is a smooth function with compact support, i.e. a test function
            -- uses `ContDiffBump.hasCompactSupport` from `Analysis.Calculus.BumpFunction.Basic`,
            -- which needs `[FiniteDimensional ℝ Y]`.
            exact ⟨ContDiffBump.contDiff φ1, ContDiffBump.hasCompactSupport φ1⟩
          constructor
          · exact φ1.pos_of_mem_ball (Metric.mem_ball_self φ1.rOut_pos)
          constructor
          · -- ∀ x ∈ Function.support φ, 0 ≤ φ x
            intros x hx
            exact φ1.nonneg
          constructor
          · rw [ContDiffBump.support_eq]
          · intros x hx
            have h_in_support : x ∈ Metric.ball x₀ φ1.rOut := by
              rw [Metric.mem_ball]
              calc dist x x₀ ≤ δ₂ / 4 := by rwa [Metric.mem_closedBall] at hx
                              _ = rIn := by simp [rIn]
                              _ < rOut := h_rIn_lt_rOut
                              _ = φ1.rOut := by
                                congr 1
            exact φ1.pos_of_mem_ball h_in_support
    obtain ⟨φ, hφ_testfun, hφ_pos_x₀, hφ_non_neg, hφ_support_subset, hφ_pos_inner⟩ :=
      bump_exists
  -- Define test function g(x) = φ(x) * f(x₀)
    let g : Y → V := fun x => φ x • f x₀
  -- Show that g is a test function
    have hg_test : IsTestFunction g := by
    -- Use the smul_right lemma, noting: `φ` is a test function and `f x₀` is smooth (constant)
      apply IsTestFunction.smul_right hφ_testfun
      exact contDiff_const

  -- [4] Derive contradiction. First compute the integral ∫ ⟪f x, g x⟫
  -- [4.1] ∫ φ x * ⟪f x, f x₀⟫ = 0
    have key_integral := hg g hg_test
    simp [g] at key_integral
  -- We have ∫ ⟪f x, φ x • f x₀⟫ = ∫ φ x * ⟪f x, f x₀⟫ = 0
  -- This follows from linearity of inner product in the second argument
    have integral_rewrite : ∫ x, ⟪f x, φ x • f x₀⟫_ℝ ∂μ = ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ := by
      congr 1
      ext x
      have : ⟪f x, φ x • f x₀⟫_ℝ = φ x * ⟪f x, f x₀⟫_ℝ := by
        apply inner_smul_right' (f x) (f x₀) (φ x)
      exact this
    rw [integral_rewrite] at key_integral

  -- [4.2] 0 < ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ. Sketch: on the support of φ (which is contained in
  -- B(x₀, δ/2) ⊆ B(x₀, δ)), we have ⟪f x, f x₀⟫ > ‖f x₀‖²/2 > 0 by our choice of δ.
  -- Since φ is nonnegative on its support and positive somewhere, this gives the contradiction.

  -- [4.2.1] Integrability of the integrand: `integrable_prod` .
    have support_subset : Function.support φ ⊆ Metric.ball x₀ δ₂ := by
      trans Metric.ball x₀ (δ₂/2)
      · exact hφ_support_subset
      · exact Metric.ball_subset_ball (by linarith)
    have supp_subset2 : Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) ⊆ Function.support φ := by
      intro x hprod hφ0
    -- if φ x = 0 then φ x * inner = 0, contradiction
      simp [hφ0] at hprod
    have hinner_cont : Continuous (fun x => ⟪f x, f x₀⟫_ℝ) :=
      Continuous.inner' (f : Y → V) (fun _ => f x₀) hf continuous_const
    have integrable_prod :
      Integrable (fun x => φ x * ⟪f x, f x₀⟫_ℝ) μ :=
    -- (i) build a `HasCompactSupport` witness for the product
      (Continuous.mul hφ_testfun.smooth.continuous hinner_cont).integrable_of_hasCompactSupport
        (hφ_testfun.supp.mono supp_subset2)

  -- [4.2.2] Nonnegativity everywhere (`h_nonneg`)
    have hφ_zero_outside : ∀ x, x ∉ Function.support φ → φ x = 0 := by
      intro xs hx
      exact Function.notMem_support.mp hx
    have h_nonneg : ∀ x, 0 ≤ φ x * ⟪f x, f x₀⟫_ℝ := by
      intro x
      by_cases hx : x ∈ Function.support φ
      · -- on the support, φ ≥ 0 and ⟪f x, f x₀⟫ > 0
        have hφx : 0 ≤ φ x := hφ_non_neg x hx
        have hball : x ∈ Metric.ball x₀ δ₂ := by exact support_subset hx
        have hin : 0 < ⟪f x, f x₀⟫_ℝ := inner_pos_V x hball
        exact mul_nonneg hφx hin.le
      · -- off the support, φ x = 0 so the product is 0
        apply hφ_zero_outside at hx
        rw [hx]
        linarith

  -- [4.2.3] That closed ball has positive measure, and is contained in the support
    have hμ_ball : 0 < μ (Metric.ball x₀ (δ₂/4)) := by
    -- Use the fact that every nonempty open set has positive measure
      apply IsOpen.measure_pos
      exact Metric.isOpen_ball
      refine Metric.nonempty_ball.mpr ?_
      linarith
    have hμ : 0 < μ (Metric.closedBall x₀ (δ₂/4)) := by
      calc μ (Metric.closedBall x₀ (δ₂/4))
        _ ≥ μ (Metric.ball x₀ (δ₂/4)) := measure_mono Metric.ball_subset_closedBall
        _ > 0 := hμ_ball
    have closedBall_subset_support :
        Metric.closedBall x₀ (δ₂/4)
          ⊆ Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) := by
        intro x hx
        have hφx := hφ_pos_inner x hx
        have hin : 0 < ⟪f x, f x₀⟫_ℝ :=
          inner_pos_V x (Metric.closedBall_subset_ball (by linarith) hx)
        simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq]
        constructor
        linarith; linarith

  -- [4.2.4] putting everything together
    have integral_pos : 0 < ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ := by
      refine (integral_pos_iff_support_of_nonneg h_nonneg ?_).mpr ?_
      · exact integrable_prod -- Goal 1: Integrable (fun i => φ i * ⟪f i, f x₀⟫_ℝ) μ
      · calc -- Goal 2: 0 < μ (Function.support fun i => φ i * ⟪f i, f x₀⟫_ℝ)
        0 < μ (Metric.closedBall x₀ (δ₂/4)) := hμ
        _ ≤ μ (Function.support fun x => φ x * ⟪f x, f x₀⟫_ℝ) :=
          measure_mono closedBall_subset_support
    linarith

/- A version of `fundamental_theorem_of_variational_calculus` for test functions `f`.
Source/domain `X` of `f` is not assumed to be a finite-dimensional space, and
`hf` gives compact support for `f`.
-/

lemma fundamental_theorem_of_variational_calculus {f : X → V}
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace X]
    (hf : IsTestFunction f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0 := by
  have hf' := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hf'
  · rw [Continuous.ae_eq_iff_eq] at hf'
    · funext x
      have hf'' := congrFun hf' x
      simpa using hf''
    · have hf : Continuous f := hf.smooth.continuous
      fun_prop
    · fun_prop
  · intro x
    simp only [Pi.zero_apply]
    apply real_inner_self_nonneg'
  · apply IsTestFunction.integrable
    exact IsTestFunction.inner hf hf
