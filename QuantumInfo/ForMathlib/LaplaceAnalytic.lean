/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Analyticity of Laplace-type integrals

The Laplace transform is analytic on the interior of its region of absolute convergence. Here we
prove the version we need: if `x ↦ exp (-b * w x)` is integrable for `b = β - δ` and for
`b = β + δ`, then `b ↦ ∫ exp (-b * w x)` is real-analytic at `β`.

The proof extends the parameter into the complex strip `|Re z - β| < δ/2`, where differentiation
under the integral sign applies with the dominating function
`|w x| * exp (-(Re z) * w x) ≤ 2/δ * (exp (-(β - δ) * w x) + exp (-(β + δ) * w x))`. Complex
differentiability on an open set gives complex analyticity, which restricts back to the reals.
-/

open MeasureTheory Metric Filter Topology

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `exp (-β t + δ |t|)` is bounded by the sum of the two "extreme" exponentials. -/
theorem rexp_abs_le_add (β δ t : ℝ) :
    Real.exp (-β * t + δ * |t|) ≤ Real.exp (-(β - δ) * t) + Real.exp (-(β + δ) * t) := by
  rcases abs_cases t with ⟨ht, -⟩ | ⟨ht, -⟩
  · rw [ht, show -β * t + δ * t = -(β - δ) * t by ring]
    linarith [Real.exp_pos (-(β + δ) * t)]
  · rw [ht, show -β * t + δ * -t = -(β + δ) * t by ring]
    linarith [Real.exp_pos (-(β - δ) * t)]

private theorem sub_mul_le {a β c : ℝ} (h : |a - β| ≤ c) (t : ℝ) : (β - a) * t ≤ c * |t| :=
  calc (β - a) * t ≤ |(β - a) * t| := le_abs_self _
    _ = |β - a| * |t| := abs_mul _ _
    _ ≤ c * |t| := mul_le_mul_of_nonneg_right (by rwa [abs_sub_comm]) (abs_nonneg t)

/-- On the strip `|a - β| ≤ δ`, the exponential `exp (-a t)` is dominated by the two exponentials at
the edges of the strip. -/
theorem rexp_le_add_of_abs_sub_le {a β δ : ℝ} (h : |a - β| ≤ δ) (t : ℝ) :
    Real.exp (-a * t) ≤ Real.exp (-(β - δ) * t) + Real.exp (-(β + δ) * t) := by
  refine le_trans (Real.exp_le_exp.mpr ?_) (rexp_abs_le_add β δ t)
  nlinarith [sub_mul_le h t]

/-- On the half-width strip `|a - β| ≤ δ/2`, even `|t| * exp (-a t)` — the size of the derivative in
`a` — is dominated by the two exponentials at the edges of the full strip. -/
theorem abs_mul_rexp_le_add {a β δ : ℝ} (hδ : 0 < δ) (h : |a - β| ≤ δ / 2) (t : ℝ) :
    |t| * Real.exp (-a * t) ≤
      2 / δ * (Real.exp (-(β - δ) * t) + Real.exp (-(β + δ) * t)) := by
  have habs : |t| ≤ 2 / δ * Real.exp (δ / 2 * |t|) := by
    have h1 : δ / 2 * |t| ≤ Real.exp (δ / 2 * |t|) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have h2 : 2 / δ * (δ / 2 * |t|) ≤ 2 / δ * Real.exp (δ / 2 * |t|) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 / δ * (δ / 2 * |t|) = |t| := by field_simp
    linarith
  have hexp : Real.exp (-a * t) ≤ Real.exp (-β * t + δ / 2 * |t|) :=
    Real.exp_le_exp.mpr (by nlinarith [sub_mul_le h t])
  calc |t| * Real.exp (-a * t)
      ≤ (2 / δ * Real.exp (δ / 2 * |t|)) * Real.exp (-β * t + δ / 2 * |t|) :=
        mul_le_mul habs hexp (Real.exp_pos _).le (by positivity)
    _ = 2 / δ * Real.exp (-β * t + δ * |t|) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ 2 / δ * (Real.exp (-(β - δ) * t) + Real.exp (-(β + δ) * t)) :=
        mul_le_mul_of_nonneg_left (rexp_abs_le_add β δ t) (by positivity)

open Complex in
/-- A Laplace-transform-type integral `b ↦ ∫ exp (-b * w x)` is real-analytic at `β`, provided the
integral converges absolutely at `β - δ` and at `β + δ` for some `δ > 0`. -/
theorem analyticAt_integral_rexp_neg_mul {w : α → ℝ} (hw : AEMeasurable w μ)
    {β δ : ℝ} (hδ : 0 < δ)
    (h₁ : Integrable (fun x ↦ Real.exp (-(β - δ) * w x)) μ)
    (h₂ : Integrable (fun x ↦ Real.exp (-(β + δ) * w x)) μ) :
    AnalyticAt ℝ (fun b : ℝ ↦ ∫ x, Real.exp (-b * w x) ∂μ) β := by
  set G : ℂ → α → ℂ := fun z x ↦ Complex.exp (-z * w x) with hGdef
  set G' : ℂ → α → ℂ := fun z x ↦ Complex.exp (-z * w x) * (-(w x : ℂ)) with hG'def
  have hnorm : ∀ z x, ‖G z x‖ = Real.exp (-z.re * w x) := by
    intro z x
    simp [hGdef, Complex.norm_exp]
  have hnorm' : ∀ z x, ‖G' z x‖ = |w x| * Real.exp (-z.re * w x) := by
    intro z x
    rw [hG'def]
    simp [Complex.norm_exp, mul_comm]
  have hwc : AEMeasurable (fun x ↦ ((w x : ℝ) : ℂ)) μ :=
    Complex.measurable_ofReal.comp_aemeasurable hw
  have hGmeas : ∀ z, AEStronglyMeasurable (G z) μ := fun z ↦
    (Complex.measurable_exp.comp_aemeasurable (hwc.const_mul (-z))).aestronglyMeasurable
  have hG'meas : ∀ z, AEStronglyMeasurable (G' z) μ := fun z ↦
    ((Complex.measurable_exp.comp_aemeasurable (hwc.const_mul (-z))).mul
      hwc.neg).aestronglyMeasurable
  set bnd : α → ℝ :=
    fun x ↦ 2 / δ * (Real.exp (-(β - δ) * w x) + Real.exp (-(β + δ) * w x)) with hbnddef
  have hbndint : Integrable bnd μ := (h₁.add h₂).const_mul _
  have hGint : ∀ z : ℂ, |z.re - β| ≤ δ → Integrable (G z) μ := by
    intro z hz
    refine Integrable.mono' (h₁.add h₂) (hGmeas z) (.of_forall fun x ↦ ?_)
    rw [hnorm]
    exact rexp_le_add_of_abs_sub_le hz _
  set U : Set ℂ := {z : ℂ | |z.re - β| < δ / 2} with hUdef
  have hUopen : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hbound : ∀ᵐ x ∂μ, ∀ z ∈ U, ‖G' z x‖ ≤ bnd x := by
    refine .of_forall fun x z hz ↦ ?_
    simp only [hnorm', hbnddef]
    exact abs_mul_rexp_le_add hδ (le_of_lt hz) _
  have hderiv : ∀ᵐ x ∂μ, ∀ z ∈ U, HasDerivAt (G · x) (G' z x) z := by
    refine .of_forall fun x z _ ↦ ?_
    simp only [hGdef, hG'def]
    exact ((by simpa using ((hasDerivAt_id z).neg.mul_const ((w x : ℝ) : ℂ)) :
      HasDerivAt (fun z : ℂ ↦ -z * (w x : ℂ)) (-(w x : ℂ)) z)).cexp
  have hdiff : DifferentiableOn ℂ (fun z ↦ ∫ x, G z x ∂μ) U := by
    intro z₀ hz₀
    refine DifferentiableAt.differentiableWithinAt ?_
    have hz₀' : |z₀.re - β| < δ / 2 := hz₀
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := G) (F' := G')
      (bound := bnd) (s := U) (hUopen.mem_nhds hz₀) (.of_forall fun z ↦ hGmeas z)
      (hGint z₀ (le_of_lt (hz₀'.trans (by linarith)))) (hG'meas z₀) hbound hbndint
      hderiv).2.differentiableAt
  have hZc : AnalyticAt ℂ (fun z ↦ ∫ x, G z x ∂μ) ((β : ℝ) : ℂ) := by
    refine hdiff.analyticOnNhd hUopen _ ?_
    simp [hUdef, hδ]
  have hre : ∀ b : ℝ, ∫ x, Real.exp (-b * w x) ∂μ = (∫ x, G (b : ℂ) x ∂μ).re := by
    intro b
    have hpt : ∀ x, G (b : ℂ) x = ((Real.exp (-b * w x) : ℝ) : ℂ) := by
      intro x
      simp only [hGdef, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_complex_ofReal]
    simp
  simp_rw [hre]
  exact (Complex.reCLM.analyticAt _).comp
    (hZc.restrictScalars.comp (Complex.ofRealCLM.analyticAt β))
