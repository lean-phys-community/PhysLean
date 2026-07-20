/-
Copyright (c) 2025 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

noncomputable section

/-- The integrand of the complex Laplace transform of a possibly infinite-valued energy function. -/
def ComplexLaplaceIntegrand {α : Type*} (E : α → WithTop ℝ) (z : ℂ) (x : α) : ℂ :=
  if h : E x = ⊤ then 0 else Complex.exp (-z * (E x).untop h : ℂ)

/-- The complex Laplace transform of a possibly infinite-valued energy function. -/
def ComplexLaplaceTransform {α : Type*} [MeasureTheory.MeasureSpace α]
    (E : α → WithTop ℝ) (z : ℂ) : ℂ :=
  ∫ x, ComplexLaplaceIntegrand E z x

/-- The complex convergence domain of a Laplace transform. -/
def ComplexLaplaceConvergenceDomain {α : Type*} [MeasureTheory.MeasureSpace α]
    (E : α → WithTop ℝ) : Set ℂ :=
  {z | MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E z)}

/-- A two-sided exponential envelope controlling the Laplace integrand near `z`. -/
private def ComplexLaplaceEnvelope {α : Type*} (E : α → WithTop ℝ) (z : ℂ) (δ : ℝ)
    (x : α) : ℝ :=
  ‖ComplexLaplaceIntegrand E (z - (δ : ℂ)) x‖ +
    ‖ComplexLaplaceIntegrand E (z + (δ : ℂ)) x‖

private def ComplexLaplaceEndpointEnvelope {α : Type*} (E : α → WithTop ℝ) (z w : ℂ)
    (x : α) : ℝ :=
  ‖ComplexLaplaceIntegrand E z x‖ + ‖ComplexLaplaceIntegrand E w x‖

private theorem norm_complexLaplaceIntegrand_le_envelope
    {α : Type*} {E : α → WithTop ℝ} {z w : ℂ} {δ : ℝ}
    (hw : w ∈ Metric.closedBall z δ) (x : α) :
    ‖ComplexLaplaceIntegrand E w x‖ ≤ ComplexLaplaceEnvelope E z δ x := by
  unfold ComplexLaplaceEnvelope ComplexLaplaceIntegrand
  by_cases h : E x = ⊤
  · simp [h]
  have hre : |w.re - z.re| ≤ δ := by
    simpa [Complex.sub_re] using (Complex.abs_re_le_norm (w - z)).trans
      (by rwa [Metric.mem_closedBall, dist_eq_norm] at hw)
  simp only [h, dite_false, Complex.norm_exp, neg_mul, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re, Complex.add_re]
  rcases le_total 0 ((E x).untop h) with he | he
  · exact le_add_of_le_of_nonneg
      (Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hre).1])) (Real.exp_pos _).le
  · exact le_add_of_nonneg_of_le (Real.exp_pos _).le
      (Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hre).2]))

private theorem norm_complexLaplaceIntegrand_horizontal_le_endpointEnvelope
    {α : Type*} {E : α → WithTop ℝ} {a b : ℂ} {t : ℝ}
    (ht : t ∈ Set.uIcc a.re b.re) (x : α) :
    ‖ComplexLaplaceIntegrand E (t + a.im * Complex.I) x‖ ≤
      ComplexLaplaceEndpointEnvelope E a (b.re + a.im * Complex.I) x := by
  unfold ComplexLaplaceEndpointEnvelope ComplexLaplaceIntegrand
  by_cases h : E x = ⊤
  · simp [h]
  simp only [h, dite_false, Complex.norm_exp, neg_mul, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.add_re, Complex.I_re]
  rcases Set.mem_uIcc.mp ht with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rcases le_total 0 ((E x).untop h) with he | he <;>
    first
      | exact le_add_of_le_of_nonneg
          (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
      | exact le_add_of_nonneg_of_le (Real.exp_pos _).le
          (Real.exp_le_exp.mpr (by nlinarith))

private theorem norm_complexLaplaceIntegrand_vertical_le_endpointEnvelope
    {α : Type*} {E : α → WithTop ℝ} {a b : ℂ} {t : ℝ}
    (x : α) :
    ‖ComplexLaplaceIntegrand E (b.re + t * Complex.I) x‖ ≤
      ComplexLaplaceEndpointEnvelope E b (b.re + a.im * Complex.I) x := by
  unfold ComplexLaplaceEndpointEnvelope ComplexLaplaceIntegrand
  by_cases h : E x = ⊤
  · simp [h]
  simp only [h, dite_false, Complex.norm_exp, neg_mul, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.add_re, Complex.I_re]
  exact le_add_of_le_of_nonneg le_rfl (Real.exp_pos _).le

/-- For each configuration, the complex Laplace integrand is analytic in the parameter. -/
theorem analyticAt_complexLaplaceIntegrand
    {α : Type*} (E : α → WithTop ℝ) (x : α) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ComplexLaplaceIntegrand E w x) z := by
  unfold ComplexLaplaceIntegrand
  split_ifs <;> fun_prop

theorem measurable_complexLaplaceIntegrand
    {α : Type*} [MeasurableSpace α] {E : α → WithTop ℝ} (hE : Measurable E) (z : ℂ) :
    Measurable (ComplexLaplaceIntegrand E z) := by
  rw [show ComplexLaplaceIntegrand E z =
      fun x => if E x = ⊤ then 0 else Complex.exp (-z * (((E x).untopD 0 : ℝ) : ℂ)) by
    funext x
    unfold ComplexLaplaceIntegrand
    split_ifs with hx
    · rfl
    · obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp hx
      simp [← he]]
  exact Measurable.ite (hE (measurableSet_singleton (⊤ : WithTop ℝ))) measurable_const
    (by fun_prop)

/-- Interior convergence gives integrability throughout a neighborhood of the parameter. -/
theorem eventually_integrable_complexLaplaceIntegrand_of_mem_interior_convergenceDomain
    {α : Type*} [MeasureTheory.MeasureSpace α] {E : α → WithTop ℝ} {z : ℂ}
    (hz : z ∈ interior (ComplexLaplaceConvergenceDomain E)) :
    ∀ᶠ w in nhds z,
      MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E w) :=
  Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hz) _root_.interior_subset

theorem continuousAt_complexLaplaceTransform_of_mem_interior_convergenceDomain
    {α : Type*} [MeasureTheory.MeasureSpace α] {E : α → WithTop ℝ} {z : ℂ}
    (hz : z ∈ interior (ComplexLaplaceConvergenceDomain E)) :
    ContinuousAt (ComplexLaplaceTransform E) z := by
  rcases Metric.isOpen_iff.mp isOpen_interior z hz with ⟨ε, hε_pos, hε⟩
  have hint {w : ℂ} (hw : w ∈ Metric.ball z ε) :
      MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E w) :=
    _root_.interior_subset (s := ComplexLaplaceConvergenceDomain E) (hε hw)
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (F := fun w x => ComplexLaplaceIntegrand E w x)
    (f := fun x => ComplexLaplaceIntegrand E z x)
    (ComplexLaplaceEnvelope E z (ε / 2))
    ((eventually_integrable_complexLaplaceIntegrand_of_mem_interior_convergenceDomain hz).mono
      fun _ hw => hw.aestronglyMeasurable) ?_ ?_
    (Filter.Eventually.of_forall fun x => (analyticAt_complexLaplaceIntegrand E x z).continuousAt)
  · filter_upwards [Metric.ball_mem_nhds z (by positivity : (0:ℝ) < ε / 2)] with w hw
    exact .of_forall fun x =>
      norm_complexLaplaceIntegrand_le_envelope (Metric.ball_subset_closedBall hw) x
  · refine (hint ?_).norm.add (hint ?_).norm <;>
      simp [Metric.mem_ball, dist_eq_norm, abs_of_pos hε_pos, half_lt_self_iff, hε_pos]

theorem continuousOn_complexLaplaceTransform_interior_convergenceDomain
    {α : Type*} [MeasureTheory.MeasureSpace α] {E : α → WithTop ℝ} :
    ContinuousOn (ComplexLaplaceTransform E) (interior (ComplexLaplaceConvergenceDomain E)) :=
  fun _ hz =>
    (continuousAt_complexLaplaceTransform_of_mem_interior_convergenceDomain hz).continuousWithinAt

private theorem integrable_uncurry_complexLaplaceIntegrand_horizontal
    {α : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)] {E : α → WithTop ℝ}
    {a b : ℂ}
    (hE : Measurable E)
    (ha : MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E a))
    (hb : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceIntegrand E (b.re + a.im * Complex.I))) :
    MeasureTheory.Integrable
      (Function.uncurry fun t : ℝ => fun x : α =>
        ComplexLaplaceIntegrand E (t + a.im * Complex.I) x)
      ((MeasureTheory.volume.restrict (Set.uIoc a.re b.re)).prod MeasureTheory.volume) := by
  let μI := MeasureTheory.volume.restrict (Set.uIoc a.re b.re)
  haveI : MeasureTheory.IsFiniteMeasure μI := ⟨by simp [μI, Set.uIoc]⟩
  have hsm : MeasureTheory.StronglyMeasurable (Function.uncurry fun t : ℝ => fun x : α =>
      ComplexLaplaceIntegrand E (t + a.im * Complex.I) x) :=
    MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun x => (continuous_iff_continuousAt.2 fun w =>
        (analyticAt_complexLaplaceIntegrand E x w).continuousAt).comp (by fun_prop))
      fun t => (measurable_complexLaplaceIntegrand hE (t + a.im * Complex.I)).stronglyMeasurable
  refine ((ha.norm.add hb.norm).comp_snd μI).mono' hsm.aestronglyMeasurable ?_
  have h1 : ∀ᵐ p : ℝ × α ∂(MeasureTheory.volume.restrict (Set.uIoc a.re b.re)).prod
      MeasureTheory.volume, p.1 ∈ Set.uIoc a.re b.re := by
    rw [MeasureTheory.Measure.restrict_prod_eq_prod_univ]
    exact (MeasureTheory.ae_restrict_mem (measurableSet_uIoc.prod .univ)).mono fun _ hp => hp.1
  filter_upwards [h1] with p hp
  exact norm_complexLaplaceIntegrand_horizontal_le_endpointEnvelope (Set.uIoc_subset_uIcc hp) p.2

private theorem integrable_uncurry_complexLaplaceIntegrand_vertical
    {α : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)] {E : α → WithTop ℝ}
    {a b : ℂ}
    (hE : Measurable E)
    (hb : MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E b))
    (hba : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceIntegrand E (b.re + a.im * Complex.I))) :
    MeasureTheory.Integrable
      (Function.uncurry fun t : ℝ => fun x : α =>
        ComplexLaplaceIntegrand E (b.re + t * Complex.I) x)
      ((MeasureTheory.volume.restrict (Set.uIoc a.im b.im)).prod MeasureTheory.volume) := by
  let μI := MeasureTheory.volume.restrict (Set.uIoc a.im b.im)
  haveI : MeasureTheory.IsFiniteMeasure μI := ⟨by simp [μI, Set.uIoc]⟩
  have hsm : MeasureTheory.StronglyMeasurable (Function.uncurry fun t : ℝ => fun x : α =>
      ComplexLaplaceIntegrand E (b.re + t * Complex.I) x) :=
    MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun x => (continuous_iff_continuousAt.2 fun w =>
        (analyticAt_complexLaplaceIntegrand E x w).continuousAt).comp (by fun_prop))
      fun t => (measurable_complexLaplaceIntegrand hE (b.re + t * Complex.I)).stronglyMeasurable
  exact ((hb.norm.add hba.norm).comp_snd μI).mono' hsm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p =>
      norm_complexLaplaceIntegrand_vertical_le_endpointEnvelope (a := a) (b := b) (t := p.1) p.2)

private theorem wedgeIntegral_complexLaplaceTransform_eq_integral
    {α : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)] {E : α → WithTop ℝ}
    {a b : ℂ}
    (hE : Measurable E)
    (hab : Complex.Rectangle a b ⊆ interior (ComplexLaplaceConvergenceDomain E)) :
    Complex.wedgeIntegral a b (ComplexLaplaceTransform E) =
      ∫ x, Complex.wedgeIntegral a b (fun w : ℂ => ComplexLaplaceIntegrand E w x) := by
  have hint {z : ℂ} (hz : z ∈ Complex.Rectangle a b) :
      MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E z) :=
    _root_.interior_subset (s := ComplexLaplaceConvergenceDomain E) (hab hz)
  have ha : MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E a) :=
    hint (by simp [Complex.Rectangle, Complex.mem_reProdIm])
  have hb : MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E b) :=
    hint (by simp [Complex.Rectangle, Complex.mem_reProdIm])
  have hcorner : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceIntegrand E (b.re + a.im * Complex.I)) :=
    hint (by simp [Complex.Rectangle, Complex.mem_reProdIm])
  have hH := MeasureTheory.intervalIntegral_integral_swap
    (integrable_uncurry_complexLaplaceIntegrand_horizontal hE ha hcorner)
  have hV := MeasureTheory.intervalIntegral_integral_swap
    (integrable_uncurry_complexLaplaceIntegrand_vertical hE hb hcorner)
  simp only [Complex.wedgeIntegral, ComplexLaplaceTransform]
  rw [hH, hV, ← MeasureTheory.integral_smul, ← MeasureTheory.integral_add]
  · have hi := (integrable_uncurry_complexLaplaceIntegrand_horizontal
      hE ha hcorner).integral_prod_right
    rcases le_total a.re b.re with hab | hba
    · simpa [intervalIntegral.integral_of_le hab, Function.uncurry, Set.uIoc_of_le hab] using hi
    · simpa [intervalIntegral.integral_of_ge hba, Function.uncurry, Set.uIoc_of_ge hba] using hi.neg
  · refine (?_ : MeasureTheory.Integrable _ MeasureTheory.volume).smul Complex.I
    have hi := (integrable_uncurry_complexLaplaceIntegrand_vertical
      hE hb hcorner).integral_prod_right
    rcases le_total a.im b.im with hab | hba
    · simpa [intervalIntegral.integral_of_le hab, Function.uncurry, Set.uIoc_of_le hab] using hi
    · simpa [intervalIntegral.integral_of_ge hba, Function.uncurry, Set.uIoc_of_ge hba] using hi.neg

/-- A complex Laplace transform is analytic on the interior of its convergence domain. -/
theorem analyticAt_complexLaplaceTransform_of_mem_interior_convergenceDomain
    {α : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)] {E : α → WithTop ℝ} {z : ℂ}
    (hE : Measurable E)
    (hz : z ∈ interior (ComplexLaplaceConvergenceDomain E)) :
    AnalyticAt ℂ (ComplexLaplaceTransform E) z := by
  rcases Metric.isOpen_iff.mp isOpen_interior z hz with ⟨r, hr_pos, hr⟩
  have hcons : Complex.IsConservativeOn (ComplexLaplaceTransform E) (Metric.ball z r) := by
    intro a b hab
    rw [wedgeIntegral_complexLaplaceTransform_eq_integral hE (hab.trans hr),
      wedgeIntegral_complexLaplaceTransform_eq_integral hE (by
        simpa [Complex.Rectangle, Set.uIcc_comm] using hab.trans hr)]
    · rw [← MeasureTheory.integral_neg]
      exact MeasureTheory.integral_congr_ae (.of_forall fun x =>
        (DifferentiableOn.isConservativeOn fun y _ =>
          (analyticAt_complexLaplaceIntegrand E x y).differentiableAt.differentiableWithinAt)
          a b (Set.subset_univ _))
  exact ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn Metric.isOpen_ball).1
    ⟨hcons, continuousOn_complexLaplaceTransform_interior_convergenceDomain.mono hr⟩).analyticAt
      (Metric.ball_mem_nhds z hr_pos)


end
