/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.LaplaceAnalytic
import QuantumInfo.StatMech.Hamiltonian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder

noncomputable section
namespace MicroHamiltonian

variable {D : Type} (H : MicroHamiltonian D) (d : D)

/-- The partition function corresponding to a given MicroHamiltonian. This is a function taking a thermodynamic β, not a temperature.
It also depends on the data D defining the system extrinsincs.

 * Ideally this would be an NNReal, but ∫ (NNReal) doesn't work right now, so it would just be a separate proof anyway
-/
def PartitionZ (β : ℝ) : ℝ :=
  ∫ (config : H.dim d → ℝ),
    let E := H.H config
    if h : E = ⊤ then 0 else Real.exp (-β * (E.untop h))

/-- The partition function as a function of temperature T instead of β. -/
def PartitionZT (T : ℝ) : ℝ :=
  PartitionZ H d (1/T)

/-- The Internal Energy, U or E, defined as -∂(ln Z)/∂β. Parameterized here with β. -/
def InternalU (β : ℝ) : ℝ :=
  -deriv (fun β' ↦ (PartitionZ H d β').log) β

/-- The Helmholtz Free Energy, -T * ln Z. Also denoted F. Parameterized here with temperature T, not β. -/
def HelmholtzA (T : ℝ) : ℝ :=
  -T * (PartitionZT H d T).log

/-- The entropy, defined as the -∂A/∂T. Function of T. -/
def EntropyS (T : ℝ) : ℝ :=
  -deriv (HelmholtzA H d) T

/-- The entropy, defined as ln Z + β*U. Function of β. -/
def EntropySβ (β : ℝ) : ℝ :=
  (PartitionZ H d β).log + β * InternalU H d β

/-- To be able to compute or define anything from a Hamiltonian, we need its partition function to be
a computable integral. A Hamiltonian is ZIntegrable at β if PartitionZ is Lesbegue integrable and nonzero.
-/
def ZIntegrable (β : ℝ) : Prop :=
  MeasureTheory.Integrable (fun (config : H.dim d → ℝ) ↦
    let E := H.H config;
    if h : E = ⊤ then 0 else Real.exp (-β * (E.untop h))
  ) ∧ (H.PartitionZ d β ≠ 0)

/--
This Prop defines the most common case of ZIntegrable, that it is integrable at all finite temperatures
(aka all positive β).
-/
def PositiveβIntegrable : Prop :=
  ∀ β > 0, H.ZIntegrable d β

/-- `H` is locally Z-integrable at `β` when it is `ZIntegrable` at every `β'` in a neighborhood of
`β`.

This, and not bare `ZIntegrable` at `β`, is the hypothesis that makes the partition function
differentiable at `β`: the defining integral can converge at `β` and diverge on one side of it, and
then `Z` drops discontinuously to zero there. For instance on a one-dimensional configuration space,
with `H x = ⊤` for `x ≤ e` and `H x = log x + 2 log log x` above, the integrand at `β` is
`x ^ (-β) * (log x) ^ (-2β)`, which is integrable exactly when `β ≥ 1`.
-/
def LocallyZIntegrable (β : ℝ) : Prop :=
  ∀ᶠ β' in nhds β, H.ZIntegrable d β'

variable {H d}

theorem LocallyZIntegrable.zIntegrable {β : ℝ} (h : H.LocallyZIntegrable d β) :
    H.ZIntegrable d β :=
  h.self_of_nhds

theorem PositiveβIntegrable.locallyZIntegrable (h : H.PositiveβIntegrable d) {β : ℝ} (hβ : 0 < β) :
    H.LocallyZIntegrable d β :=
  (eventually_gt_nhds hβ).mono fun _ hb ↦ h _ hb

open MeasureTheory in
/-- The integrand of the partition function, `exp (-β E)`, agrees almost everywhere with
`exp (-β w)` restricted to a measurable set, for a single measurable `w` and set `s` working
simultaneously for every `β`.

This is what replaces "the energy `H.H` is measurable", which the definition of `MicroHamiltonian`
does not require: integrability at one nonzero `β₁` is enough, because the energy can be recovered
from the integrand there as `-log (exp (-β₁ E)) / β₁`. -/
theorem exists_measurable_repr_of_integrable {β₁ : ℝ} (hβ₁ : β₁ ≠ 0)
    (hint : Integrable (fun config : H.dim d → ℝ ↦
      let E := H.H config
      if h : E = ⊤ then 0 else Real.exp (-β₁ * (E.untop h)))) :
    ∃ (s : Set (H.dim d → ℝ)) (w : (H.dim d → ℝ) → ℝ), MeasurableSet s ∧ Measurable w ∧
      ∀ b : ℝ, (fun config : H.dim d → ℝ ↦
        let E := H.H config
        if h : E = ⊤ then 0 else Real.exp (-b * (E.untop h)))
          =ᵐ[volume] s.indicator (fun x ↦ Real.exp (-b * w x)) := by
  obtain ⟨g, hgsm, hgae⟩ := hint.aestronglyMeasurable
  have hgm : Measurable g := hgsm.measurable
  refine ⟨{x | g x ≠ 0}, fun x ↦ -Real.log (g x) / β₁, ?_, by fun_prop, ?_⟩
  · exact (hgm (measurableSet_singleton 0)).compl
  · intro b
    filter_upwards [hgae] with x hx
    simp only at hx ⊢
    by_cases hE : H.H x = ⊤
    · have hgx : g x = 0 := by rw [← hx]; simp [hE]
      simp [hE, hgx]
    · have hgx : g x = Real.exp (-β₁ * ((H.H x).untop hE)) := by rw [← hx]; simp [hE]
      have hne : g x ≠ 0 := by rw [hgx]; exact (Real.exp_pos _).ne'
      have hw : -Real.log (g x) / β₁ = ((H.H x).untop hE) := by
        rw [hgx, Real.log_exp]
        field_simp
      rw [Set.indicator_of_mem hne, dif_neg hE, hw]

/-
The partition function Z is the Laplace transform of the density of states: letting μ⁻(H,E) be the
measure of {x | H(x) ≤ E}, for nonzero β,
∫ exp(-βH) dμ =
∫ (1/β * ∫_H..∞ exp(-βE) dE) dμ =
∫ (1/β * ∫_-∞..∞ exp(-βE) χ(E ≤ H) dE) dμ =
1/β * ∫ (∫ exp(-βE) χ(E ≤ H) dμ) dE =
1/β * ∫ exp(-βE) * μ⁻(H,E) dE.
See e.g. https://math.stackexchange.com/q/84382/127777. So Z is analytic wherever the transform
converges absolutely on a neighborhood; that is `analyticAt_integral_rexp_neg_mul`, proved by
differentiating under the integral sign in a complex strip.
-/
open MeasureTheory in
open scoped ContDiff in
theorem DifferentiableAt_Z_if_ZIntegrable {β : ℝ} (h : H.LocallyZIntegrable d β) :
    ContDiffAt ℝ ω (H.PartitionZ d) β := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  obtain ⟨δ, hδ0, hδε, hβδ⟩ : ∃ δ, 0 < δ ∧ δ < ε ∧ β + δ ≠ 0 := by
    rcases eq_or_ne (β + ε / 2) 0 with hb | hb
    · exact ⟨ε / 4, by linarith, by linarith, fun hc ↦ by linarith⟩
    · exact ⟨ε / 2, by linarith, by linarith, hb⟩
  have hdist : ∀ σ : ℝ, |σ| = δ → dist (β + σ) β < ε := by
    intro σ hσ
    rw [Real.dist_eq, add_sub_cancel_left, hσ]
    exact hδε
  have hp : H.ZIntegrable d (β + δ) := hball (hdist δ (abs_of_pos hδ0))
  have hm : H.ZIntegrable d (β - δ) := by
    have := hball (hdist (-δ) (by rw [abs_neg, abs_of_pos hδ0]))
    rwa [← sub_eq_add_neg] at this
  obtain ⟨s, w, hs, hw, hrep⟩ := exists_measurable_repr_of_integrable hβδ hp.1
  have hZ : ∀ b : ℝ, H.PartitionZ d b = ∫ x in s, Real.exp (-b * w x) := fun b ↦ by
    rw [PartitionZ, integral_congr_ae (hrep b), integral_indicator hs]
  have hrestrict : ∀ b : ℝ, H.ZIntegrable d b →
      Integrable (fun x ↦ Real.exp (-b * w x)) (volume.restrict s) := by
    intro b hb
    have := hb.1
    rw [integrable_congr (hrep b)] at this
    exact (integrable_indicator_iff hs).mp this
  have hana : AnalyticAt ℝ (fun b : ℝ ↦ ∫ x in s, Real.exp (-b * w x)) β :=
    analyticAt_integral_rexp_neg_mul hw.aemeasurable hδ0 (hrestrict _ hm) (hrestrict _ hp)
  exact ((analyticAt_congr (Filter.Eventually.of_forall hZ)).mpr hana).contDiffAt

/-- The two definitions of entropy, in terms of T or β, are equivalent. -/
theorem entropy_A_eq_entropy_Z (T β : ℝ) (hβT : T * β = 1) (hi : H.LocallyZIntegrable d β)
    : EntropyS H d T = EntropySβ H d β := by
  have hTnz : T ≠ 0 := left_ne_zero_of_mul_eq_one hβT
  have hβnz : β ≠ 0 := right_ne_zero_of_mul_eq_one hβT
  have hβT' := eq_one_div_of_mul_eq_one_right hβT
  dsimp [EntropyS, EntropySβ, InternalU, PartitionZT]
  unfold HelmholtzA
  erw [deriv_mul]
  rw [deriv_neg'', neg_mul, one_mul, neg_add_rev, neg_neg, mul_neg, add_comm]
  congr 1
  · rw [PartitionZT, hβT']
  simp_rw [PartitionZT]
  have hdc := deriv_comp (h := fun T ↦ T⁻¹) (h₂ := fun β => Real.log (H.PartitionZ d β)) T ?_ ?_
  unfold Function.comp at hdc
  simp only [hdc, one_div, deriv_inv', mul_neg, neg_inj, hβT']
  field_simp
  ring_nf
  --Show the differentiability side-goals
  · rw [← one_div, ← hβT']
    have h₁ := hi.zIntegrable.2
    have := (DifferentiableAt_Z_if_ZIntegrable hi).differentiableAt WithTop.top_ne_zero
    fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · fun_prop
  · simp_rw [PartitionZT]
    rw [hβT'] at hi
    have := hi.zIntegrable.2
    have := (DifferentiableAt_Z_if_ZIntegrable hi).differentiableAt WithTop.top_ne_zero
    fun_prop (disch := assumption)

/--
The "definition of temperature from entropy":
1/T = (∂S/∂U), when the derivative is at constant extrinsic d (typically N/V).
Here we use β instead of 1/T on the left, and express the right actually as (∂S/∂β)/(∂U/∂β),
as all our things are ultimately parameterized by β.

The hypothesis `hU` says that the internal energy actually responds to a change in β; equivalently,
that the energy has nonzero variance. Without it the right-hand side is a division by zero, and
temperature is not determined by the entropy-energy relation.
-/
theorem β_eq_deriv_S_U {β : ℝ} (hi : H.LocallyZIntegrable d β)
    (hU : deriv (H.InternalU d) β ≠ 0) :
    β = (deriv (H.EntropySβ d) β) / deriv (H.InternalU d) β := by
  have hU' : deriv (deriv fun β ↦ Real.log (H.PartitionZ d β)) β ≠ 0 := by
    intro hzero
    refine hU ?_
    show deriv (-deriv fun β'' ↦ Real.log (H.PartitionZ d β'')) β = 0
    rw [deriv.neg, hzero, neg_zero]
  unfold EntropySβ
  unfold InternalU

  --Show the differentiability side-goals
  have : DifferentiableAt ℝ (fun β => Real.log (H.PartitionZ d β)) β := by
    have := hi.zIntegrable.2
    have := (DifferentiableAt_Z_if_ZIntegrable hi).differentiableAt WithTop.top_ne_zero
    fun_prop (disch := assumption)
  have : DifferentiableAt ℝ (deriv fun β => Real.log (H.PartitionZ d β)) β := by
    have this := (DifferentiableAt_Z_if_ZIntegrable hi).log hi.zIntegrable.2
    replace this :=
      (this.fderiv_right (m := ⊤) (OrderTop.le_top _)).differentiableAt WithTop.top_ne_zero
    unfold deriv
    fun_prop

  --Main goal
  simp only [mul_neg]
  erw [deriv.neg', deriv_add, deriv.neg']
  dsimp
  erw [deriv_mul]
  simp only [deriv_id'', one_mul, neg_add_rev, add_neg_cancel_comm_assoc, neg_div_neg_eq]
  exact (mul_div_cancel_right₀ β hU').symm
  --Discharge those side-goals
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)

open scoped ContDiff in
example (x : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ ω f x) : DifferentiableAt ℝ (deriv f) x := by
  have := (hf.fderiv_right (m := ⊤) (OrderTop.le_top _)).differentiableAt WithTop.top_ne_zero
  unfold deriv
  fun_prop

end MicroHamiltonian

--! Specializing to a system of particles in space

namespace NVEHamiltonian
open MicroHamiltonian

variable (H : NVEHamiltonian) (d : ℕ × ℝ)

/-- Pressure, as a function of T. Defined as the conjugate variable to volume. -/
def Pressure (T : ℝ) : ℝ :=
  let (n, V) := d;
  -deriv (fun V' ↦ HelmholtzA H (n, V') T) V

end NVEHamiltonian
