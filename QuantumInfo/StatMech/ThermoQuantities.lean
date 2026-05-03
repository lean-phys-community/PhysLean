/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.StatMech.Hamiltonian
public import QuantumInfo.ForMathlib.ComplexLaplaceTransform
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.L1
public import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

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

/-- The complexified partition function, viewed as a Laplace transform. -/
def PartitionZComplex (z : ℂ) : ℂ :=
  ComplexLaplaceTransform (fun config : H.dim d → ℝ => H.H config) z

/-- The complex convergence domain of the partition-function Laplace transform. -/
def ZComplexConvergenceDomain : Set ℂ :=
  ComplexLaplaceConvergenceDomain (fun config : H.dim d → ℝ => H.H config)

private theorem partitionZ_eq_re_partitionZComplex {β : ℝ}
    (hβ : (β : ℂ) ∈ H.ZComplexConvergenceDomain d) :
    H.PartitionZ d β = (H.PartitionZComplex d β).re := by
  have hInt : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceIntegrand (fun config : H.dim d → ℝ => H.H config) (β : ℂ)) := hβ
  rw [PartitionZ, PartitionZComplex, ComplexLaplaceTransform]
  calc
    (∫ (config : H.dim d → ℝ),
        have E := H.H config
        if h : E = ⊤ then 0 else Real.exp (-β * E.untop h)) =
        ∫ x, RCLike.re (ComplexLaplaceIntegrand
          (fun config : H.dim d → ℝ => H.H config) (β : ℂ) x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with config
      unfold ComplexLaplaceIntegrand
      by_cases h : H.H config = ⊤
      · simp [h]
      · simp only [h, dite_false]
        set e : ℝ := (H.H config).untop h
        simpa [Complex.ofReal_mul] using (Complex.exp_ofReal_re (-(β * e))).symm
    _ = RCLike.re (∫ x, ComplexLaplaceIntegrand
        (fun config : H.dim d → ℝ => H.H config) (β : ℂ) x) := integral_re hInt

open scoped ContDiff Topology in
theorem contDiffAt_partitionZ_of_mem_interior_convergenceDomain {β : ℝ}
    (hβ : (β : ℂ) ∈ interior (H.ZComplexConvergenceDomain d)) :
    ContDiffAt ℝ ⊤ (H.PartitionZ d) β := by
  refine (analyticAt_complexLaplaceTransform_of_mem_interior_convergenceDomain
    (E := fun config : H.dim d → ℝ => H.H config) (H.measurable_H d) hβ).contDiffAt
    |>.real_of_complex |>.congr_of_eventuallyEq ?_
  filter_upwards [(Complex.continuous_ofReal.tendsto β).eventually
    (IsOpen.mem_nhds isOpen_interior hβ)] with x hx
  exact H.partitionZ_eq_re_partitionZComplex d (_root_.interior_subset hx)

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

variable {H d}

/-
Need the fact that the partition function Z is differentiable. Assume it's integrable.
Letting μ⁻(H,E) be the measure of {x | H(x) ≤ E}, then for nonzero β,
∫_0..∞ exp(-βE) (dμ⁻/dE) dE =
∫ exp(-βH) dμ =
∫ (1/β * ∫_H..∞ exp(-βE) dE) dμ =
∫ (1/β * ∫_-∞..∞ exp(-βE) χ(E ≤ H) dE) dμ =
1/β * ∫ (∫ exp(-βE) χ(E ≤ H) dμ) dE =
1/β * ∫ exp(-βE) * μ⁻(H,E) dE

so this will be differentiable if
∫ exp(-βE) * μ⁻(H,E) dE
is, aka if the Laplace transform is differentiable.
See e.g. https://math.stackexchange.com/q/84382/127777
For this we really want the fact that the Laplace transform is analytic wherever it's absolutely convergent,
which follows from the local domination estimate above, Fubini's theorem, and Morera's theorem.
-/
/-- The two definitions of entropy, in terms of `T` or `β = 1 / T`, are equivalent. -/
theorem entropy_A_eq_entropy_Z (T : ℝ) (hT : T ≠ 0)
    (hZne : H.PartitionZ d (1 / T) ≠ 0)
    (hZint : ((1 / T : ℝ) : ℂ) ∈ interior (H.ZComplexConvergenceDomain d)) :
    EntropyS H d T = EntropySβ H d (1 / T) := by
  have hZdiff : DifferentiableAt ℝ (H.PartitionZ d) (1 / T) :=
    (H.contDiffAt_partitionZ_of_mem_interior_convergenceDomain d hZint).differentiableAt
      (by simp)
  dsimp [EntropyS, EntropySβ, InternalU, PartitionZT]
  unfold HelmholtzA
  erw [deriv_mul]
  rw [deriv_neg'', neg_mul, one_mul, neg_add_rev, neg_neg, mul_neg, add_comm]
  congr 1
  simp_rw [PartitionZT]
  have hdc := deriv_comp (h := fun T ↦ T⁻¹) (h₂ := fun β => Real.log (H.PartitionZ d β)) T ?_ ?_
  unfold Function.comp at hdc
  simp only [hdc, one_div, deriv_inv', mul_neg, neg_inj]
  field_simp
  ring_nf
  --Show the differentiability side-goals
  · rw [← one_div]
    fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · fun_prop
  · simp_rw [PartitionZT]
    fun_prop (disch := assumption)


set_option backward.isDefEq.respectTransparency false in
open scoped ContDiff in
/--
The "definition of temperature from entropy":
1/T = (∂S/∂U), when the derivative is at constant extrinsic d (typically N/V).
Here we use β instead of 1/T on the left, and express the right actually as (∂S/∂β)/(∂U/∂β),
as all our things are ultimately parameterized by β.

This identity requires the denominator `∂U/∂β` to be nonzero.
-/
theorem β_eq_deriv_S_U {β : ℝ}
    (hZne : H.PartitionZ d β ≠ 0)
    (hZint : (β : ℂ) ∈ interior (H.ZComplexConvergenceDomain d))
    (hU' : deriv (H.InternalU d) β ≠ 0) :
    β = (deriv (H.EntropySβ d) β) / deriv (H.InternalU d) β := by
  have hZ : ContDiffAt ℝ ⊤ (H.PartitionZ d) β :=
    H.contDiffAt_partitionZ_of_mem_interior_convergenceDomain d hZint
  unfold EntropySβ
  unfold InternalU

  --Show the differentiability side-goals
  have hlogDiff : DifferentiableAt ℝ (fun β => Real.log (H.PartitionZ d β)) β := by
    have := hZne
    have := hZ.differentiableAt (by simp)
    fun_prop (disch := assumption)
  have hlogDerivDiff : DifferentiableAt ℝ (deriv fun β => Real.log (H.PartitionZ d β)) β := by
    have this := hZ.log hZne
    replace this :=
      (this.fderiv_right (m := ⊤) (OrderTop.le_top _)).differentiableAt (by simp)
    unfold deriv
    fun_prop
  have hderiv : deriv (deriv fun β => Real.log (H.PartitionZ d β)) β ≠ 0 := by
    intro hzero
    apply hU'
    change deriv (-fun β => deriv (fun β' => Real.log (H.PartitionZ d β')) β) β = 0
    rw [deriv.neg]
    simp [hzero]

  --Main goal
  simp only [mul_neg]
  erw [deriv.neg', deriv_add, deriv.neg']
  dsimp
  erw [deriv_mul]
  simp only [deriv_id'', one_mul, neg_add_rev, add_neg_cancel_comm_assoc, neg_div_neg_eq]
  exact (mul_div_cancel_right₀ β hderiv).symm
  --Discharge those side-goals
  · exact differentiableAt_id
  · exact hlogDerivDiff
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)

set_option backward.isDefEq.respectTransparency false in
open scoped ContDiff in
example (x : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ ⊤ f x) : DifferentiableAt ℝ (deriv f) x := by
  have := (hf.fderiv_right (m := ⊤) (OrderTop.le_top _)).differentiableAt (by simp)
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
