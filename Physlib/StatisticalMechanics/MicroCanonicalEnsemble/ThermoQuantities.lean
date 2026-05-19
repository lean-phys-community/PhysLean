/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic
public import Physlib.Meta.TODO.Basic
/-!

## The theormodynamical quantities of a microcanonical ensemble

-/
@[expose] public section

noncomputable section
namespace MicroHamiltonian

variable {D : Type} (H : MicroHamiltonian D) (d : D)

/-- The partition function corresponding to a given MicroHamiltonian. This is a function taking a
  thermodynamic β, not a temperature. It also depends on the data D defining the system extrinsincs.

 * Ideally this would be an NNReal, but ∫ (NNReal) doesn't work right now, so it would just be a
   separate proof anyway
-/
def partitionZ (β : ℝ) : ℝ :=
  ∫ (config : H.dim d → ℝ),
    let E := H.H config
    if h : E = ⊤ then 0 else Real.exp (-β * (E.untop h))

/-- The partition function as a function of temperature T instead of β. -/
def partitionZT (T : ℝ) : ℝ :=
  partitionZ H d (1/T)

/-- The Internal Energy, U or E, defined as -∂(ln Z)/∂β. Parameterized here with β. -/
def internalU (β : ℝ) : ℝ :=
  -deriv (fun β' ↦ (partitionZ H d β').log) β

/-- The Helmholtz Free Energy, -T * ln Z. Also denoted F. Parameterized here with temperature T, not
  β. -/
def helmholtzA (T : ℝ) : ℝ :=
  -T * (partitionZT H d T).log

/-- The entropy, defined as the -∂A/∂T. Function of T. -/
def entropyS (T : ℝ) : ℝ :=
  -deriv (helmholtzA H d) T

/-- The entropy, defined as ln Z + β*U. Function of β. -/
def entropySβ (β : ℝ) : ℝ :=
  (partitionZ H d β).log + β * internalU H d β

/-- To be able to compute or define anything from a Hamiltonian, we need its partition function to
  be a computable integral. A Hamiltonian is ZIntegrable at β if PartitionZ is Lesbegue integrable
  and nonzero.
-/
def ZIntegrable (β : ℝ) : Prop :=
  MeasureTheory.Integrable (fun (config : H.dim d → ℝ) ↦
    let E := H.H config;
    if h : E = ⊤ then 0 else Real.exp (-β * (E.untop h))
  ) ∧ (H.partitionZ d β ≠ 0)

/--
This Prop defines the most common case of ZIntegrable, that it is integrable at all finite
temperatures (aka all positive β).
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
For this we really want the fact that the Laplace transform is analytic wherever it's absolutely
convergent, which is (as Wikipedia informs) an easy consequence of Fubini's theorem + Morera's
theorem. Morera's theorem is now in Mathlib as `Complex.IsConservativeOn.isExactOn_ball` (in
HasPrimitives.lean), so this would be a good task:
 - Prove the analyticity of the Laplace transform
 - Use this to show that the partition function Z here is analytic (ContDiffAt ℝ ω)
-/

TODO "Show that the partition function for a microcanonical ensemble is analytic (ContDiffAt ℝ ω).
  Refer to the comments above this TODO item in the code for more details. See also #1077."

open scoped ContDiff in
@[sorryful]
lemma differentiableAt_Z_if_ZIntegrable {β : ℝ} (h : H.ZIntegrable d β) :
    ContDiffAt ℝ ω (H.partitionZ d) β := sorry

/-- The two definitions of entropy, in terms of T or β, are equivalent. -/
@[sorryful]
lemma entropy_A_eq_entropy_Z (T β : ℝ) (hβT : T * β = 1) (hi : H.ZIntegrable d β) :
    entropyS H d T = entropySβ H d β := by
  have hTnz : T ≠ 0 := left_ne_zero_of_mul_eq_one hβT
  have hβnz : β ≠ 0 := right_ne_zero_of_mul_eq_one hβT
  have hβT' := eq_one_div_of_mul_eq_one_right hβT
  dsimp [entropyS, entropySβ, internalU, partitionZT]
  unfold helmholtzA
  erw [deriv_mul]
  rw [deriv_neg'', neg_mul, one_mul, neg_add_rev, neg_neg, mul_neg, add_comm]
  congr 1
  · rw [partitionZT, hβT']
  simp_rw [partitionZT]
  have hdc := deriv_comp (h := fun T ↦ T⁻¹) (h₂ := fun β => Real.log (H.partitionZ d β)) T ?_ ?_
  unfold Function.comp at hdc
  simp only [hdc, one_div, deriv_inv', mul_neg, neg_inj, hβT']
  field_simp
  ring_nf
  --Show the differentiability side-goals
  · rw [← one_div, ← hβT']
    have h₁ := hi.2
    have := (differentiableAt_Z_if_ZIntegrable hi).differentiableAt WithTop.top_ne_zero
    fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · fun_prop
  · simp_rw [partitionZT]
    rw [hβT'] at hi
    have := hi.2
    have := (differentiableAt_Z_if_ZIntegrable hi).differentiableAt WithTop.top_ne_zero
    fun_prop (disch := assumption)

set_option backward.isDefEq.respectTransparency false in
/--
The "definition of temperature from entropy":
1/T = (∂S/∂U), when the derivative is at constant extrinsic d (typically N/V).
Here we use β instead of 1/T on the left, and express the right actually as (∂S/∂β)/(∂U/∂β),
as all our things are ultimately parameterized by β.
-/
@[sorryful]
lemma β_eq_deriv_S_U {β : ℝ} (hi : H.ZIntegrable d β) :
    β = (deriv (H.entropySβ d) β) / deriv (H.internalU d) β := by
  unfold entropySβ
  unfold internalU
  --Show the differentiability side-goals
  have : DifferentiableAt ℝ (fun β => Real.log (H.partitionZ d β)) β := by
    have := hi.2
    have := (differentiableAt_Z_if_ZIntegrable hi).differentiableAt WithTop.top_ne_zero
    fun_prop (disch := assumption)
  have : DifferentiableAt ℝ (deriv fun β => Real.log (H.partitionZ d β)) β := by
    have this := (differentiableAt_Z_if_ZIntegrable hi).log hi.2
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
  have : deriv (deriv fun β => Real.log (H.partitionZ d β)) β ≠ 0 := ?_
  exact (mul_div_cancel_right₀ β this).symm
  --Discharge those side-goals
  · sorry
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)

set_option backward.isDefEq.respectTransparency false in
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
def pressure (T : ℝ) : ℝ :=
  let (n, V) := d;
  - deriv (fun V' ↦ helmholtzA H (n, V') T) V

end NVEHamiltonian
