/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.StatisticalMechanics.CanonicalEnsemble.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
/-!
# Canonical Ensemble: Thermodynamic Identities and Relations

This file develops relations between the *mathematical* objects defined in
`Basic.lean` and the *physical* thermodynamic quantities, together with
calculus identities for the canonical ensemble.

## Contents Overview

1. Helmholtz Free Energies
  * `mathematicalHelmholtzFreeEnergy`
  * Relation to physical `helmholtzFreeEnergy` with semi–classical correction.

2. Entropy Relations
  * Pointwise logarithm of (mathematical / physical) Boltzmann probabilities.
  * Key identity:
      `differentialEntropy = kB * β * meanEnergy + kB * log Z_math`
  * Fundamental link:
      `thermodynamicEntropy = differentialEntropy - kB * dof * log h`
    (semi–classical correction term).
  * Specializations removing the correction when `dof = 0` or `phaseSpaceUnit = 1`.

3. Fundamental Thermodynamic Identity
  * Proof of `F = U - T S_thermo`.
  * Equivalent rearrangements giving entropy from energies and free energy.
  * Discrete / normalized specialization (no correction).

4. Mean energy as
      `U = - d/dβ log Z_math`
      and likewise with the physical partition function (constant factor cancels).

## Design Notes

* All derivative statements are given as `derivWithin` on `Set.Ioi 0`, matching the physical
  domain β > 0.
* Assumptions (finiteness, integrability) are parameterized to keep lemmas reusable.
* Semi–classical correction appears systematically as
    `kB * dof * log phaseSpaceUnit`.

## References

Same references as `Basic.lean` (Landau–Lifshitz; Tong), especially the identities
`F = U - T S` and `U = -∂_β log Z`.

-/

@[expose] public section
set_option linter.unusedVariables.funArgs false

namespace CanonicalEnsemble

open MeasureTheory Real Temperature Constants

open scoped Constants ENNReal

variable {ι ι1 : Type} [MeasurableSpace ι]
  [MeasurableSpace ι1] (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)

/-- An intermediate potential defined from the mathematical partition function. See
`helmholtzFreeEnergy` for the physical thermodynamic quantity. -/
noncomputable def mathematicalHelmholtzFreeEnergy (T : Temperature) : ℝ :=
  - kB * T.val * Real.log (𝓒.mathematicalPartitionFunction T)

/-- The relationship between the physical Helmholtz Free Energy and the Helmholtz Potential. -/
lemma helmholtzFreeEnergy_eq_helmholtzMathematicalFreeEnergy_add_correction (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.helmholtzFreeEnergy T = 𝓒.mathematicalHelmholtzFreeEnergy T +
      kB * T.val * 𝓒.dof * Real.log (𝓒.phaseSpaceunit) := by
  have hZ_pos := mathematicalPartitionFunction_pos 𝓒 T
  have h_pow_pos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  simp_rw [helmholtzFreeEnergy, mathematicalHelmholtzFreeEnergy, partitionFunction,
    Real.log_div hZ_pos.ne' h_pow_pos.ne', Real.log_pow]
  ring

/-- General identity: S_diff = kB β ⟨E⟩ + kB log Z_math.
This connects the differential entropy to the mean energy and the mathematical partition function.
Integrability of `log (probability …)` follows from the pointwise formula. -/
lemma differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hE : Integrable 𝓒.energy (𝓒.μProd T)) :
    𝓒.differentialEntropy T = kB * (T.β : ℝ) * 𝓒.meanEnergy T +
      kB * Real.log (𝓒.mathematicalPartitionFunction T) := by
  have hZpos := mathematicalPartitionFunction_pos 𝓒 T
  unfold differentialEntropy
  simp_rw [probability, Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  rw [integral_sub (hE.const_mul _) (integrable_const _), integral_const_mul,
      meanEnergy, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-- Pointwise logarithm of the Boltzmann probability. -/
lemma log_probability
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    Real.log (𝓒.probability T i)
      = - (β T) * 𝓒.energy i - Real.log (𝓒.mathematicalPartitionFunction T) := by
  have hZpos := mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T)
  unfold probability
  simp [Real.log_div, hZpos.ne', Real.log_exp, sub_eq_add_neg]

/-- Auxiliary identity: `kB · β = 1 / T`.
`β` is defined as `1 / (kB · T)` (see `Temperature.β`). -/
@[simp]
lemma kB_mul_beta (T : Temperature) (hT : 0 < T.val) :
    (kB : ℝ) * (T.β : ℝ) = 1 / T.val := by
  simp only [β_toReal, Temperature.toReal]
  field_simp [kB_ne_zero]

/-- Fundamental relation between thermodynamic and differential entropy:
`S_thermo = S_diff - kB * dof * log h`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_sub_correction
    (T : Temperature)
    (hE : Integrable 𝓒.energy (𝓒.μProd T))
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy T
      = 𝓒.differentialEntropy T
        - kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
  have h_int_log_prob :
      Integrable (fun i => Real.log (𝓒.probability T i)) (𝓒.μProd T) := by
    simp_rw [log_probability]
    exact (hE.const_mul _).sub (integrable_const _)
  unfold thermodynamicEntropy differentialEntropy
  simp_rw [log_physicalProbability]
  rw [integral_add h_int_log_prob (integrable_const _), integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-- No semiclassical correction when `dof = 0`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_of_dof_zero
    (T : Temperature) (hE : Integrable 𝓒.energy (𝓒.μProd T))
    (h0 : 𝓒.dof = 0)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy T = 𝓒.differentialEntropy T := by
  simpa [h0] using
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction (T:=T) (hE:=hE)

/-- No semiclassical correction when `phase_space_unit = 1`. -/
lemma thermodynamicEntropy_eq_differentialEntropy_of_phase_space_unit_one
    (T : Temperature) (hE : Integrable 𝓒.energy (𝓒.μProd T))
    (h1 : 𝓒.phaseSpaceunit = 1)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.thermodynamicEntropy T = 𝓒.differentialEntropy T := by
  simpa [h1] using
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction (T:=T) (hE:=hE)
/-

## Thermodynamic Identities

-/

/-!

## The Fundamental Thermodynamic Identity

-/

/-- The Helmholtz free energy `F` is related to the mean energy `U` and the absolute
thermodynamic entropy `S` by the identity `F = U - TS`. This theorem shows that the
statistically-defined quantities in this framework correctly satisfy this principle of
thermodynamics. -/
theorem helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy
    (T : Temperature) (hT : 0 < T.val)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hE : Integrable 𝓒.energy (𝓒.μProd T)) :
    𝓒.helmholtzFreeEnergy T
      = 𝓒.meanEnergy T - T.val * 𝓒.thermodynamicEntropy T := by
  have hSdiff :=
    𝓒.differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ (T:=T) (hE:=hE)
  have hScorr :=
    𝓒.thermodynamicEntropy_eq_differentialEntropy_sub_correction (T:=T) (hE:=hE)
  have hTne : (T.val : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hkβT : (T.val : ℝ) * (kB * (T.β : ℝ)) = 1 := by
    rw [kB_mul_beta T hT, mul_one_div, div_self hTne]
  have hZpos := 𝓒.mathematicalPartitionFunction_pos T
  have hhpos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  have hF_rewrite :
      𝓒.helmholtzFreeEnergy T
        = -kB * T.val *
            (Real.log (𝓒.mathematicalPartitionFunction T)
              - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit) := by
    simp [helmholtzFreeEnergy, partitionFunction,
          Real.log_div hZpos.ne' hhpos.ne', Real.log_pow,
          sub_eq_add_neg, mul_add, add_comm, mul_comm, mul_left_comm, mul_assoc]
  rw [hScorr, hSdiff, hF_rewrite]
  linear_combination 𝓒.meanEnergy T * hkβT

/-- **Theorem: Helmholtz identity with semi–classical correction term**.
Physical identity (always true for `T > 0`) :
  (U - F)/T = S_thermo
and:
  S_thermo = S_diff - kB * dof * log h.
Hence:
  S_diff = (U - F)/T + kB * dof * log h.
This theorem gives the correct relation for the (mathematical / differential) entropy.
(Removing the correction is only valid in normalized discrete cases
with `dof = 0` (or `phaseSpaceUnit = 1`).) -/
theorem differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp_add_correction
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hT : 0 < T.val)
    (hE : Integrable 𝓒.energy (𝓒.μProd T)) :
    𝓒.differentialEntropy T
      = (𝓒.meanEnergy T - 𝓒.helmholtzFreeEnergy T) / T.val
        + kB * 𝓒.dof * Real.log 𝓒.phaseSpaceunit := by
  have hS :=
    differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ (𝓒:=𝓒) (T:=T) hE
  have hTne : (T.val : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hZpos := 𝓒.mathematicalPartitionFunction_pos T
  have hhpos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  have hlog :
      Real.log (𝓒.mathematicalPartitionFunction T)
        = Real.log (𝓒.partitionFunction T)
          + (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
    rw [partitionFunction_def, Real.log_div hZpos.ne' hhpos.ne', Real.log_pow]
    ring
  rw [hS, helmholtzFreeEnergy_def, kB_mul_beta T hT, hlog]
  field_simp
  ring

/-- Discrete / normalized specialization of the previous theorem.
If either `dof = 0` (no semiclassical correction) or `phaseSpaceUnit = 1`
(so `log h = 0`), the correction term vanishes and we recover the bare Helmholtz identity
for the (differential) entropy. -/
lemma differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hT : 0 < T.val)
    (hE : Integrable 𝓒.energy (𝓒.μProd T))
    (hNorm : 𝓒.dof = 0 ∨ 𝓒.phaseSpaceunit = 1) :
    𝓒.differentialEntropy T
      = (𝓒.meanEnergy T - 𝓒.helmholtzFreeEnergy T) / T.val := by
  rw [differentialEntropy_eq_meanEnergy_sub_helmholtz_div_temp_add_correction
        (𝓒:=𝓒) (T:=T) hT hE]
  rcases hNorm with h | h <;> simp [h]

/-- Chain rule convenience lemma for `log ∘ f` on a set. -/
lemma hasDerivWithinAt_log_comp
    {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun t => Real.log (f t)) ((f x)⁻¹ * f') s x :=
  (Real.hasDerivAt_log hx).comp_hasDerivWithinAt x hf

/-- A version rewriting the derivative value with `1 / f x`. -/
lemma hasDerivWithinAt_log_comp'
    {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun t => Real.log (f t))
      ((1 / f x) * f') s x := by
  simpa [one_div, mul_comm, mul_left_comm, mul_assoc]
    using (hasDerivWithinAt_log_comp (f:=f) (f':=f') (s:=s) (x:=x) hf hx)

lemma integral_bolt_eq_integral_mul_exp
    {ι} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (φ : ι → ℝ) :
    ∫ x, φ x ∂ 𝓒.μBolt T
      = ∫ x, φ x * Real.exp (-T.β * 𝓒.energy x) ∂ 𝓒.μ := by
  unfold μBolt
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  simp [ENNReal.toReal_ofReal, Real.exp_nonneg, smul_eq_mul, mul_comm]

set_option linter.unusedVariables false in
/-- A specialization of `integral_bolt_eq_integral_mul_exp`
to the energy observable. -/
lemma integral_energy_bolt
    {ι} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    ∫ x, 𝓒.energy x ∂ 𝓒.μBolt T
      = ∫ x, 𝓒.energy x * Real.exp (-T.β * 𝓒.energy x) ∂ 𝓒.μ := by
  exact integral_bolt_eq_integral_mul_exp 𝓒 T 𝓒.energy

/-- The mean energy can be expressed as a ratio of integrals. -/
lemma meanEnergy_eq_ratio_of_integrals
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    𝓒.meanEnergy T =
      (∫ i, 𝓒.energy i * Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ) /
        (∫ i, Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ) := by
  unfold meanEnergy μProd
  have h_den : (𝓒.μBolt T Set.univ).toReal = ∫ x, Real.exp (- T.β * 𝓒.energy x) ∂ 𝓒.μ :=
    mathematicalPartitionFunction_eq_integral (𝓒:=𝓒) (T:=T)
  rw [integral_smul_measure, integral_energy_bolt, smul_eq_mul, ENNReal.toReal_inv,
      h_den, div_eq_inv_mul]

/-- The mean energy is the negative derivative of the logarithm of the
(mathematical) partition function with respect to β = 1/(kB T).
see: Tong (§1.3.2, §1.3.3), L&L (§31, implicitly, and §36)
Here the derivative is a `derivWithin` over `Set.Ioi 0`
since `β > 0`. -/
lemma meanEnergy_eq_neg_deriv_log_mathZ_of_beta
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h_deriv :
        HasDerivWithinAt
          (fun β : ℝ => ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          (- ∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ)
          (Set.Ioi 0) (T.β : ℝ)) :
    𝓒.meanEnergy T =
      - (derivWithin
          (fun β : ℝ => Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂𝓒.μ))
          (Set.Ioi 0) (T.β : ℝ)) := by
  set f : ℝ → ℝ := fun β => ∫ i, Real.exp (-β * 𝓒.energy i) ∂𝓒.μ
  have hβ_pos : 0 < (T.β : ℝ) := beta_pos T hT_pos
  have hZpos : 0 < f (T.β : ℝ) := by
    simpa [f, mathematicalPartitionFunction_eq_integral (𝓒:=𝓒) (T:=T)]
      using mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T)
  have hUD : UniqueDiffWithinAt ℝ (Set.Ioi (0:ℝ)) (T.β : ℝ) :=
    isOpen_Ioi.uniqueDiffWithinAt hβ_pos
  have h_deriv_log :
      derivWithin (fun β : ℝ => Real.log (f β)) (Set.Ioi 0) (T.β : ℝ)
        = (1 / f (T.β : ℝ)) *
            (- ∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ) :=
    (hasDerivWithinAt_log_comp' (hf := h_deriv) (hx := hZpos.ne')).derivWithin hUD
  have hf : f (T.β : ℝ) = ∫ i, Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ := rfl
  rw [meanEnergy_eq_ratio_of_integrals, h_deriv_log, hf]
  ring

section Ratios

open Set

open scoped Topology Filter ENNReal Constants

/-- Helper: equality (on `Set.Ioi 0`) between the β–parametrized logarithm of the
physical partition function and the β–parametrized logarithm of the *mathematical*
partition function up to the (β–independent) semiclassical correction. This is used only
to identify derivatives (the correction drops).
We add the hypothesis `h_fin` giving finiteness of the Boltzmann measure for every β > 0
(as needed to ensure the mathematical partition function is strictly positive). -/
lemma log_phys_eq_log_math_sub_const_on_Ioi
    (𝓒 : CanonicalEnsemble ι) [NeZero 𝓒.μ]
    (h_fin :
      ∀ β > 0,
        IsFiniteMeasure (𝓒.μBolt (Temperature.ofβ (Real.toNNReal β)))) :
    Set.EqOn
      (fun β : ℝ =>
        Real.log (𝓒.partitionFunction (Temperature.ofβ (Real.toNNReal β))))
      (fun β : ℝ =>
        Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit)
      (Set.Ioi (0 : ℝ)) := by
  intro β hβ
  have hβpos : 0 < β := hβ
  have _inst := h_fin β hβpos
  have hβnn : (Real.toNNReal β : ℝ) = β := Real.coe_toNNReal β hβpos.le
  have h_pow_pos : 0 < 𝓒.phaseSpaceunit ^ 𝓒.dof := pow_pos 𝓒.hPos _
  have hZpos : 0 < ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ := by
    have := mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=Temperature.ofβ (Real.toNNReal β))
    rwa [mathematicalPartitionFunction_eq_integral, β_ofβ, hβnn] at this
  simp only [partitionFunction_def, mathematicalPartitionFunction_eq_integral, β_ofβ, hβnn,
    Real.log_div hZpos.ne' h_pow_pos.ne', Real.log_pow]

/-- Derivative equality needed in `meanEnergy_eq_neg_deriv_log_Z_of_beta`.
Adds `h_fin` (finiteness of the Boltzmann measure for every β > 0). -/
lemma derivWithin_log_phys_eq_derivWithin_log_math
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val) [NeZero 𝓒.μ]
    (h_fin :
        ∀ β > 0,
          IsFiniteMeasure (𝓒.μBolt (Temperature.ofβ (Real.toNNReal β)))) :
    derivWithin
      (fun β : ℝ => Real.log (𝓒.partitionFunction (ofβ (Real.toNNReal β))))
      (Set.Ioi 0) (T.β : ℝ)
    =
    derivWithin
      (fun β : ℝ => Real.log (∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ))
      (Set.Ioi 0) (T.β : ℝ) := by
  have h_eq := log_phys_eq_log_math_sub_const_on_Ioi (𝓒:=𝓒) (h_fin:=h_fin)
  rw [derivWithin_congr h_eq (h_eq (beta_pos T hT_pos)), derivWithin_sub_const]

/-- The mean energy can also be expressed as the negative derivative of the logarithm of the
*physical* partition function with respect to β. This follows from the fact that the physical and
mathematical partition functions differ only by a constant factor, which vanishes upon
differentiation. -/
theorem meanEnergy_eq_neg_deriv_log_Z_of_beta
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    (hT_pos : 0 < T.val) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h_fin :
        ∀ β > 0,
          IsFiniteMeasure (𝓒.μBolt (Temperature.ofβ (Real.toNNReal β))))
    (h_deriv :
        HasDerivWithinAt
          (fun β : ℝ => ∫ i, Real.exp (-β * 𝓒.energy i) ∂ 𝓒.μ)
          (- ∫ i, 𝓒.energy i * Real.exp (-(T.β : ℝ) * 𝓒.energy i) ∂𝓒.μ)
          (Set.Ioi 0) (T.β : ℝ)) :
    𝓒.meanEnergy T =
      - (derivWithin
          (fun β : ℝ => Real.log (𝓒.partitionFunction (ofβ (Real.toNNReal β))))
          (Set.Ioi 0) (T.β : ℝ)) := by
  have h_math :=
    𝓒.meanEnergy_eq_neg_deriv_log_mathZ_of_beta T hT_pos h_deriv
  have h_dw :=
    derivWithin_log_phys_eq_derivWithin_log_math
      (𝓒:=𝓒) (T:=T) hT_pos h_fin
  rw [h_dw]; exact h_math

end Ratios

open scoped Topology Filter

/-! ## Fluctuations: variance identity -/

/-- The identity Var(E) = ⟨E²⟩ - ⟨E⟩². -/
theorem energyVariance_eq_meanSquareEnergy_sub_meanEnergy_sq
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) [IsProbabilityMeasure (𝓒.μProd T)]
    (hE_int : Integrable 𝓒.energy (𝓒.μProd T))
    (hE2_int : Integrable (fun i => (𝓒.energy i)^2) (𝓒.μProd T)) :
    𝓒.energyVariance T = 𝓒.meanSquareEnergy T - (𝓒.meanEnergy T)^2 := by
  unfold energyVariance meanSquareEnergy meanEnergy
  set U := ∫ i, 𝓒.energy i ∂𝓒.μProd T with hU
  have h_expand : (fun i => (𝓒.energy i - U)^2)
      = (fun i => (𝓒.energy i)^2 - 2 * U * 𝓒.energy i + U^2) := by
    funext i; ring
  have h1 : Integrable (fun i => 2 * U * 𝓒.energy i) (𝓒.μProd T) := hE_int.const_mul _
  rw [h_expand]
  erw [integral_add (hE2_int.sub h1) (integrable_const _), integral_sub hE2_int h1]
  rw [integral_const_mul, integral_const]
  simp only [← hU, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-! ## Heat capacity and parametric FDT -/

-- We define functions from ℝ to handle derivatives smoothly, using Real.toNNReal

/-- The mean energy as a function of the real-valued temperature t. -/
noncomputable def meanEnergy_T (𝓒 : CanonicalEnsemble ι) (t : ℝ) : ℝ :=
  𝓒.meanEnergy (Temperature.ofNNReal (Real.toNNReal t))

/-- The mean energy as a function of the real-valued inverse temperature b. -/
noncomputable def meanEnergyBeta (𝓒 : CanonicalEnsemble ι) (b : ℝ) : ℝ :=
  𝓒.meanEnergy (Temperature.ofβ (Real.toNNReal b))

/-- The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0). -/
noncomputable def heatCapacity (𝓒 : CanonicalEnsemble ι) (T : Temperature) : ℝ :=
  derivWithin (𝓒.meanEnergy_T) (Set.Ioi 0) (T.val : ℝ)

/-- Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)). -/
lemma heatCapacity_eq_deriv_meanEnergyBeta
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (hT_pos : 0 < T.val)
    (hU_deriv :
      HasDerivWithinAt (𝓒.meanEnergyBeta)
        (derivWithin (𝓒.meanEnergyBeta) (Set.Ioi 0) (T.β : ℝ))
        (Set.Ioi 0) (T.β : ℝ)) :
    𝓒.heatCapacity T
      = (derivWithin (𝓒.meanEnergyBeta) (Set.Ioi 0) (T.β : ℝ))
        * (-1 / (kB * (T.val : ℝ)^2)) := by
  unfold heatCapacity meanEnergy_T
  have h_U_eq_comp : (𝓒.meanEnergy_T) = fun t : ℝ => (𝓒.meanEnergyBeta) (betaFromReal t) := by
    funext t
    dsimp [meanEnergy_T, meanEnergyBeta, betaFromReal]
    simp
  let dUdβ := derivWithin (𝓒.meanEnergyBeta) (Set.Ioi 0) (T.β : ℝ)
  have h_chain := chain_rule_T_beta (F:=𝓒.meanEnergyBeta) (F':=dUdβ) T hT_pos hU_deriv
  have h_UD :
    UniqueDiffWithinAt ℝ (Set.Ioi (0 : ℝ)) (T.val : ℝ) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).uniqueDiffWithinAt hT_pos
  simp only [ofNNReal]
  rw [← (h_chain.derivWithin h_UD)]
  ring_nf
  simp_rw [← h_U_eq_comp]; rfl

/-- Parametric FDT: C_V = Var(E)/(kB T²), assuming Var(E) = - dU/dβ. -/
theorem fluctuation_dissipation_energy_parametric
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (hT_pos : 0 < T.val)
    (h_Var_eq_neg_dUdβ :
      𝓒.energyVariance T = - derivWithin (𝓒.meanEnergyBeta) (Set.Ioi 0) (T.β : ℝ))
    (hU_deriv :
      DifferentiableWithinAt ℝ (𝓒.meanEnergyBeta) (Set.Ioi 0) (T.β : ℝ)) :
    𝓒.heatCapacity T = 𝓒.energyVariance T / (kB * (T.val : ℝ)^2) := by
  let dUdβ := derivWithin (𝓒.meanEnergyBeta) (Set.Ioi 0) (T.β : ℝ)
  have hCV_eq_dUdβ_mul :
      𝓒.heatCapacity T = dUdβ * (-1 / (kB * (T.val : ℝ)^2)) :=
    heatCapacity_eq_deriv_meanEnergyBeta 𝓒 T hT_pos hU_deriv.hasDerivWithinAt
  rw [hCV_eq_dUdβ_mul, h_Var_eq_neg_dUdβ]
  have hkB_ne_zero := kB_ne_zero
  field_simp [hkB_ne_zero, pow_ne_zero 2]
  ring

end CanonicalEnsemble
