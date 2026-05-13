/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded_v2
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
public import Physlib.QuantumMechanics.PlanckConstant
public import Physlib.SpaceAndTime.Space.Derivatives.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star
/-!

# Momentum operators

## i. Overview

In this module we introduce several momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `momentumOperator` : (components of) the momentum vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `-iℏ∂ᵢ`.
- `momentumUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.

Notation:
- `𝐩` for `momentumOperator`

## iii. Table of contents

- A. Momentum vector operator
- B. Unbounded momentum vector operator

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
noncomputable section
open Constants Complex
open Space
open ContDiff SchwartzMap

variable {d : ℕ} (i : Fin d)

/-!

## A. Momentum vector operator

-/

set_option backward.isDefEq.respectTransparency false in
/-- Component `i` of the momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`. -/
def momentumCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (- Complex.I * ℏ) • (SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ∘L
    (SchwartzMap.fderivCLM ℂ (Space d) ℂ)

@[inherit_doc momentumCLM]
notation "𝐩" => momentumCLM

@[inherit_doc momentumCLM]
notation "𝐩[" d' "]" => momentumCLM (d := d')

lemma momentumCLM_apply_fun (ψ : 𝓢(Space d, ℂ)) : 𝐩 i ψ = (-I * ℏ) • ∂[i] ψ := rfl

@[simp]
lemma momentumCLM_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) : 𝐩 i ψ x = -I * ℏ * ∂[i] ψ x :=
  rfl

/-!

## B. Unbounded momentum vector operator

-/

open MeasureTheory
open SpaceDHilbertSpace
open SchwartzSubmodule
open UnboundedOperator

set_option backward.isDefEq.respectTransparency false in
/-- The momentum operators defined on the Schwartz submodule. -/
def momentumOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ (𝐩 i).toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
lemma momentumOperatorSchwartz_isSymmetric :
    (momentumOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨f, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨f', rfl⟩ := schwartzEquiv.surjective ψ'
  simp only [momentumOperatorSchwartz, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
    schwartzEquiv_inner, momentumCLM_apply, neg_mul, map_neg, map_mul, Complex.conj_I,
    Complex.conj_ofReal, neg_neg, mul_neg, integral_neg]
  field_simp
  simp only [Space.deriv_eq, mul_assoc, integral_const_mul, neg_mul_eq_mul_neg, starRingEnd_apply]
  congr 2
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable _ _ _ (by fun_prop) (by fun_prop)]
  · simp only [neg_neg, fderiv_star]
    rfl
  · simp only [fderiv_star]
    exact .mul_of_top_left (((starL' ℝ : ℂ ≃L[ℝ] ℂ).integrable_comp_iff).mpr
        ((f.fderivCLM ℂ _ ℂ).evalCLM ℂ _ ℂ (basis i)).integrable)
      (SchwartzMap.memLp_top f' volume)
  · exact .mul_of_top_left (((starL' ℝ : ℂ ≃L[ℝ] ℂ).integrable_comp_iff).mpr f.integrable)
      (((f'.fderivCLM ℂ _ ℂ).evalCLM ℂ _ ℂ (basis i)).memLp_top volume)
  · exact .mul_of_top_left (((starL' ℝ : ℂ ≃L[ℝ] ℂ).integrable_comp_iff).mpr f.integrable)
      (f'.memLp_top volume)

/-- The symmetric momentum unbounded operators with domain the Schwartz
  submodule of the Hilbert space. -/
def momentumUnboundedOperator :
    UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) :=
  ofSymmetric' (SchwartzSubmodule.dense d) (momentumOperatorSchwartz_isSymmetric i)

/-!
## Momentum operator v2
-/

/-- The momentum operator as a LinearPMap with domain the Schwartz submodule. -/
def momentumOperator : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d where
  domain := schwartzSubmodule d
  toFun := schwartzIncl.toLinearMap ∘ₗ (𝐩 i).toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

@[inherit_doc momentumOperator]
notation "𝐏" => momentumOperator

lemma momentumOperator_apply (ψ : schwartzSubmodule d) :
    𝐏 i ψ = schwartzEquiv (𝐩 i (schwartzEquiv.symm ψ)) := rfl

lemma momentumOperator_apply_ae (ψ : schwartzSubmodule d) :
    𝐏 i ψ =ᵐ[volume] 𝐩 i (schwartzEquiv.symm ψ) :=
  schwartzEquiv_coe_ae _

lemma momentumOperator_range (ψ : schwartzSubmodule d) : 𝐏 i ψ ∈ schwartzSubmodule d := by
  simp [momentumOperator_apply]

lemma momentumOperator_hasDenseDomain : (𝐏 i).HasDenseDomain := SchwartzSubmodule.dense d

lemma momentumOperator_isSymmetric : (𝐏 i).IsSymmetric := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨g, rfl⟩ := schwartzEquiv.surjective φ
  simp only [momentumOperator_apply, ← Submodule.coe_inner, schwartzEquiv_inner,
    schwartzEquiv.symm_apply_apply, momentumCLM_apply]
  have heq : ∀ x, fderiv ℝ (star ∘ f) x = (starL' ℝ).toContinuousLinearMap ∘L (fderiv ℝ f x) :=
    fun _ ↦ fderiv_star
  have hI₁ : Integrable fun x ↦ star (f x) := (starL' ℝ).integrable_comp_iff.mpr f.integrable
  have hI₂ : Integrable fun x ↦ fderiv ℝ g x (basis i) * star (f x) := by
    refine hI₁.mul_of_top_right ?_
    exact ((g.fderivCLM ℂ _ _).evalCLM ℂ _ _ _).memLp_top
  have hI₃ : Integrable fun x ↦ g x * fderiv ℝ (star ∘ f) x (basis i) := by
    simp_rw [heq]
    refine Integrable.mul_of_top_right ?_ g.memLp_top
    apply (starL' ℝ).integrable_comp_iff.mpr
    exact ((f.fderivCLM ℂ _ _).evalCLM ℂ _ _ _).integrable
  have hI₄ : Integrable fun x ↦ g x * star (f x) := hI₁.mul_of_top_right g.memLp_top
  trans I * ℏ * ∫ x, g x * fderiv ℝ (star ∘ f) x (basis i)
  · simp_rw [← integral_const_mul_of_integrable hI₃, heq]
    simp [mul_comm, mul_left_comm, Space.deriv_eq]
  symm
  trans I * ℏ * -∫ x, fderiv ℝ ⇑g x (basis i) * star (f x)
  · rw [mul_neg, ← neg_mul, ← integral_const_mul_of_integrable hI₂]
    simp [mul_left_comm, mul_comm, Space.deriv_eq]
  symm
  congr 2
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI₂ hI₃ hI₄ (by fun_prop) (by fun_prop)

lemma momentumOperator_isUnbounded : (𝐏 i).IsUnbounded := by
  refine (LinearPMap.IsSymmetric.isUnbounded_iff_hasDenseDomain ?_).mpr ?_
  · exact momentumOperator_isSymmetric i
  · exact momentumOperator_hasDenseDomain i

/-- The square of the momentum operator. -/
def momentumSqrOperator : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  ∑ i, (𝐏 i).comp (𝐏 i) (momentumOperator_range i)

end
end QuantumMechanics
