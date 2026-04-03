/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.QuantumMechanics.DDimensions.Operators.Unbounded
public import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
public import PhysLean.QuantumMechanics.PlanckConstant
public import PhysLean.SpaceAndTime.Space.Derivatives.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star
/-!

# Momentum operators

## i. Overview

In this module we introduce several momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `momentumOperator` : (components of) the momentum vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `-iℏ∂ᵢ`.
- `momentumOperatorSqr` : operator acting on Schwartz maps `𝓢(Space d, ℂ)` as `∑ᵢ 𝐩[i]∘𝐩[i]`.
- `momentumUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.

Notation:
- `𝐩[i]` for `momentumOperator i`
- `𝐩²` for `momentumOperatorSqr`

## iii. Table of contents

- A. Momentum vector operator
- B. Momentum-squared operator
- C. Unbounded momentum vector operator

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
noncomputable section
open Constants
open Space
open ContDiff SchwartzMap

variable {d : ℕ} (i : Fin d)

/-!

## A. Momentum vector operator

-/

/-- Component `i` of the momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`. -/
def momentumOperator : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (- Complex.I * ℏ) • (SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ∘L
    (SchwartzMap.fderivCLM ℂ (Space d) ℂ)

@[inherit_doc momentumOperator]
notation "𝐩[" i "]" => momentumOperator i

lemma momentumOperator_apply_fun (ψ : 𝓢(Space d, ℂ)) :
    𝐩[i] ψ = (- Complex.I * ℏ) • ∂[i] ψ := rfl

@[simp]
lemma momentumOperator_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩[i] ψ x = - Complex.I * ℏ * ∂[i] ψ x := rfl

/-!

## B. Momentum-squared operator

-/

/-- The square of the momentum operator, `𝐩² ≔ ∑ᵢ 𝐩ᵢ∘𝐩ᵢ`. -/
def momentumOperatorSqr : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := ∑ i, 𝐩[i] ∘L 𝐩[i]

@[inherit_doc momentumOperatorSqr]
notation "𝐩²" => momentumOperatorSqr

lemma momentumOperatorSqr_eq : 𝐩² = ∑ i : Fin d, 𝐩[i] ∘L 𝐩[i] := rfl

lemma momentumOperatorSqr_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩² ψ x = ∑ i, 𝐩[i] (𝐩[i] ψ) x := by
  dsimp only [momentumOperatorSqr]
  rw [← SchwartzMap.coe_coeHom]
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp', Finset.sum_apply,
    Function.comp_apply, map_sum]

/-!

## C. Unbounded momentum vector operator

-/

open SpaceDHilbertSpace MeasureTheory

/-- The momentum operators defined on the Schwartz submodule. -/
def momentumOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ 𝐩[i].toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

lemma momentumOperatorSchwartz_isSymmetric :
    (momentumOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨f, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨f', rfl⟩ := schwartzEquiv.surjective ψ'
  simp only [momentumOperatorSchwartz, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
    schwartzEquiv_inner, momentumOperator_apply, neg_mul, map_neg, map_mul, Complex.conj_I,
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
  UnboundedOperator.ofSymmetric (schwartzSubmodule_dense d)
    (momentumOperatorSchwartz_isSymmetric i)

end
end QuantumMechanics
