/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Physlib.Electromagnetism.ThreeDimension.Basic
public import Physlib.Electromagnetism.Dynamics.IsExtrema
/-!

# Maxwell equations in three dimensions

This file states Maxwell's equations in the familiar vector-calculus language
and connects them to the tensorial backend formulation.

-/
namespace Electromagnetism
namespace ThreeDimension

open Time
open Space
open ElectromagneticPotential
open ContDiff

variable {𝓕 : FreeSpace} (V : ElectromagneticPotential 3) (J₄ : LorentzCurrentDensity 3)

local notation "φ" => V.scalarPotential 𝓕.c
local notation "A" => V.vectorPotential 𝓕.c
local notation "E" => V.electricField 𝓕.c
local notation "B" => V.magneticField 𝓕.c
local notation "ρ" => J₄.chargeDensity 𝓕.c
local notation "J" => J₄.currentDensity 𝓕.c
local notation "ε₀" => 𝓕.ε₀
local notation "μ₀" => 𝓕.μ₀

/-- Gauss's law for the electric field. -/
theorem gaussLawElectric (t : Time) (x : Space)
    (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V) (hJ : ContDiff ℝ ∞ J₄) :
    (∇ ⬝ E t) x = ρ t x / ε₀ := by
  rw [((isExtrema_iff_gauss_ampere_magneticFieldMatrix hV J₄ hJ (𝓕 := 𝓕)).mp h t x).1]

/-- Gauss's law for the magnetic field. -/
theorem gaussLawMagnetic (t : Time) (x : Space) (hV : ContDiff ℝ ∞ V) :
    (∇ ⬝ B t) x = 0 := by
  rw [magneticField_eq_3D, div_of_curl_eq_zero _ (by fun_prop)]
  simp only [Pi.zero_apply]

/-- Ampère's law. -/
theorem ampereLaw (t : Time) (x : Space)
    (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V) (hJ : ContDiff ℝ ∞ J₄) :
      (∇ ⨯ B t) x = μ₀ • J t x + μ₀ • ε₀ • ∂ₜ (fun t => E t x) t := by
  ext i
  have hdE := ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hV J₄ hJ (𝓕 := 𝓕)).mp h t x).2 i
  rw [← magneticField_curl_eq_magneticFieldMatrix] at hdE
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ← mul_assoc, hdE, add_sub_cancel]
  exact hV.of_le ENat.LEInfty.out

/-- Faraday's law. -/
theorem faradayLaw (t : Time) (x : Space) (hV : ContDiff ℝ ∞ V) :
    (∇ ⨯ E t) x = - ∂ₜ (fun t => B t x) t := by
  rw [electricField_eq_3D, magneticField_eq_3D]
  change curl ((-(fun t x => ∇ (scalarPotential 𝓕.c V t) x) t -
      (fun t x => ∂ₜ (fun t => vectorPotential 𝓕.c V t x) t) t)) x = _
  rw [curl_sub, curl_neg, curl_of_grad_eq_zero, time_deriv_curl_commute]
  simp only [neg_zero, Pi.sub_apply, Pi.zero_apply, zero_sub]
  all_goals fun_prop

end ThreeDimension
end Electromagnetism
