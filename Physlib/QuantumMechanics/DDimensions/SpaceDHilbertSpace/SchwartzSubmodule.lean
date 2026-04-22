/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
/-!

# Schwartz submodules

## i. Overview

In this module we define the Schwartz submodule of `SpaceDHilbertSpace`.

We also define, for each `a : ℕ∞`, a variant corresponding to Schwartz maps `f` satisfying
the polynomial growth bounds `‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` for each `(k : ℕ) ≤ a`. In particular,
for `a = ⊤` such a bound holds for all natural numbers. These serve as a natural domain
for singular unbounded operators such as the `1/r` Coulomb potential acting on `SpaceDHilbertSpace`.

Note: the condition defining polynomially-bounded Schwartz maps is phrased as
`‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` rather than as `‖f x‖ ≤ Cₖ * ‖x‖ ^ k` to mirror `SchwartzMap.decay`.
These two conditions only differ at `x = 0` and are therefore equivalent for `d > 0` since
then `f 0` may be determined by continuity. For `d = 0` the former does not constrain `f 0 = 0`
(since `x = 0` is the only point and `0⁻¹ = 0`) while the latter does (and would therefore spoil
their being dense in `SpaceDHilbertSpace 0 ≅ ℂ`).

## ii. Key results

- `schwartzSubmodule d`: Submodule of `SpaceDHilbertSpace d` consisting of the L² equivalence
  classes of Schwartz maps `𝓢(Space d, ℂ)`.
- `polyBddSchwartzSubmodule d (a : ℕ∞)`: Restriction of `schwartzSubmodule d` to those Schwartz maps
  which are bounded by powers of `‖x‖`.

## iii. Table of contents

- A. Schwartz submodule
- B. Polynomially-bounded Schwartz submodule
  - B.1. Definitions
  - B.2. (In)equalities
  - B.3. Density

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

open MeasureTheory
open InnerProductSpace
open SchwartzMap

/-!
## A. Schwartz submodule
-/

noncomputable section

variable {d : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The continuous linear map including Schwartz maps into `SpaceDHilbertSpace d`. -/
def schwartzIncl : 𝓢(Space d, ℂ) →L[ℂ] SpaceDHilbertSpace d := toLpCLM ℂ (E := Space d) ℂ 2

set_option backward.isDefEq.respectTransparency false in
/-- The submodule of `SpaceDHilbertSpace d` corresponding to Schwartz maps. -/
abbrev schwartzSubmodule (d : ℕ) := (schwartzIncl (d := d)).range

instance : CoeFun (schwartzSubmodule d) fun _ ↦ Space d → ℂ := ⟨fun ψ ↦ ψ.val⟩

@[simp]
lemma val_eq_coe (ψ : schwartzSubmodule d) (x : Space d) : ψ.val x = ψ x := rfl

lemma schwartzSubmodule_dense (d : ℕ) :
    Dense (schwartzSubmodule d : Set (SpaceDHilbertSpace d)) :=
  denseRange_toLpCLM ENNReal.top_ne_ofNat.symm

set_option backward.isDefEq.respectTransparency false in
/-- The linear equivalence between the Schwartz maps `𝓢(Space d, ℂ)` and the Schwartz submodule
  of `SpaceDHilbertSpace d`. -/
def schwartzEquiv : 𝓢(Space d, ℂ) ≃ₗ[ℂ] schwartzSubmodule d :=
  LinearEquiv.ofInjective schwartzIncl.toLinearMap (injective_toLp (E := Space d) 2)

variable (f g : 𝓢(Space d, ℂ)) (ψ : schwartzSubmodule d)

lemma schwartzEquiv_coe_ae : (schwartzEquiv f) =ᵐ[volume] f := coeFn_toLp f 2 volume

lemma schwartzEquiv_symm_coe_ae : schwartzEquiv.symm ψ =ᵐ[volume] ψ := by
  nth_rw 2 [← schwartzEquiv.apply_symm_apply ψ]
  exact (schwartzEquiv_coe_ae _).symm

lemma schwartzEquiv_apply_coe : ↑(schwartzEquiv f) = schwartzIncl f := by simp [schwartzEquiv]

lemma schwartzEquiv_inner :
    ⟪schwartzEquiv f, schwartzEquiv g⟫_ℂ = ∫ x : Space d, starRingEnd ℂ (f x) * g x := by
  apply integral_congr_ae
  filter_upwards [schwartzEquiv_coe_ae f, schwartzEquiv_coe_ae g] with _ hf hg
  simp [hf, hg, mul_comm]

lemma schwartzEquiv_ae_eq (h : schwartzEquiv f =ᵐ[volume] schwartzEquiv g) : f = g :=
  (EmbeddingLike.apply_eq_iff_eq _).mp (SetLike.coe_eq_coe.mp (ext_iff.mpr h))

lemma schwartzIncl_ker : schwartzIncl.ker = (⊥ : Submodule ℂ 𝓢(Space d, ℂ)) := by
  ext; simp [← schwartzEquiv_apply_coe]

end

/-!
## B. Polynomially-bounded Schwartz submodule
-/

noncomputable section

/-!
### B.1. Definitions
-/

/-- A function is a bounded Schwartz map if it is both Schwartz and bounded by powers of `‖x‖`. -/
def polyBddSchwartzMap (d : ℕ) (a : ℕ∞) : Submodule ℂ 𝓢(Space d, ℂ) where
  carrier := {f : 𝓢(Space d, ℂ) |
    ∀ k : ℕ, k ≤ a → ∃ C : ℝ, 0 < C ∧ ∀ x : Space d, ‖x‖ ^ (-k : ℤ) * ‖f x‖ ≤ C}
  add_mem' := by
    intro f g hf hg k hk
    obtain ⟨C₁, hC₁_pos, hC₁⟩ := hf k hk
    obtain ⟨C₂, hC₂_pos, hC₂⟩ := hg k hk
    refine ⟨C₁ + C₂, by positivity, fun x ↦ ?_⟩
    refine le_trans ?_ (add_le_add (hC₁ x) (hC₂ x))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le (f x) (g x)) (by positivity)
  zero_mem' := fun _ _ ↦ ⟨1, by simp⟩
  smul_mem' := by
    intro c f hf k hk
    obtain ⟨C, hC_pos, hC⟩ := hf k hk
    refine ⟨(1 + ‖c‖) * C, by positivity, fun x ↦ ?_⟩
    rw [smul_apply, norm_smul, mul_rotate', mul_comm ‖f x‖]
    exact le_trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)) (by linarith)

/-- The linear map `schwartzIncl` with domain restricted to `polyBddSchwartzMap d a`. -/
def polyBddSchwartzIncl {d : ℕ} {a : ℕ∞} : polyBddSchwartzMap d a →ₗ[ℂ] SpaceDHilbertSpace d :=
  schwartzIncl.domRestrict (polyBddSchwartzMap d a)

/-- The submodule of `SpaceDHilbertSpace d` corresponding to bounded Schwartz maps. -/
abbrev polyBddSchwartzSubmodule (d : ℕ) (a : ℕ∞) : Submodule ℂ (SpaceDHilbertSpace d) :=
  (polyBddSchwartzIncl (a := a)).range

lemma polyBddSchwartzIncl_injective (d : ℕ) (a : ℕ∞) :
    Function.Injective (polyBddSchwartzIncl (d := d) (a := a)) :=
  LinearMap.injective_domRestrict_iff.mpr <| schwartzIncl_ker.symm ▸ inf_bot_eq _

/-- The linear equivalence between polynomially-bounded Schwartz maps and the corresponding
  submodule of the Hilbert space. -/
def polyBddSchwartzEquiv {d : ℕ} {a : ℕ∞} :
    polyBddSchwartzMap d a ≃ₗ[ℂ] polyBddSchwartzSubmodule d a :=
  LinearEquiv.ofInjective polyBddSchwartzIncl (polyBddSchwartzIncl_injective d a)

/-!
### B.2. (In)equalities
-/

lemma polyBddSchwartzMap_zero_eq_top (d : ℕ) : polyBddSchwartzMap d 0 = ⊤ := by
  ext f
  have := f.decay 0 0
  simp_all [polyBddSchwartzMap]

lemma polyBddSchwartzMap_le_of_ge (d : ℕ) {a b : ℕ∞} (h : a ≤ b) :
    polyBddSchwartzMap d b ≤ polyBddSchwartzMap d a := fun _ hx k hk ↦ hx k (hk.trans h)

lemma polyBddSchwartzSubmodule_zero_eq (d : ℕ) :
    polyBddSchwartzSubmodule d 0 = schwartzSubmodule d := by
  simp [polyBddSchwartzSubmodule, polyBddSchwartzIncl, polyBddSchwartzMap_zero_eq_top]

lemma polyBddSchwartzSubmodule_le (d : ℕ) (a : ℕ∞) :
    polyBddSchwartzSubmodule d a ≤ schwartzSubmodule d := LinearMap.range_domRestrict_le_range _ _

lemma polyBddSchwartzSubmodule_le_of_ge (d : ℕ) {a b : ℕ∞} (h : a ≤ b) :
    polyBddSchwartzSubmodule d b ≤ polyBddSchwartzSubmodule d a := by
  simp only [polyBddSchwartzSubmodule, polyBddSchwartzIncl, LinearMap.range_domRestrict]
  exact Submodule.map_mono (polyBddSchwartzMap_le_of_ge d h)

end

end
end

end SpaceDHilbertSpace
end QuantumMechanics
