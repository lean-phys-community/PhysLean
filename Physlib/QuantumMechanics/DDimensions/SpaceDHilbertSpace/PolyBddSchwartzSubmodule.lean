/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
public import Physlib.Meta.Linters.Sorry
/-!

# Polynomially-bounded Schwartz submodules

## i. Overview

In this module we define polynomially-bounded Schwartz submodules of `SpaceDHilbertSpace`.

For each `a : ℕ∞`, `polyBddSchwartzSubmodule d a` is the submodule corresponding to Schwartz
maps `f` satisfying the polynomial growth bounds `‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` for all `(k : ℕ) ≤ a`.
In particular, for `a = ⊤` such a bound holds for all natural numbers.

These serve as a natural domain for singular unbounded operators. For example, the `1/r` Coulomb
potential operator maps `polyBddSchwartzSubmodule d ⊤` to itself. In the same way that multiplying
a Schwartz map by any polynomial in the coordinates results in a square-integrable function,
polynomially-bounded Schwartz maps may be multiplied by Laurent polynomials and remain
square-integrable (the precise condition depends on `d`, `a` and the negative degree of
the Laurent polynomial).

Note: the condition defining polynomially-bounded Schwartz maps is phrased as
`‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` rather than as `‖f x‖ ≤ Cₖ * ‖x‖ ^ k` to mirror `SchwartzMap.decay`.
These two conditions only differ at `x = 0` and are therefore equivalent for `d > 0` since
then `f 0` may be determined by continuity. For `d = 0` the former does not constrain `f 0 = 0`
(since `x = 0` is the only point and `0⁻¹ = 0`) while the latter does (and would therefore spoil
their being dense in `SpaceDHilbertSpace 0 ≅ ℂ`).

## ii. Key results

- `polyBddSchwartzSubmodule d (a : ℕ∞)`: Restriction of `schwartzSubmodule d` to those Schwartz maps
  which are bounded by powers of `‖x‖`.
- `polyBddSchwartzSubmodule_dense d a`: These submodules are dense in `SpaceDHilbertSpace`.

## iii. Table of contents

- A. Definitions
- B. (In)equalities
- C. Density

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

open MeasureTheory
open InnerProductSpace
open SchwartzMap

noncomputable section

/-!
### A. Definitions
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

/-- The continuous linear map `schwartzIncl` with domain restricted to `polyBddSchwartzMap d a`. -/
def polyBddSchwartzIncl {d : ℕ} {a : ℕ∞} : polyBddSchwartzMap d a →L[ℂ] SpaceDHilbertSpace d :=
  ⟨schwartzIncl.domRestrict (polyBddSchwartzMap d a),
    schwartzIncl.continuous_domRestrict schwartzIncl.continuous _⟩

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
  LinearEquiv.ofInjective polyBddSchwartzIncl.toLinearMap (polyBddSchwartzIncl_injective d a)

/-!
### B. (In)equalities
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

/-!
### C. Density
-/

@[sorryful]
lemma polyBddSchwartzSubmodule_top_dense (d : ℕ) :
    Dense (polyBddSchwartzSubmodule d ⊤ : Set (SpaceDHilbertSpace d)) :=
  sorry

@[sorryful]
lemma polyBddSchwartzSubmodule_dense (d : ℕ) (a : ℕ∞) :
    Dense (polyBddSchwartzSubmodule d a : Set (SpaceDHilbertSpace d)) :=
  (polyBddSchwartzSubmodule_top_dense d).mono (polyBddSchwartzSubmodule_le_of_ge d le_top)

end

end SpaceDHilbertSpace
end QuantumMechanics
