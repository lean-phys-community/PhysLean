/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
/-!

# Schwartz submodule of the Hilbert space

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

noncomputable section

open MeasureTheory
open InnerProductSpace
open SchwartzMap

/-!
## A. Schwartz submodule
-/

section

variable {d : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The continuous linear map including Schwartz functions into `SpaceDHilbertSpace d`. -/
def schwartzIncl : 𝓢(Space d, ℂ) →L[ℂ] SpaceDHilbertSpace d := toLpCLM ℂ (E := Space d) ℂ 2

set_option backward.isDefEq.respectTransparency false in
/-- The submodule of `SpaceDHilbertSpace d` consisting of Schwartz functions. -/
abbrev schwartzSubmodule (d : ℕ) := (schwartzIncl (d := d)).range

instance : CoeFun (schwartzSubmodule d) fun _ ↦ Space d → ℂ := ⟨fun ψ ↦ ψ.val⟩

@[simp]
lemma val_eq_coe (ψ : schwartzSubmodule d) (x : Space d) : ψ.val x = ψ x := rfl

lemma schwartzSubmodule_dense (d : ℕ) :
    Dense (schwartzSubmodule d : Set (SpaceDHilbertSpace d)) :=
  denseRange_toLpCLM ENNReal.top_ne_ofNat.symm

set_option backward.isDefEq.respectTransparency false in
/-- The linear equivalence between the Schwartz functions `𝓢(Space d, ℂ)`
  and the Schwartz submodule of `SpaceDHilbertSpace d`. -/
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

end

/-!
## B. Bounded Schwartz submodule
-/

section

/-!
### B.1. Definitions
-/

/-- The submodule of Schwartz maps which are bounded by `Cₖ‖x‖ᵏ` for all `(k : ℕ) ≤ a`. -/
def bddSchwartzMap (d : ℕ) (a : ℕ∞) : Submodule ℂ 𝓢(Space d, ℂ) where
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

lemma bddSchwartzMap_zero_eq_top (d : ℕ) : bddSchwartzMap d 0 = ⊤ := by
  ext f
  have := f.decay 0 0
  simp_all [bddSchwartzMap]

lemma bddSchwartzMap_le_of_ge (d : ℕ) {a b : ℕ∞} (h : a ≤ b) :
    bddSchwartzMap d b ≤ bddSchwartzMap d a := fun _ hx k hk ↦ hx k (hk.trans h)

/-- The linear map including `bddSchwartzMap d a` into the Hilbert space. -/
def bddSchwartzIncl (d : ℕ) (a : ℕ∞) : bddSchwartzMap d a →ₗ[ℂ] SpaceDHilbertSpace d :=
  schwartzIncl.domRestrict (bddSchwartzMap d a)

/-- The submodule of `SpaceDHilbertSpace d` consisting of Schwartz functions which are bounded
  by `Cₖ‖x‖ᵏ` for all `(k : ℕ) ≤ a`. -/
abbrev bddSchwartzSubmodule (d : ℕ) (a : ℕ∞) : Submodule ℂ (SpaceDHilbertSpace d) :=
  (bddSchwartzIncl d a).range

lemma bddSchwartzIncl_injective (d : ℕ) (a : ℕ∞) : Function.Injective (bddSchwartzIncl d a) := by
  apply LinearMap.injective_domRestrict_iff.mpr
  have h : (schwartzIncl (d := d)).toLinearMap.ker = ⊥ := by ext; simp [← schwartzEquiv_apply_coe]
  exact h.symm ▸ inf_bot_eq _

/-- The linear equivalence between `bddSchwartzMap d a` and the bounded Schwartz submodule
  of `SpaceDHilbertSpace d`. -/
def bddSchwartzEquiv {d : ℕ} {a : ℕ∞} : bddSchwartzMap d a ≃ₗ[ℂ] bddSchwartzSubmodule d a :=
  LinearEquiv.ofInjective (bddSchwartzIncl d a) (bddSchwartzIncl_injective d a)

end

end
end SpaceDHilbertSpace
end QuantumMechanics
