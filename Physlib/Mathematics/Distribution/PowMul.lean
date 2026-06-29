/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
/-!

## The multiple of a Schwartz map by `x`

In this module we define the continuous linear map from the Schwartz space
`𝓢(ℝ, 𝕜)` to itself which takes a Schwartz map `η` to the Schwartz map `x * η`.

-/

@[expose] public section
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Physlib
namespace Distribution

variable [NormedSpace ℝ E]
open ContDiff
open MeasureTheory

lemma norm_iteratedFDeriv_ofRealCLM {x} (i : ℕ) :
    ‖iteratedFDeriv ℝ i (RCLike.ofRealCLM (K := 𝕜)) x‖ =
      if i = 0 then |x| else if i = 1 then 1 else 0 := by
  match i with
  | 0 => simp
  | 1 =>
    rw [norm_iteratedFDeriv_one, RCLike.ofRealCLM.fderiv]
    simp
  | (n + 2) =>
    have h : fderiv ℝ ⇑(RCLike.ofRealCLM (K := 𝕜)) = fun _ => RCLike.ofRealCLM := by
      ext1 y
      exact RCLike.ofRealCLM.fderiv
    rw [← norm_iteratedFDeriv_fderiv, h, iteratedFDeriv_const_of_ne n.succ_ne_zero]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The continuous linear map `𝓢(ℝ, 𝕜) →L[𝕜] 𝓢(ℝ, 𝕜)` taking a Schwartz map
  `η` to `x * η`. -/
def powOneMul : 𝓢(ℝ, 𝕜) →L[𝕜] 𝓢(ℝ, 𝕜) := by
  refine mkCLM (fun ψ ↦ fun x => x * ψ x) ?_ ?_ ?_ ?_
  · intro ψ1 ψ2 x
    simp [mul_add]
  · intro c ψ x
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  · intro ψ
    apply ContDiff.mul
    · change ContDiff ℝ _ RCLike.ofRealCLM
      fun_prop
    · exact SchwartzMap.smooth ψ ⊤
  · intro (k, n)
    use {(k, n - 1), (k + 1, n)}
    simp only [Real.norm_eq_abs, Finset.sup_insert, schwartzSeminormFamily_apply,
      Finset.sup_singleton, Seminorm.coe_sup, Pi.sup_apply]
    use n + 1
    refine ⟨by linarith, ?_⟩
    intro ψ x
    trans ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), ↑(n.choose i) *
      ‖iteratedFDeriv ℝ i (fun (x : ℝ) => (x : 𝕜)) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (fun x => ψ x) x‖
    · apply mul_le_mul_of_nonneg'
      · exact Preorder.le_refl (‖x‖ ^ k)
      · apply norm_iteratedFDeriv_mul_le (N := ∞)
        · change ContDiff ℝ ∞ RCLike.ofRealCLM
          fun_prop
        · exact SchwartzMap.smooth (ψ) ⊤
        · exact right_eq_inf.mp rfl
      · exact ContinuousMultilinearMap.opNorm_nonneg _
      · refine pow_nonneg ?_ k
        exact norm_nonneg x
    conv_lhs =>
      enter [2, 2, i, 1, 2]
      change ‖iteratedFDeriv ℝ i RCLike.ofRealCLM x‖
      rw [norm_iteratedFDeriv_ofRealCLM 𝕜 i]
    match n with
    | 0 =>
      simp only [Real.norm_eq_abs, zero_add, Finset.range_one, mul_ite, mul_one, mul_zero, ite_mul,
        zero_mul, Finset.sum_singleton, ↓reduceIte, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_zero, norm_iteratedFDeriv_zero, CharP.cast_eq_zero, ge_iff_le]
      trans (SchwartzMap.seminorm 𝕜 (k + 1) 0) ψ
      · apply le_trans ?_ (ψ.le_seminorm 𝕜 _ _ x)
        simp only [Real.norm_eq_abs, norm_iteratedFDeriv_zero]
        ring_nf
        rfl
      exact le_max_right ((SchwartzMap.seminorm 𝕜 k (0 - 1)) ψ)
        ((SchwartzMap.seminorm 𝕜 (k + 1) 0) ψ)
    | .succ n =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Real.norm_eq_abs, Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        and_self, ↓reduceIte, Nat.add_eq_right, mul_zero, zero_mul, Finset.sum_const_zero,
        zero_add, Nat.choose_one_right, Nat.cast_add, Nat.cast_one, mul_one, Nat.reduceAdd,
        Nat.add_one_sub_one, Nat.choose_zero_right, one_mul, Nat.sub_zero, ge_iff_le]
      trans (↑n + 1) * (|x| ^ k * ‖iteratedFDeriv ℝ n (fun x => (ψ) x) x‖)
            + (|x| ^ (k + 1) * ‖iteratedFDeriv ℝ (n + 1) (fun x => (ψ) x) x‖)
      · apply le_of_eq
        ring
      trans (↑n + 1) * (SchwartzMap.seminorm 𝕜 k (n) ψ)
            + (SchwartzMap.seminorm 𝕜 (k + 1) (n + 1) ψ)
      · apply add_le_add _ _
        apply mul_le_mul_of_nonneg_left _
        refine Left.add_nonneg ?_ ?_
        · exact Nat.cast_nonneg' n
        · exact zero_le_one' ℝ
        · exact ψ.le_seminorm 𝕜 k n x
        · exact ψ.le_seminorm 𝕜 (k + 1) (n + 1) x
      · by_cases h1 :((SchwartzMap.seminorm 𝕜 (k + 1) (n + 1)) ψ) <
          ((SchwartzMap.seminorm 𝕜 k n) ψ)
        · rw [max_eq_left_of_lt h1]
          trans (↑n + 1) * (SchwartzMap.seminorm 𝕜 k n) ψ + (SchwartzMap.seminorm 𝕜 k n) ψ
          apply add_le_add
          · simp
          · exact le_of_lt h1
          apply le_of_eq
          ring
        · simp at h1
          rw [max_eq_right h1]
          trans (↑n + 1) * (SchwartzMap.seminorm 𝕜 (k + 1) (n + 1)) ψ +
            (SchwartzMap.seminorm 𝕜 (k + 1) (n + 1)) ψ
          · apply add_le_add
            · apply mul_le_mul_of_nonneg_left _
              · linarith
              · exact h1
            · simp
          · apply le_of_eq
            ring

lemma powOneMul_apply (ψ : 𝓢(ℝ, 𝕜)) (x : ℝ) :
    powOneMul 𝕜 ψ x = x * ψ x := rfl

end Distribution
end Physlib
