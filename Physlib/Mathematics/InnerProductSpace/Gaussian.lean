/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!

# Gaussians in inner product spaces

-/

@[expose] public section

open ContinuousLinearMap Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (x : E)

/-- Crude bounds on the norms of iterated Fréchet derivatives of `innerSL ℝ`
  in the form required by `norm_iteratedFDeriv_comp_le`. -/
private lemma norm_iteratedFDeriv_innerSL_le_pow {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun x : E ↦ innerSL ℝ x x) x‖ ≤ (2 + ‖x‖ ^ 2) ^ n := by
  have h_id₁ : ‖iteratedFDeriv ℝ 1 id x‖ ≤ 1 := by simp [norm_id_le]
  have h_id : ∀ k ≥ 2, ‖iteratedFDeriv ℝ k id x‖ = 0 := by
    intro k hk
    rw [show k = k - 2 + 2 by omega, norm_eq_zero]
    ext
    simp [iteratedFDeriv_succ_apply_right]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        n.choose k * ‖iteratedFDeriv ℝ k id x‖ * ‖iteratedFDeriv ℝ (n - k) id x‖ :=
      (innerSL ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
        contDiff_id contDiff_id x (Nat.cast_le.mpr n.le_succ) (norm_innerSL_le ℝ)
    _ = n.choose 0 * ‖iteratedFDeriv ℝ 0 id x‖ * ‖iteratedFDeriv ℝ (n - 0) id x‖ +
        n.choose 1 * ‖iteratedFDeriv ℝ 1 id x‖ * ‖iteratedFDeriv ℝ (n - 1) id x‖ := by
      refine Finset.sum_eq_add_of_mem 0 1 ?_ ?_ zero_ne_one fun k hk hk₀₁ ↦ ?_
      · simp
      · simp [Nat.zero_lt_of_lt hn]
      · simp [h_id, hk₀₁, Nat.two_le_iff]
    _ ≤ ‖x‖ * ‖iteratedFDeriv ℝ n id x‖ + n.choose 1 * ‖iteratedFDeriv ℝ (n - 1) id x‖ := by bound
  rcases (show n = 1 ∨ n = 2 ∨ 2 < n by omega) with rfl | rfl | hn'
  · refine le_trans (b := 2 * ‖x‖) ?_ (by nlinarith)
    simp [← le_sub_iff_add_le, two_mul, mul_le_of_le_one_right, norm_id_le]
  · refine le_trans ?_ (le_trans (le_self_pow₀ one_le_two two_ne_zero) (by bound))
    simp [h_id, norm_id_le]
  · rw [h_id n (by omega), h_id (n - 1) (by omega), mul_zero, mul_zero, add_zero]
    positivity

private lemma pow_mul_exp_bddAbove {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∃ C > 0, ∀ x ≥ 0, x ^ s * (2 + x) ^ n * rexp (-2⁻¹ * x) ≤ C := by
  let b : ℝ → ℝ := fun x ↦ x ^ s * (2 + x) ^ n * rexp (-2⁻¹ * x)
  have hb : Continuous b := by fun_prop
  have htop : Tendsto b atTop (nhds 0) := by
    let g : ℝ → ℝ := fun x : ℝ ↦ x ^ (s + n) * rexp (-2⁻¹ * x)
    let g' : ℝ → ℝ := fun x ↦ 2 + x
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := 0) (h := exp 1 • g ∘ g') ?_ ?_ ?_ ?_
    · exact tendsto_const_nhds
    · rw [← smul_zero (exp 1)]
      refine Tendsto.const_smul ?_ _
      refine Tendsto.comp (y := atTop) ?_ ?_
      · exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s + n) 2⁻¹ (by norm_num)
      · exact tendsto_atTop_atTop.mpr fun x ↦ ⟨x - 2, by simp [g', add_comm]⟩
    · exact eventually_atTop.mpr ⟨0, fun _ _ ↦ by positivity⟩
    · refine eventually_atTop.mpr ⟨0, fun x hx ↦ ?_⟩
      simp only [b, g, g', Function.comp_def, Pi.smul_def, mul_add, exp_add, smul_eq_mul]
      field_simp
      simp only [exp_neg, rpow_add (show 0 < 2 + x by linarith), rpow_natCast]
      field_simp
      exact rpow_le_rpow hx (by linarith) hs
  have htail : ∀ᶠ x in atTop, b x < 1 :=
    (htop.eventually <| isOpen_Ioo.mem_nhds ⟨neg_one_lt_zero, zero_lt_one⟩).mono fun _ h ↦ h.2
  obtain ⟨M, hgM⟩ := eventually_atTop.mp htail
  obtain ⟨x₀, hx₀, hx₀'⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, Set.left_mem_Icc.mpr (abs_nonneg M)⟩ hb.continuousOn
  refine ⟨max (b x₀) 1, by simp, fun x hx ↦ ?_⟩
  by_cases hxM : x ≤ |M|
  · exact le_max_of_le_left (hx₀' ⟨hx, hxM⟩)
  · exact le_max_of_le_right (hgM x <| (le_abs_self _).trans (Std.le_of_not_ge hxM)).le

variable (E) in
/-- The (unnormalized) real-valued standard Gaussian `exp (-2⁻¹ * ‖x‖ ^ 2)` as a Schwartz map. -/
def realStdGaussian : 𝓢(E, ℝ) where
  toFun x := rexp (-2⁻¹ * ‖x‖ ^ 2)
  smooth' := contDiff_exp.fun_comp <| contDiff_const.mul <| contDiff_norm_sq ℝ
  decay' k n := by
    obtain ⟨C, hC, hbC⟩ := pow_mul_exp_bddAbove (show 0 ≤ (k / 2 : ℝ) by positivity) n
    use n.factorial * C
    intro x
    calc
      _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((fun x ↦ rexp (-2⁻¹ * x)) ∘ fun x ↦ innerSL ℝ x x) x‖ := by
        simp [Function.comp_def]
      _ ≤ ‖x‖ ^ k * (n.factorial * rexp (-2⁻¹ * innerSL ℝ x x) * (2 + ‖x‖ ^ 2) ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by simp)
        refine norm_iteratedFDeriv_comp_le (by fun_prop) ?_ (Nat.cast_le.mpr n.le_succ) x ?_ ?_
        · simp [contDiff_norm_sq ℝ]
        · intro m _
          simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul,
            norm_mul, norm_eq_abs, abs_exp, norm_pow, norm_neg, norm_inv, inv_pow, Nat.abs_ofNat]
          refine mul_le_of_le_one_left (exp_nonneg _) ?_
          exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
        · exact fun m hm _ ↦ norm_iteratedFDeriv_innerSL_le_pow x hm
      _ = n.factorial * ((‖x‖ ^ 2) ^ (k / 2 : ℝ) * (2 + ‖x‖ ^ 2) ^ n * rexp (-2⁻¹ * ‖x‖ ^ 2)) := by
        rw [← rpow_natCast_mul (norm_nonneg _)]
        field_simp
        simp
      _ ≤ n.factorial * C :=
        mul_le_mul_of_nonneg_left (hbC _ <| pow_two_nonneg ‖x‖) (Nat.cast_nonneg' _)

