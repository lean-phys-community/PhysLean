/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
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

open Filter Complex

private lemma enorm_bump_mul_le_enorm {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] {c : E} (f : ContDiffBump c) (g : E → 𝕜) (x : E) :
    ‖f x * g x‖ₑ ≤ ‖g x‖ₑ := by
  nth_rw 2 [← one_mul (g x)]
  simp_rw [enorm_mul]
  refine mul_le_mul_left ?_ ‖g x‖ₑ
  apply enorm_le_iff_norm_le.mpr
  rw [norm_algebraMap', Real.norm_eq_abs, norm_one, ← abs_one]
  exact abs_le_abs_of_nonneg f.nonneg f.le_one

private lemma tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq
    {d : ℕ} {α : Type*} {l : Filter α} {ψ : α → SpaceDHilbertSpace d} :
    Tendsto ψ l (nhds 0) ↔ Tendsto (fun a ↦ ∫⁻ x : Space d, ‖ψ a x‖ₑ ^ 2) l (nhds 0) := by
  trans Tendsto (fun a ↦ (∫⁻ x, ‖ψ a x‖ₑ ^ 2) ^ (2⁻¹ : ℝ)) l (nhds 0)
  · simp [tendsto_iff_edist_tendsto_0, edist_zero_right, Lp.enorm_def, eLpNorm, eLpNorm']
  constructor <;> intro h
  · apply Tendsto.ennrpow_const 2 at h
    simp_all [← ENNReal.rpow_mul_natCast]
  · apply Tendsto.ennrpow_const 2⁻¹ at h
    simp_all

private lemma polyBddSchwartzSubmodule_zero_top_dense :
    Dense (polyBddSchwartzSubmodule 0 ⊤ : Set (SpaceDHilbertSpace 0)) := by
  suffices polyBddSchwartzMap 0 ⊤ = ⊤ by
    simp [polyBddSchwartzSubmodule, polyBddSchwartzIncl, this, schwartzSubmodule_dense]
  refine Submodule.eq_top_iff'.mpr (fun f k hk ↦ ?_)
  refine ⟨1 + ‖f 0‖, by positivity, fun x ↦ ?_⟩
  simp only [Space.point_dim_zero_eq, norm_zero, zpow_neg, zpow_natCast]
  rcases eq_or_ne k 0 with (rfl | hk')
  · simp
  · simp [hk', add_nonneg]

lemma polyBddSchwartzSubmodule_top_dense (d : ℕ) :
    Dense (polyBddSchwartzSubmodule d ⊤ : Set (SpaceDHilbertSpace d)) := by
  rcases eq_zero_or_pos d with (rfl | hd)
  · -- `d = 0`: Every function `Space 0 ≅ {0} → ℂ` is in `polyBddSchwartzSubmodule 0 ⊤`.
    exact polyBddSchwartzSubmodule_zero_top_dense
  · -- `d > 0`: Construct a sequence in `polyBddSchwartzSubmodule d ⊤` which tends to `ξ`
    intro ξ
    apply mem_closure_iff_seq_limit.mpr
    -- `ψₙ = [fₙ]` is a sequence in `schwartzSubmodule` which tends to `ξ`
    obtain ⟨ψ, hψ, hψξ⟩ := mem_closure_iff_seq_limit.mp (schwartzSubmodule_dense d ξ)
    let f (n : ℕ) : 𝓢(Space d, ℂ) := schwartzEquiv.symm ⟨ψ n, hψ n⟩
    -- `bₙ` is a sequence of bump functions with shrinking domain
    let b (n : ℕ) : ContDiffBump (0 : Space d) :=
      ⟨(n + 1)⁻¹, 2 * (n + 1 : ℝ)⁻¹, by positivity, lt_two_mul_self Nat.inv_pos_of_nat⟩
    -- `φₙ = [bₙfₙ]` is a sequence in `schwartzSubmodule` which tends to `0`
    let g (n : ℕ) : 𝓢(Space d, ℂ) := smulLeftCLM ℂ (b n) (f n)
    let φ (n : ℕ) : SpaceDHilbertSpace d := schwartzIncl (g n)
    have hg (n : ℕ) (x : Space d) : g n x = b n x * f n x := by
      have := (b n).hasCompactSupport.hasTemperateGrowth (b n).contDiff
      rw [smulLeftCLM_apply_apply this, ← Complex.coe_smul, smul_eq_mul]
    use ψ - φ
    constructor
    · intro n
      rw [SetLike.mem_coe, LinearMap.mem_range, Subtype.exists]
      refine ⟨f n - g n, ?_, by simp [f, φ, polyBddSchwartzIncl, ← schwartzEquiv_apply_coe]⟩
      intro k _
      obtain ⟨C, hC_pos, hC⟩ := (f n).decay 0 0
      simp only [pow_zero, norm_iteratedFDeriv_zero, one_mul] at hC
      use (n + 1) ^ k * C
      refine ⟨by positivity, fun x ↦ ?_⟩
      rcases le_or_gt ‖x‖ (b n).rIn with (hx | hx)
      · have h_one : b n x = 1 := (b n).one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
        exact le_of_eq_of_le (b := 0) (by simp [hg, h_one]) (by positivity)
      · refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) hC_pos.le
        · rw [← inv_zpow', zpow_natCast]
          refine pow_le_pow_left₀ (by positivity) ?_ k
          exact (inv_lt_of_inv_lt₀ (Nat.cast_add_one_pos n) hx).le
        · refine le_trans ?_ (hC x)
          rw [sub_apply, ← one_mul (f n x), hg, ← sub_mul]
          simp_rw [norm_mul, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_one]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact abs_sub_le_of_nonneg_of_le zero_le_one le_rfl (b n).nonneg (b n).le_one
    · refine tendsto_of_sub_tendsto_zero ξ hψξ ?_
      rw [sub_sub_cancel_left, Pi.neg_def, ← neg_zero, tendsto_neg_iff]
      -- Split `φₙ = σₙ + (φₙ - σₐ)` with `σₙ ≔ [bₙξ]` a sequence in `SpaceDHilbertSpace`
      let s (n : ℕ) : Space d → ℂ := fun x ↦ b n x * ξ x
      let σ (n : ℕ) : SpaceDHilbertSpace d := by
        refine mk (f := s n) ⟨?_, ?_⟩
        · refine Continuous.comp_aestronglyMeasurable₂ (by fun_prop) ?_ ξ.val.aestronglyMeasurable
          exact continuous_ofReal.comp_aestronglyMeasurable (b n).continuous.aestronglyMeasurable
        · refine lt_of_le_of_lt ?_ (coe_hilbertSpace_memHS ξ).2
          exact eLpNorm_mono_enorm (enorm_bump_mul_le_enorm (b n) ξ)
      have hψ_ae (n : ℕ) : ψ n =ᵐ[volume] f n := (schwartzEquiv_symm_coe_ae ⟨ψ n, hψ n⟩).symm
      have hφ_ae (n : ℕ) : φ n =ᵐ[volume] g n := schwartzEquiv_coe_ae (g n)
      have hσ_ae (n : ℕ) : σ n =ᵐ[volume] s n := coe_mk_ae _
      have hφσ_ae (n : ℕ) : (φ - σ) n =ᵐ[volume] g n - s n :=
        (AEEqFun.coeFn_sub (φ n).val (σ n).val).trans <| (hφ_ae n).sub (hσ_ae n)
      have hψξ_ae (n : ℕ) : ψ n - ξ =ᵐ[volume] f n - ξ :=
        (AEEqFun.coeFn_sub (ψ n).val ξ.val).trans <| (hψ_ae n).sub EventuallyEq.rfl
      refine tendsto_of_sub_tendsto_zero (f := σ) 0 ?_ ?_
      · -- `σ = bₙξ → 0` since the norms are bounded by the integral of `‖ξ‖²` (independent of `n`!)
        -- on a domain which tends to zero
        apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
        let B (n : ℕ) : Set (Space d) := Metric.ball 0 (b n).rOut
        have hξB : Tendsto (fun n ↦ ∫⁻ x in B n, ‖ξ x‖ₑ ^ 2) atTop (nhds 0) := by
          refine tendsto_setLIntegral_zero ?_ ?_
          · apply lt_top_iff_ne_top.mp
            have hξ := L2.eLpNorm_rpow_two_norm_lt_top ξ
            simp_rw [eLpNorm_one_eq_lintegral_enorm, Real.rpow_ofNat, enorm_pow, enorm_norm] at hξ
            exact hξ
          · have : Nontrivial (Space d) := Nat.succ_pred_eq_of_pos hd ▸ Space.instNontrivialSucc
            let C : ℝ := (ENNReal.ofReal (√Real.pi ^ d / Real.Gamma (d / 2 + 1))).toReal
            have hvolB : ⇑volume ∘ B = fun n ↦ ENNReal.ofReal (C * (b n).rOut ^ d) := by
              ext n
              simp [B, InnerProductSpace.volume_ball, C, mul_comm,
                ENNReal.ofReal_pow (b n).rOut_pos.le]
            simp_rw [hvolB, ← ENNReal.ofReal_zero, b, ← one_div, mul_pow, ← mul_assoc]
            rw [← mul_zero (C * 2 ^ d), ← zero_pow (M₀ := ℝ) hd.ne']
            refine ENNReal.tendsto_ofReal <| Tendsto.const_mul (C * 2 ^ d) ?_
            exact tendsto_one_div_add_atTop_nhds_zero_nat.pow d
        refine Tendsto.squeeze tendsto_const_nhds hξB (zero_le _) (fun n ↦ ?_)
        suffices ∫⁻ x, ‖σ n x‖ₑ ^ 2 = ∫⁻ x in B n, ‖σ n x‖ₑ ^ 2 by
          rw [this]
          refine setLIntegral_mono_ae' measurableSet_ball ?_
          filter_upwards [hσ_ae n] with x h _
          exact ENNReal.pow_le_pow_left <| h ▸ enorm_bump_mul_le_enorm (b n) ξ x
        have h (A : Set (Space d)) : ∫⁻ x in A, ‖σ n x‖ₑ ^ 2 = ∫⁻ x in A, ‖s n x‖ₑ ^ 2 :=
          lintegral_congr_ae ((hσ_ae n).fun_comp (fun z ↦ ‖z‖ₑ ^ 2)).restrict
        rw [← setLIntegral_univ, h, h, setLIntegral_univ]
        refine (setLIntegral_eq_of_support_subset ?_).symm
        refine Function.support_subset_iff'.mpr (fun x hx ↦ ?_)
        simp [s, (b n).zero_of_le_dist (not_lt.mp hx)]
      · -- `φₙ - σₙ = bₙ(ψₙ - ξ) → 0` since `ψₙ → ξ` (by definition) and the `bₙ` are bounded
        apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
        have hψξ : Tendsto (fun n ↦ ∫⁻ x, ‖(ψ n - ξ) x‖ₑ ^ 2) atTop (nhds 0) :=
          tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mp (sub_self ξ ▸ hψξ.sub_const ξ)
        refine Tendsto.squeeze tendsto_const_nhds hψξ (zero_le _) (fun n ↦ ?_)
        refine lintegral_mono_ae ?_
        filter_upwards [hφσ_ae n, hψξ_ae n] with x h h'
        simp_rw [h, h', Pi.sub_apply, hg, s, ← mul_sub]
        exact ENNReal.pow_le_pow_left <| enorm_bump_mul_le_enorm (b n) (fun x ↦ f n x - ξ x) x

lemma polyBddSchwartzSubmodule_dense (d : ℕ) (a : ℕ∞) :
    Dense (polyBddSchwartzSubmodule d a : Set (SpaceDHilbertSpace d)) :=
  (polyBddSchwartzSubmodule_top_dense d).mono (polyBddSchwartzSubmodule_le_of_ge d le_top)

end

end SpaceDHilbertSpace
end QuantumMechanics
