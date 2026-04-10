/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
public import Physlib.SpaceAndTime.Space.Integrals.NormPow
/-!

# Position operators

## i. Overview

In this module we introduce several position operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `positionOperator` : (components of) the position vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` by multiplication by `xᵢ`.
- `radiusRegPowOperator` : operator acting on Schwartz maps by multiplication by
    `(‖x‖² + ε²)^(s/2)`, a smooth regularization of `‖x‖ˢ`.
- `positionUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.
- `readiusRegPowUnboundedOperator` : a symmetric unbounded operator acting on the Schwartz
    submodule of the Hilbert space `SpaceDHilbertSpace d`. For `s ≤ 0` this operator is in fact
    bounded (by `|ε|ˢ`) and has natural domain the entire Hilbert space, but for uniformity we
    use the same domain for all `s`.

Notation:
- `𝐱` for `positionOperator`
- `𝐫₀` for `radiusRegPowOperator`
- `𝐫` for `radiusPowOperator`

## iii. Table of contents

- A. Schwartz operators
  - A.1. Position vector
  - A.2. Radius powers (regularized)
  - A.3. Radius powers
    - A.3.1. As limit of regularized operators
- B. Unbounded operators
  - B.1. Position vector
  - B.2. Radius powers (regularized)

## iv. References

-/

@[expose] public section

namespace QuantumMechanics

variable {d : ℕ} (i : Fin d)

/-!
## A. Schwartz operators
-/

noncomputable section
open Space Function
open SchwartzMap

/-!
### A.1. Position vector
-/

set_option backward.isDefEq.respectTransparency false in
/-- Component `i` of the position operator is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`. -/
def positionOperator : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofRealCLM ∘L coordCLM i)

@[inherit_doc positionOperator]
notation "𝐱" => positionOperator

@[inherit_doc positionOperator]
notation "𝐱[" d' "]" => positionOperator (d := d')

lemma positionOperator_apply_fun (ψ : 𝓢(Space d, ℂ)) : 𝐱 i ψ = (fun x : Space d ↦ x i) • ⇑ψ := by
  ext
  simp [positionOperator, coordCLM_apply, coord_apply,
    smulLeftCLM_apply_apply (g := Complex.ofRealCLM ∘ (coordCLM i)) (by fun_prop)]

@[simp]
lemma positionOperator_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) : 𝐱 i ψ x = x i * ψ x := by
  simp [positionOperator_apply_fun]

/-!
### A.2. Radius powers (regularized)
-/
TODO "ZGCNP" "Incorporate normRegularizedPow into Space.Norm"

/-- Power of regularized norm, `(‖x‖² + ε²)^(s/2)`. -/
def normRegularizedPow (d : ℕ) (ε s : ℝ) : Space d → ℝ :=
  fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)

lemma norm_sq_add_unit_sq_pos {d : ℕ} (ε : ℝˣ) (x : Space d) : 0 < ‖x‖ ^ 2 + ε ^ 2 :=
    Left.add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) (sq_pos_iff.mpr <| Units.ne_zero ε)

lemma normRegularizedPow_pos (d : ℕ) (ε : ℝˣ) (s : ℝ) (x : Space d) :
    0 < normRegularizedPow d ε s x :=
  Real.rpow_pos_of_pos (norm_sq_add_unit_sq_pos ε x) (s / 2)

lemma normRegularizedPow_hasTemperateGrowth (d : ℕ) (ε : ℝˣ) (s : ℝ) :
    HasTemperateGrowth (normRegularizedPow d ε s) := by
  -- Write `normRegularizedPow` as the composition of three simple functions
  -- to take advantage of `hasTemperateGrowth_one_add_norm_sq_rpow`.
  let f1 := fun (x : ℝ) ↦ (ε ^ 2) ^ (s / 2) * x
  let f2 := fun (x : Space d) ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)
  let f3 := fun (x : Space d) ↦ ε.1⁻¹ • x
  have h123 : normRegularizedPow d ε s = f1 ∘ f2 ∘ f3 := by
    ext
    simp only [normRegularizedPow, f1, f2, f3, comp_apply, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [← Real.mul_rpow (sq_nonneg ↑ε) (add_nonneg (zero_le_one' _) (sq_nonneg _))]
    simp [mul_add, mul_pow, add_comm]
  rw [h123]
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-- The radius operator to power `s`, regularized by `ε ≠ 0`, is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `(‖x‖² + ε²)^(s/2) • ψ`. -/
def radiusRegPowOperator {d : ℕ} (ε : ℝˣ) (s : ℝ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ normRegularizedPow d ε s)

@[inherit_doc radiusRegPowOperator]
notation "𝐫₀" => radiusRegPowOperator

@[inherit_doc radiusRegPowOperator]
notation "𝐫₀[" d' "]" => radiusRegPowOperator (d := d')

lemma radiusRegPowOperator_apply_fun {d : ℕ} (ε : ℝˣ) (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    𝐫₀ ε s ψ = fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by
  ext x
  dsimp [radiusRegPowOperator]
  refine smulLeftCLM_apply_apply ?_ ψ x
  exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth d ε s)

@[simp]
lemma radiusRegPowOperator_apply {d : ℕ} (ε : ℝˣ) (s : ℝ) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐫₀ ε s ψ x = (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by
  rw [radiusRegPowOperator_apply_fun]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma radiusRegPowOperator_comp_eq {d : ℕ} (ε : ℝˣ) (s t : ℝ) :
    𝐫₀[d] ε s ∘L 𝐫₀ ε t = 𝐫₀ ε (s+t) := by
  ext ψ x
  simp [add_div, Real.rpow_add (norm_sq_add_unit_sq_pos ε x), mul_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma radiusRegPowOperator_zero {d : ℕ} (ε : ℝˣ) :
    𝐫₀ ε 0 = ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
lemma positionOperatorSqr_eq {d : ℕ} (ε : ℝˣ) :
    ∑ i, 𝐱 i ∘L 𝐱 i = 𝐫₀ ε 2 - ε.1 ^ 2 • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext
  simp [Space.norm_sq_eq, add_mul, ← mul_assoc, ← pow_two, Finset.sum_mul]

/-!
### A.3. Radius powers
-/

open MeasureTheory
open SpaceDHilbertSpace

set_option backward.isDefEq.respectTransparency false in
/-- The radius operator to power `s` is the linear map from `𝓢(Space d, ℂ)` to `Space d → ℂ` that
  maps `ψ` to `x ↦ ‖x‖ˢψ(x)` (which is 'nearly' Schwartz for general `s`). -/
def radiusPowOperator {d : ℕ} (s : ℝ) : 𝓢(Space d, ℂ) →ₗ[ℂ] Space d → ℂ where
  toFun ψ := (fun x : Space d ↦ ‖x‖ ^ s) • ψ
  map_add' _ _ := by rw [← smul_add]; rfl
  map_smul' _ _ := by rw [smul_comm]; rfl

@[inherit_doc radiusPowOperator]
notation "𝐫" => radiusPowOperator

lemma radiusPowOperator_apply_fun {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    𝐫 s ψ = fun x ↦ ‖x‖ ^ s • ψ x := rfl

@[simp]
lemma radiusPowOperator_apply {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐫 s ψ x = ‖x‖ ^ s • ψ x := by
  rw [radiusPowOperator_apply_fun]

set_option backward.isDefEq.respectTransparency false in
/-- `x ↦ ‖x‖ˢψ(x)` is smooth away from `x = 0`. -/
@[fun_prop]
lemma radiusPowOperator_apply_contDiffAt {d : ℕ} (s : ℝ) (n : ℕ∞) (ψ : 𝓢(Space d, ℂ)) {x : Space d}
    (hx : x ≠ 0) : ContDiffAt ℝ n (𝐫 s ψ) x := by
  refine ContDiffAt.smul ?_ (ψ.contDiffAt n)
  have h (x : Space d) : ‖x‖ ^ s = (inner ℝ x x) ^ (s / 2) := by
    simp [← Real.rpow_natCast_mul, mul_div_cancel₀]
  simp only [h]
  exact ContDiffAt.rpow_const_of_ne (by fun_prop) (inner_self_ne_zero.mpr hx)

set_option backward.isDefEq.respectTransparency false in
/-- `x ↦ ‖x‖ˢψ(x)` is strongly measurable. -/
@[fun_prop]
lemma radiusPowOperator_apply_stronglyMeasurable {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    StronglyMeasurable (𝐫 s ψ) := by
  rw [radiusPowOperator_apply_fun]
  exact StronglyMeasurable.smul (by measurability) ψ.continuous.stronglyMeasurable

set_option backward.isDefEq.respectTransparency false in
/-- `x ↦ ‖x‖ˢψ(x)` is square-integrable provided `s` is not too negative. -/
lemma radiusPowOperator_apply_memHS {d : ℕ} (s : ℝ) (h : 0 < d + 2 * s) (ψ : 𝓢(Space d, ℂ)) :
    MemHS (𝐫 s ψ) := by
  rcases Nat.eq_zero_or_pos d with (rfl | hd)
  · simp only [MemHS, MemLp.of_discrete]
  · refine (MeasureTheory.memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ⟨by fun_prop, ?_⟩
    suffices ∫⁻ (a : Space d), ‖‖ψ a‖ ^ 2 * ‖a‖ ^ (2 * s)‖ₑ < ⊤ by
      have hInt (x : Space d) : ‖𝐫 s ψ x‖ ^ 2 = ‖ψ x‖ ^ 2 * ‖x‖ ^ (2 * s) := by
        simp [radiusPowOperator, mul_pow, mul_comm, Real.rpow_mul]
      simpa only [HasFiniteIntegral, hInt]
    rw [← lintegral_add_compl _ (measurableSet_ball (x := 0) (ε := 1)), ENNReal.add_lt_top]
    constructor
    · -- `‖x‖ < 1`: bound `‖ψ x‖` by a constant
      obtain ⟨C, hC_pos, hC⟩ := ψ.decay 0 0
      simp only [pow_zero, norm_iteratedFDeriv_zero, one_mul] at hC
      suffices hBound : ∀ x, ‖‖ψ x‖ ^ 2 * ‖x‖ ^ (2 * s)‖ₑ ≤ ‖C ^ 2‖ₑ * ‖‖x‖ ^ (2 * s)‖ₑ by
        calc
          _ ≤ ∫⁻ (x : Space d) in (Metric.ball 0 1), ‖C ^ 2‖ₑ * ‖‖x‖ ^ (2 * s)‖ₑ :=
            setLIntegral_mono' measurableSet_ball (fun x _ ↦ hBound x)
          _ = ‖C ^ 2‖ₑ * ∫⁻ (x : Space d) in (Metric.ball 0 1), ‖‖x‖ ^ (2 * s)‖ₑ :=
            lintegral_const_mul _ (by fun_prop)
        apply ENNReal.mul_lt_top enorm_lt_top
        exact ((integrableOn_norm_rpow_ball_iff hd Real.zero_lt_one _).mpr h).hasFiniteIntegral
      intro x
      simp_rw [← enorm_mul, enorm_le_iff_norm_le, norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact (sq_le_sq₀ (norm_nonneg _) hC_pos.le).mpr (hC x)
    · -- `1 ≤ ‖x‖`: bound `‖ψ x‖` by a suitable power of `‖x‖`
      obtain ⟨C, hC_pos, hC⟩ := ψ.decay (⌈s⌉.toNat + d) 0
      simp only [norm_iteratedFDeriv_zero, ← Real.rpow_natCast, Nat.cast_add] at hC
      suffices hBound : ∀ x ∈ (Metric.ball 0 1)ᶜ,
          ‖‖ψ x‖ ^ 2 * ‖x‖ ^ (2 * s)‖ₑ ≤ ‖C ^ 2‖ₑ * ‖‖x‖ ^ (-2 * d : ℝ)‖ₑ by
        calc
          _ ≤ ∫⁻ (x : Space d) in (Metric.ball 0 1)ᶜ, ‖C ^ 2‖ₑ * ‖‖x‖ ^ (-2 * d : ℝ)‖ₑ :=
            setLIntegral_mono' (by measurability) hBound
          _ = ‖C ^ 2‖ₑ * ∫⁻ (x : Space d) in (Metric.ball 0 1)ᶜ, ‖‖x‖ ^ (-2 * d : ℝ)‖ₑ :=
            lintegral_const_mul _ (by fun_prop)
        apply ENNReal.mul_lt_top enorm_lt_top
        have hd' : (d + -2 * d : ℝ) < 0 := by simp [hd]
        exact ((integrableOn_norm_rpow_ball_compl_iff hd zero_lt_one _).mpr hd').hasFiniteIntegral
      intro x hx
      simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hx
      simp_rw [← enorm_mul, enorm_le_iff_norm_le, norm_mul, norm_pow, Real.norm_eq_abs, sq_abs,
        Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm]
      have hx' : 0 < ‖x‖ := by linarith
      have hψ : ‖ψ x‖ ≤ C * ‖x‖ ^ (-(⌈s⌉.toNat + d) : ℝ) := by
        rw [Real.rpow_neg hx'.le]
        exact (le_mul_inv_iff₀' <| Real.rpow_pos_of_pos hx' _).mpr (hC x)
      calc
        _ ≤ (C * ‖x‖ ^ (-(⌈s⌉.toNat + d) : ℝ)) ^ 2 * ‖x‖ ^ (2 * s) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx'.le _)
          exact pow_le_pow_left₀ (norm_nonneg _) hψ 2
        _ = C ^ 2 * ‖x‖ ^ (-2 * d : ℝ) * ‖x‖ ^ (2 * (s - ⌈s⌉.toNat) : ℝ) := by
          simp_rw [mul_pow, ← Real.rpow_mul_natCast hx'.le, mul_assoc, ← Real.rpow_add hx']
          ring_nf
      suffices s ≤ ⌈s⌉.toNat by
        have h' : 0 < C ^ 2 * ‖x‖ ^ (-2 * d : ℝ) :=
          mul_pos (sq_pos_of_pos hC_pos) (Real.rpow_pos_of_pos hx' _)
        apply (mul_le_iff_le_one_right h').mpr
        exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
      rcases lt_or_ge 0 s with (hs | hs)
      · have hs' : ⌈s⌉.toNat = (⌈s⌉ : ℝ) :=
          Int.cast_inj.mpr <| Int.toNat_of_nonneg <| Int.ceil_nonneg hs.le
        exact hs' ▸ Int.le_ceil s
      · have hs' : ⌈s⌉.toNat = (0 : ℝ) :=
          Nat.cast_eq_zero.mpr <| Int.toNat_of_nonpos <| Int.ceil_le.mpr (by rwa [Int.cast_zero])
        exact hs' ▸ hs

/-!
#### A.3.1. As limit of regularized operators
-/

open Filter

/-- Neighborhoods of "0" in the non-zero reals, i.e. those sets containing `(-ε,0) ∪ (0,ε) ⊆ ℝˣ`
  for some `ε > 0`. -/
abbrev nhdsZeroUnits : Filter ℝˣ := comap (Units.coeHom ℝ) (nhds 0)

instance : NeBot nhdsZeroUnits := by
  refine comap_neBot fun t ht ↦ ?_
  obtain ⟨ε, hε_pos, hε⟩ := Metric.mem_nhds_iff.mp ht
  use Units.mk0 (ε / 2) (by linarith)
  apply hε
  simp [abs_of_pos, hε_pos]

/-- `𝐫[ε,s] ψ` converges pointwise to `𝐫[s] ψ` as `ε → 0` except perhaps at `x = 0`. -/
lemma radiusRegPow_tendsto_radiusPow {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) {x : Space d}
    (hx : x ≠ 0) : Tendsto (fun ε ↦ 𝐫₀ ε s ψ x) nhdsZeroUnits (nhds (𝐫 s ψ x)) := by
  have hpow : ‖x‖ ^ s = (‖x‖ ^ 2 + 0 ^ 2) ^ (s / 2) := by
    simp [← Real.rpow_natCast_mul, mul_div_cancel₀]
  simp only [radiusRegPowOperator_apply, radiusPowOperator_apply, Complex.real_smul, hpow]
  refine Tendsto.mul_const (ψ x) <| Tendsto.ofReal ?_
  refine Tendsto.rpow_const ?_ (Or.inl <| by simp [hx])
  exact Tendsto.const_add _ <| Tendsto.pow tendsto_comap 2

/-- `𝐫[ε,s] ψ` converges pointwise to `𝐫[s] ψ` as `ε → 0` provided `𝐫[ε,s] ψ 0` is bounded. -/
lemma radiusRegPow_tendsto_radiusPow' {d : ℕ} (s : ℝ) (ψ : 𝓢(Space d, ℂ)) (h : 0 ≤ s ∨ ψ 0 = 0) :
    Tendsto (fun ε ↦ ⇑(𝐫₀ ε s ψ)) nhdsZeroUnits (nhds (𝐫 s ψ)) := by
  refine tendsto_pi_nhds.mpr fun x ↦ ?_
  rcases eq_zero_or_neZero x with (rfl | hx)
  · rcases h with (hs | hψ)
    · simp only [radiusRegPowOperator_apply, radiusPowOperator_apply, Complex.real_smul, norm_zero,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
      have : (0 : ℝ) ^ s = (0 ^ 2) ^ (s / 2) := by
        rw [← Real.rpow_natCast_mul (le_refl 0), Nat.cast_ofNat, mul_div_cancel₀ s (by norm_num)]
      rw [this]
      refine Tendsto.mul_const (ψ 0) <| Tendsto.ofReal ?_
      exact Tendsto.rpow_const (Tendsto.pow tendsto_comap 2) (Or.inr <| by linarith)
    · simp [hψ]
  · exact radiusRegPow_tendsto_radiusPow s ψ hx.ne

/-- a.e. version of `radiusRegPow_tendsto_radiusPow` -/
lemma radiusRegPow_ae_tendsto_radiusPow {d : ℕ} (hd : 0 < d) (s : ℝ) (ψ : 𝓢(Space d, ℂ)) :
    ∀ᵐ x, Tendsto (fun ε ↦ 𝐫₀ ε s ψ x) nhdsZeroUnits (nhds (𝐫 s ψ x)) := by
  apply ae_iff.mpr
  suffices h : {x | ¬Tendsto (fun ε ↦ 𝐫₀ ε s ψ x) nhdsZeroUnits (nhds (𝐫 s ψ x))} ⊆ {0} by
    rcases Set.subset_singleton_iff_eq.mp h with (h' | h')
    · exact h' ▸ measure_empty
    · have : Nontrivial (Space d) := Nat.succ_pred_eq_of_pos hd ▸ Space.instNontrivialSucc
      exact h' ▸ measure_singleton 0
  intro x hx
  by_contra hx'
  exact hx <| radiusRegPow_tendsto_radiusPow s ψ hx'

lemma radiusRegPow_ae_tendsto_iff {d : ℕ} (hd : 0 < d) {s : ℝ} {ψ : 𝓢(Space d, ℂ)}
    {φ : Space d → ℂ} : (∀ᵐ x, Tendsto (fun ε ↦ 𝐫₀ ε s ψ x) nhdsZeroUnits (nhds (φ x)))
    ↔ φ =ᵐ[volume] 𝐫 s ψ := by
  let t₁ := {x | ¬Tendsto (fun ε ↦ 𝐫₀ ε s ψ x) nhdsZeroUnits (nhds (φ x))}
  let t₂ := {x | φ x ≠ 𝐫 s ψ x}
  show volume t₁ = 0 ↔ volume t₂ = 0
  suffices heq : t₁ ∪ {0} = t₂ ∪ {0} by
    have : Nontrivial (Space d) := Nat.succ_pred_eq_of_pos hd ▸ Space.instNontrivialSucc
    have hUnion : ∀ t : Set (Space d), volume t = 0 ↔ volume (t ∪ {0}) = 0 :=
      fun _ ↦ by simp only [measure_union_null_iff, measure_singleton, and_true]
    rw [hUnion t₁, hUnion t₂, heq]
  ext x
  rcases eq_zero_or_neZero x with (rfl | hx)
  · simp
  · simp only [Set.union_singleton, Set.mem_insert_iff, hx.ne, false_or]
    have hLim := radiusRegPow_tendsto_radiusPow s ψ hx.ne
    exact not_congr ⟨fun h ↦ tendsto_nhds_unique h hLim, fun h ↦ h ▸ hLim⟩

end

/-!
## B. Unbounded operators
-/

noncomputable section

open SpaceDHilbertSpace

/-!
### B.1. Position vector
-/

set_option backward.isDefEq.respectTransparency false in
/-- The position operators defined on the Schwartz submodule. -/
def positionOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ (𝐱 i).toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
lemma positionOperatorSchwartz_isSymmetric : (positionOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨_, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨_, rfl⟩ := schwartzEquiv.surjective ψ'
  unfold positionOperatorSchwartz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, schwartzEquiv_inner]
  congr with x
  simp only [LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe,
    positionOperator_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The symmetric position unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
def positionUnboundedOperator : UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (schwartzSubmodule_dense d) (positionOperatorSchwartz_isSymmetric i)

/-!
### B.2. Radius powers (regularized)
-/

set_option backward.isDefEq.respectTransparency false in
/-- The (regularized) radius operators defined on the Schwartz submodule. -/
def radiusRegPowOperatorSchwartz {d : ℕ} (ε : ℝˣ) (s : ℝ) :
    schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  schwartzEquiv.toLinearMap ∘ₗ (𝐫₀ ε s).toLinearMap ∘ₗ schwartzEquiv.symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
lemma radiusRegPowOperatorSchwartz_isSymmetric {d : ℕ} (ε : ℝˣ) (s : ℝ) :
    (radiusRegPowOperatorSchwartz (d := d) ε s).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨_, rfl⟩ := schwartzEquiv.surjective ψ
  obtain ⟨_, rfl⟩ := schwartzEquiv.surjective ψ'
  simp only [radiusRegPowOperatorSchwartz, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, schwartzEquiv_inner]
  congr with x -- match integrands
  simp only [LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe, radiusRegPowOperator_apply,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

/-- The symmetric (regularized) radius unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
def radiusRegPowUnboundedOperator {d : ℕ} (ε : ℝˣ) (s : ℝ) :
    UnboundedOperator (SpaceDHilbertSpace d) (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (schwartzSubmodule_dense d)
    (radiusRegPowOperatorSchwartz_isSymmetric ε s)

end
end QuantumMechanics
