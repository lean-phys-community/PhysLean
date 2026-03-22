module
public import PhysLean.ClassicalMechanics.RigidBody.Basic
public import PhysLean.ClassicalMechanics.RigidBody.SolidSphereHelper
/-!
# The solid sphere as a rigid body
In this module we consider the solid sphere as a rigid body, and compute its mass,
center of mass and inertia tensor.
-/
@[expose] public section
open Manifold
open MeasureTheory
namespace RigidBody
open NNReal
/-- The solid sphere as a rigid body. -/
noncomputable def solidSphere (d : ℕ) (m R : ℝ≥0) : RigidBody d where
  ρ := ⟨⟨fun f => m / volume.real (Metric.closedBall (0 : Space d) R) *
      ∫ x in Metric.closedBall (0 : Space d) R, f x ∂volume,
    by
    intro f g
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [integral_add]
    ring
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))⟩, by
      intro r f
      simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [integral_const_mul]
      ring⟩
lemma solidSphere_mass {d : ℕ} (m R : ℝ≥0) (hr : R ≠ 0) : (solidSphere d.succ m R).mass = m := by
  simp only [mass, solidSphere]
  simp only [Nat.succ_eq_add_one, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk,
    integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, smul_eq_mul,
    mul_one]
  have h1 : (@volume (Space d.succ) measureSpaceOfInnerProductSpace).real
      (Metric.closedBall 0 R) ≠ 0 := by
    refine (measureReal_ne_zero_iff ?_).mpr ?_
    · apply Space.volume_closedBall_ne_top
    · apply Space.volume_closedBall_ne_zero
      have hr' := R.2
      have hx : R.1 ≠ 0 := by simpa using hr
      apply lt_of_le_of_ne hr' (Ne.symm hx)
  field_simp
/-- The center of mass of a solid sphere located at the origin is `0`. -/
lemma solidSphere_centerOfMass {d : ℕ} (m R : ℝ≥0) : (solidSphere d.succ m R).centerOfMass = 0 := by
  ext i
  simp only [Nat.succ_eq_add_one, centerOfMass, solidSphere, one_div, LinearMap.coe_mk,
    AddHom.coe_mk, ContMDiffMap.coeFn_mk, smul_eq_mul, Space.zero_apply, mul_eq_zero, inv_eq_zero,
    div_eq_zero_iff, coe_eq_zero]
  right
  right
  suffices ∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume
    = -∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume by linarith
  rw [← integral_neg]
  simp only [← integral_indicator measurableSet_closedBall, Set.indicator, Metric.mem_closedBall,
    dist_zero_right]
  rw [← integral_neg_eq_self]
  norm_num
/-!
## Helper lemmas for the inertia tensor computation
-/
/-- The linear isometry equivalence that reflects the `i`th coordinate of `Space d`. -/
private noncomputable def reflectCoord {d : ℕ} (i : Fin d) : Space d ≃ₗᵢ[ℝ] Space d where
  toLinearEquiv :=
    { toFun := fun x => ⟨fun k => if k = i then -x k else x k⟩
      map_add' := fun x y => by
        ext k; by_cases hk : k = i
        · simp [hk]; ring
        · simp [hk]
      map_smul' := fun c x => by
        ext k; by_cases hk : k = i <;> simp [hk, mul_neg]
      invFun := fun x => ⟨fun k => if k = i then -x k else x k⟩
      left_inv := fun x => by
        ext k; by_cases hk : k = i <;> simp [hk]
      right_inv := fun x => by
        ext k; by_cases hk : k = i <;> simp [hk] }
  norm_map' := fun x => by
    simp only [Space.norm_eq, LinearEquiv.coe_mk]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = i <;> simp [hk] <;> ring
private lemma reflectCoord_apply {d : ℕ} (i : Fin d) (x : Space d) (k : Fin d) :
    (reflectCoord i x) k = if k = i then -x k else x k := rfl
/-- The linear isometry equivalence that swaps coordinates `i` and `j` in `Space d`. -/
private noncomputable def swapCoord {d : ℕ} (i j : Fin d) : Space d ≃ₗᵢ[ℝ] Space d where
  toLinearEquiv :=
    { toFun := fun x => ⟨fun k => x (Equiv.swap i j k)⟩
      map_add' := fun x y => by ext k; simp
      map_smul' := fun c x => by ext k; simp
      invFun := fun x => ⟨fun k => x (Equiv.swap i j k)⟩
      left_inv := fun x => by ext k; simp [Equiv.swap_apply_self]
      right_inv := fun x => by ext k; simp [Equiv.swap_apply_self] }
  norm_map' := fun x => by
    simp only [Space.norm_eq, LinearEquiv.coe_mk]
    congr 1
    exact Fintype.sum_equiv (Equiv.swap i j) _ _ (fun _ => rfl)
private lemma swapCoord_apply {d : ℕ} (i j : Fin d) (x : Space d) (k : Fin d) :
    (swapCoord i j x) k = x (Equiv.swap i j k) := rfl
/-- A linear isometry preserves the closed ball. -/
private lemma preimage_closedBall_eq {d : ℕ} (σ : Space d ≃ₗᵢ[ℝ] Space d) (R : ℝ) :
    σ ⁻¹' Metric.closedBall (0 : Space d) R = Metric.closedBall 0 R := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
/-- The integral of `x i * x j` over a ball centered at the origin vanishes when `i ≠ j`,
  by coordinate reflection symmetry. -/
private lemma integral_closedBall_coord_mul_eq_zero {d : ℕ}
    (R : ℝ) (i j : Fin d) (hij : i ≠ j) :
    ∫ x in Metric.closedBall (0 : Space d) R, x i * x j = 0 := by
  suffices h : ∫ x in Metric.closedBall (0 : Space d) R, x i * x j =
      -(∫ x in Metric.closedBall (0 : Space d) R, x i * x j) by linarith
  set B := Metric.closedBall (0 : Space d) R
  set σ := reflectCoord i
  have hmp := σ.measurePreserving
  have hemb : MeasurableEmbedding σ := σ.toMeasurableEquiv.measurableEmbedding
  have hball : σ ⁻¹' B = B := preimage_closedBall_eq σ R
  -- ∫_B f = ∫_{σ⁻¹B} f∘σ = ∫_B f∘σ = ∫_B (-f) = -∫_B f
  have step2 : ∀ x : Space d, (σ x) i * (σ x) j = -(x i * x j) := by
    intro x
    simp [σ, reflectCoord_apply, if_neg (Ne.symm hij)]
  conv_lhs =>
    rw [(hmp.setIntegral_preimage_emb hemb (fun x : Space d => x i * x j) B).symm, hball]
  simp_rw [step2]
  exact integral_neg (f := fun x : Space d => x i * x j)
/-- The integral of `x i ^ 2` over a ball centered at the origin is the same for all coordinates,
  by coordinate permutation symmetry. -/
private lemma integral_closedBall_coord_sq_eq {d : ℕ}
    (R : ℝ) (i j : Fin d) :
    ∫ x in Metric.closedBall (0 : Space d) R, x i ^ 2 =
    ∫ x in Metric.closedBall (0 : Space d) R, x j ^ 2 := by
  set B := Metric.closedBall (0 : Space d) R
  set σ := swapCoord i j
  have hmp := σ.measurePreserving
  have hemb : MeasurableEmbedding σ := σ.toMeasurableEquiv.measurableEmbedding
  have hball : σ ⁻¹' B = B := preimage_closedBall_eq σ R
  have step1 : ∫ x in B, (x : Space d) i ^ 2 =
      ∫ x in σ ⁻¹' B, (σ x) i ^ 2 :=
    (hmp.setIntegral_preimage_emb hemb (fun x : Space d => x i ^ 2) B).symm
  have step2 : ∀ x : Space d, (σ x) i ^ 2 = x j ^ 2 := by
    intro x
    simp only [σ, swapCoord_apply, Equiv.swap_apply_left]
  rw [step1, hball]
  simp_rw [step2]

open Pointwise MeasureTheory.Measure Real in
/-- In `Space 3`, the integral of `x 0 ^ 2` over a ball of radius `R` centered at the origin
  is `R ^ 2 / 5` times the volume of the ball. -/
private lemma integral_closedBall_coord_sq_eq_div_vol (R : ℝ≥0) (hR : R ≠ 0) :
    ∫ x in Metric.closedBall (0 : Space 3) R, x 0 ^ 2 =
    (↑R) ^ 2 / 5 * volume.real (Metric.closedBall (0 : Space 3) R) := by
  have hR_pos : (0 : ℝ) < R := by
    have := R.2; have hx : R.1 ≠ 0 := by simpa using hR
    exact lt_of_le_of_ne this (Ne.symm hx)
  -- Step 1: Scale the integral from B(0,R) to B(0,1)
  have hscale : ∫ x in Metric.closedBall (0 : Space 3) (R : ℝ), x 0 ^ 2 =
      (R : ℝ) ^ 5 * ∫ x in Metric.closedBall (0 : Space 3) 1, x 0 ^ 2 := by
    have h := setIntegral_comp_smul_of_pos (volume : Measure (Space 3))
      (fun x : Space 3 => x 0 ^ 2) (Metric.closedBall (0 : Space 3) 1) hR_pos
    rw [smul_closedBall _ 0 (by norm_num : (0:ℝ) ≤ 1)] at h
    simp only [smul_zero, mul_one, Space.finrank_eq_dim] at h
    rw [Real.norm_of_nonneg (le_of_lt hR_pos)] at h
    have step : ∀ x : Space 3, (((R:ℝ) • x) 0) ^ 2 = (R:ℝ) ^ 2 * (x 0 ^ 2) := by
      intro x; simp [Space.smul_apply]; ring
    simp_rw [step] at h
    rw [MeasureTheory.integral_const_mul, smul_eq_mul] at h
    have hR3 : (R : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hR_pos)
    field_simp at h; linarith
  -- Step 2: Scale the volume
  have hvol_scale : volume.real (Metric.closedBall (0 : Space 3) (R : ℝ)) =
      (R : ℝ) ^ 3 * volume.real (Metric.closedBall (0 : Space 3) 1) := by
    have h := addHaar_closedBall_mul_of_pos (volume : Measure (Space 3)) 0 hR_pos 1
    simp only [mul_one, Space.finrank_eq_dim] at h
    rw [Measure.real, Measure.real, h, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  -- Step 3: By symmetry, 3 * ∫ x₀² = ∫ ‖x‖²
  have hsymm : ∀ (r : ℝ),
      3 * ∫ x in Metric.closedBall (0 : Space 3) r, x 0 ^ 2 =
      ∫ x in Metric.closedBall (0 : Space 3) r, ‖x‖ ^ 2 := by
    intro r
    set B := Metric.closedBall (0 : Space 3) r
    have hI : ∀ (g : Space 3 → ℝ), ContinuousOn g B →
        Integrable g (volume.restrict B) :=
      fun g hg => IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 r) hg)
    -- ‖x‖² = ∑ x_i²
    have hnorm : ∀ x : Space 3, ‖x‖ ^ 2 = ∑ k : Fin 3, x k ^ 2 := by
      intro x; rw [sq, Space.norm_eq]
      exact Real.mul_self_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg (x k)))
    simp_rw [hnorm]
    rw [integral_finset_sum _ (fun k _ => hI _ (by fun_prop))]
    simp only [B]
    simp_rw [integral_closedBall_coord_sq_eq r _ 0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  -- Step 4: Use ∫_{B(0,1)} ‖x‖² = 4π/5
  have hunit_sq : ∫ x in Metric.closedBall (0 : Space 3) 1, x 0 ^ 2 =
      1 / 5 * volume.real (Metric.closedBall (0 : Space 3) 1) := by
    -- From hsymm: 3 * ∫ x₀² = ∫ ‖x‖² = 4π/5
    have h3 := hsymm 1
    rw [RigidBody.integral_norm_sq_unit_ball_space] at h3
    -- volume.real(B(0,1)) = 4π/3
    have hvol1 : volume.real (Metric.closedBall (0 : Space 3) 1) = 4 / 3 * π := by
      have h := addHaar_closedBall_mul_of_pos (volume : Measure (Space 3)) 0
        (by norm_num : (0:ℝ) < 1) 1
      simp only [mul_one, Space.finrank_eq_dim, one_pow] at h
      rw [Measure.real,
        InnerProductSpace.volume_closedBall_of_dim_odd
          (k := 1) (by simp [Space.finrank_eq_dim])]
      simp only [Space.finrank_eq_dim, Nat.doubleFactorial, Nat.reduceAdd,
        Nat.reduceMul, Nat.cast_ofNat, pow_one, ENNReal.ofReal_one, one_pow, one_mul]
      rw [ENNReal.toReal_ofReal (by positivity)]
      ring
    rw [hvol1]
    linarith
  -- Step 5: Combine
  rw [hscale, hvol_scale, hunit_sq]
  ring
