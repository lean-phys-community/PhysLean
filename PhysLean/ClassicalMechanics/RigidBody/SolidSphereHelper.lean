/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import PhysLean.ClassicalMechanics.RigidBody.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Helper lemma for the solid sphere inertia tensor
This file proves the integral of ‖x‖² over the unit ball in `EuclideanSpace ℝ (Fin 3)`,
which is needed for the solid sphere inertia tensor computation.
-/
open MeasureTheory Pointwise NNReal Real MeasureTheory.Measure
namespace RigidBody
/-- The integral of ‖x‖² over B(0,1) in `EuclideanSpace ℝ (Fin 3)` equals `4/5 * π`. -/
public lemma integral_norm_sq_unit_ball_euclid :
    ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖x‖ ^ 2 =
    4 / 5 * π := by
  trans ∫ x in Metric.ball ( 0 : EuclideanSpace ℝ ( Fin 3 ) ) 1, ‖x‖ ^ 2;
  · rw [ Measure.restrict_congr_set ];
    rw [ ae_eq_set ];
    norm_num [ Set.diff_eq_empty.mpr Metric.ball_subset_closedBall ];
    norm_num [ Measure.addHaar_sphere ];
  · have := @integral_eq_lintegral_of_nonneg_ae ( EuclideanSpace ℝ ( Fin 3 ) );
    convert this _ _ using 1;
    · rw [ lintegral_eq_lintegral_meas_le ];
      · have h_inner : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) {a : EuclideanSpace ℝ (Fin 3) | t ≤ ‖a‖ ^ 2} = ENNReal.ofReal (4 / 3 * Real.pi * (1 ^ 3 - t ^ (3 / 2 : ℝ))) := by
          intro t ht
          have h_volume : (volume {a : EuclideanSpace ℝ (Fin 3) | ‖a‖ ^ 2 ≥ t ∧ ‖a‖ < 1}) = ENNReal.ofReal (4 / 3 * Real.pi * (1 ^ 3 - t ^ (3 / 2 : ℝ))) := by
            have h_volume : (volume {a : EuclideanSpace ℝ (Fin 3) | ‖a‖ ≥ Real.sqrt t ∧ ‖a‖ < 1}) = ENNReal.ofReal (4 / 3 * Real.pi * (1 ^ 3 - (Real.sqrt t) ^ 3)) := by
              have h_volume : (volume {a : EuclideanSpace ℝ (Fin 3) | ‖a‖ < 1}) = ENNReal.ofReal (4 / 3 * Real.pi * 1 ^ 3) ∧ (volume {a : EuclideanSpace ℝ (Fin 3) | ‖a‖ < Real.sqrt t}) = ENNReal.ofReal (4 / 3 * Real.pi * (Real.sqrt t) ^ 3) := by
                constructor;
                · erw [ show { a : EuclideanSpace ℝ ( Fin 3 ) | ‖a‖ < 1 } = Metric.ball 0 1 by ext; simp +decide [ dist_eq_norm ], Measure.addHaar_ball ] <;> norm_num;
                  rw [ ← ENNReal.ofReal_mul ( by positivity ), mul_div_assoc, mul_comm ];
                · erw [ show { a : EuclideanSpace ℝ ( Fin 3 ) | ‖a‖ < Real.sqrt t } = Metric.ball 0 ( Real.sqrt t ) by ext; simp +decide [ dist_eq_norm ], Measure.addHaar_ball ] ; norm_num;
                  · rw [ ← ENNReal.ofReal_pow ( Real.sqrt_nonneg _ ) ] ; ring_nf;
                    rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf;
                  · positivity;
              convert congr_arg₂ ( · - · ) h_volume.1 h_volume.2 using 1;
              · rw [ ← measure_diff ] <;> norm_num;
                · exact congr_arg _ ( by ext; aesop );
                · exact fun x hx => hx.trans_le <| Real.sqrt_le_iff.mpr ⟨ by norm_num, by linarith [ ht.1, ht.2 ] ⟩;
                · exact measurableSet_lt ( measurable_norm ) measurable_const |> MeasurableSet.nullMeasurableSet;
                · exact h_volume.2.symm ▸ ENNReal.ofReal_ne_top;
              · rw [ ← ENNReal.ofReal_sub ] <;> ring_nf ; norm_num [ Real.pi_pos.le, ht.1.le, ht.2.le ];
                positivity;
            convert h_volume using 4 <;> norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 3, ← Real.rpow_mul ht.1.le ];
            exact fun _ => ⟨ fun h => by rw [ ← Real.sqrt_eq_rpow ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, h ⟩, fun h => by rw [ ← Real.sqrt_eq_rpow ] at h; nlinarith [ Real.sqrt_nonneg t, Real.sq_sqrt ht.1.le ] ⟩;
          rw [ ← h_volume, Measure.restrict_apply' ];
          · norm_num [ Set.setOf_and, Metric.mem_ball ];
            norm_num [ Metric.ball ];
          · exact measurableSet_ball;
        have h_subst : ∫⁻ (t : ℝ) in Set.Ioi 0, (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) {a : EuclideanSpace ℝ (Fin 3) | t ≤ ‖a‖ ^ 2} = ∫⁻ (t : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (4 / 3 * Real.pi * (1 ^ 3 - t ^ (3 / 2 : ℝ))) := by
          rw [ ← lintegral_indicator, ← lintegral_indicator ];
          · congr with x ; by_cases hx : 0 < x <;> by_cases hx' : x < 1 <;> simp +decide [ hx, hx', h_inner ];
            rw [ Measure.restrict_apply' ];
            · rw [ show { a : EuclideanSpace ℝ ( Fin 3 ) | x ≤ ‖a‖ ^ 2 } ∩ Metric.ball 0 1 = ∅ from Set.eq_empty_of_forall_notMem fun y hy => by nlinarith [ hy.1.out, hy.2.out, show ‖y‖ ^ 2 < 1 from by simpa using hy.2.out ] ] ; norm_num;
            · exact measurableSet_ball;
          · norm_num;
          · norm_num;
        rw [ h_subst, ← ofReal_integral_eq_lintegral_ofReal ];
        · norm_num [ ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le, Real.pi_pos.le ] ; ring_nf;
          rw [ intervalIntegral.integral_sub, integral_rpow ] <;> norm_num ; ring;
          exact intervalIntegral.intervalIntegrable_rpow' ( by norm_num );
        · exact Continuous.integrableOn_Icc ( by exact Continuous.mul ( continuous_const ) ( continuous_const.sub ( continuous_id.rpow_const <| by norm_num ) ) ) |> fun h => h.mono_set <| Set.Ioo_subset_Icc_self;
        · filter_upwards [ ae_restrict_mem measurableSet_Ioo ] with t ht using mul_nonneg ( by positivity ) ( sub_nonneg.2 <| by exact le_trans ( Real.rpow_le_one ht.1.le ht.2.le <| by norm_num ) <| by norm_num );
      · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
      · exact Continuous.aemeasurable ( by continuity );
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
    · exact Continuous.aestronglyMeasurable ( by continuity )
/-- The integral of `‖x‖²` over the unit ball in `Space 3` equals `4/5 * π`.
  Transferred from the corresponding result for `EuclideanSpace` via `Space.basis.repr`. -/
public lemma integral_norm_sq_unit_ball_space :
    ∫ x in Metric.closedBall (0 : Space 3) 1, ‖x‖ ^ 2 = 4 / 5 * π := by
  have h : ∫ x in Metric.closedBall (0 : Space 3) 1, ‖x‖ ^ 2 =
      ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖x‖ ^ 2 := by
    rw [← (Space.basis (d := 3)).repr.measurePreserving.setIntegral_preimage_emb
      (Space.basis (d := 3)).repr.toMeasurableEquiv.measurableEmbedding]
    congr 1
    · simp
    · ext x; simp [LinearIsometryEquiv.norm_map]
  rw [h, integral_norm_sq_unit_ball_euclid]
end RigidBody
