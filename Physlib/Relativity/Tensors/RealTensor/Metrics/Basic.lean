/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Basic
public import Physlib.Relativity.Tensors.MetricTensor
/-!

## Metrics as real Lorentz tensors

-/

@[expose] public section

open Module
open Matrix
open MatrixGroups
open TensorProduct

noncomputable section

namespace realLorentzTensor

/-!

## Definitions.

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
abbrev coMetric (d : ℕ := 3) : ℝT[d, .down, .down] :=
  (realLorentzTensor d).metricTensor .down

/-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
abbrev contrMetric (d : ℕ := 3) : ℝT[d, .up, .up] :=
  (realLorentzTensor d).metricTensor .up

/-!

## Notation

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η'" => @coMetric

/-- The metric `ηⁱⁱ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η" => @contrMetric

/-!

## Equivalent forms of the metrics

-/
open TensorSpecies
open Tensor

lemma coMetric_eq_fromConstPair {d : ℕ} :
    η' d = fromConstPair (S := realLorentzTensor d) (c1 := .down) (c2 := .down)
      (Lorentz.preCoMetric d) := by
  rfl

lemma contrMetric_eq_fromConstPair {d : ℕ} :
    η d = fromConstPair (S := realLorentzTensor d)
      (c1 := .up) (c2 := .up) (Lorentz.preContrMetric d) := by
  rfl

lemma coMetric_eq_fromPairT {d : ℕ} :
    η' d = fromPairT (S := realLorentzTensor d) (c1 := .down) (c2 := .down)
      (Lorentz.preCoMetricVal d) := by
  rw [coMetric_eq_fromConstPair, fromConstPair, Lorentz.preCoMetric_apply_one]

lemma contrMetric_eq_fromPairT {d : ℕ} :
    η d = fromPairT (S := realLorentzTensor d) (c1 := .up) (c2 := .up)
        (Lorentz.preContrMetricVal d) := by
  rw [contrMetric_eq_fromConstPair, fromConstPair, Lorentz.preContrMetric_apply_one]

/-

## Group actions

-/

/-- The tensor `coMetric` is invariant under the action of `LorentzGroup d`. -/
@[simp]
lemma actionT_coMetric {d : ℕ} (g : LorentzGroup d) :
    g • η' d = η' d:= by
  erw [TensorSpecies.metricTensor_invariant]

/-- The tensor `contrMetric` is invariant under the action of `LorentzGroup d`. -/
@[simp]
lemma actionT_contrMetric {d} (g : LorentzGroup d) : g • η d = η d := by
  erw [TensorSpecies.metricTensor_invariant]

/-

## There value with respect to a basis

-/

lemma coMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.down, Color.down]) :
    (Tensor.basis _).repr (coMetric d) b =
    minkowskiMatrix (b 0) (b 1) := by
  rw [coMetric_eq_fromPairT, fromPairT_basis_repr,
    Lorentz.preCoMetricVal_expand_tmul_minkowskiMatrix]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (b 0)] <;>
    simp +contextual [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply]

lemma contrMetric_repr_apply_eq_minkowskiMatrix {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.up, Color.up]) :
    (Tensor.basis _).repr (contrMetric d) b =
    minkowskiMatrix (b 0) (b 1) := by
  rw [contrMetric_eq_fromPairT, fromPairT_basis_repr,
    Lorentz.preContrMetricVal_expand_tmul_minkowskiMatrix]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (b 0)] <;>
    simp +contextual [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply]

end realLorentzTensor
