/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Y3
public import Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.B3
/-!
# The line through B₃ and Y₃

We give properties of lines through `B₃` and `Y₃`. We show that every point on this line
is a solution to the quadratic `lineY₃B₃Charges_quad` and a double point of the cubic
`lineY₃B₃_doublePoint`.

# References

The main reference for the material in this file is:
[Allanach, Madigan and Tooby-Smith][Allanach:2021yjy]

-/

@[expose] public section

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- The line through $Y_3$ and $B_3$ as `LinSols`. -/
def lineY₃B₃Charges (a b : ℚ) : MSSMACC.LinSols := a • Y₃.1.1 + b • B₃.1.1

set_option backward.isDefEq.respectTransparency false in
lemma lineY₃B₃Charges_quad (a b : ℚ) : accQuad (lineY₃B₃Charges a b).val = 0 := by
  change accQuad (a • Y₃.val + b • B₃.val) = 0
  rw [accQuad]
  rw [quadBiLin.toHomogeneousQuad_add]
  rw [quadBiLin.toHomogeneousQuad.map_smul]
  rw [quadBiLin.toHomogeneousQuad.map_smul]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₂]
  erw [quadSol Y₃.1, quadSol B₃.1]
  simp only [mul_zero, add_zero, zero_add, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
  apply Or.inr ∘ Or.inr
  with_unfolding_all rfl

set_option backward.isDefEq.respectTransparency false in
lemma lineY₃B₃Charges_cubic (a b : ℚ) : accCube (lineY₃B₃Charges a b).val = 0 := by
  change accCube (a • Y₃.val + b • B₃.val) = 0
  rw [accCube]
  rw [cubeTriLin.toCubic_add]
  rw [cubeTriLin.toCubic.map_smul]
  rw [cubeTriLin.toCubic.map_smul]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  erw [Y₃.cubicSol, B₃.cubicSol]
  rw [show cubeTriLin Y₃.val Y₃.val B₃.val = 0 by with_unfolding_all rfl]
  rw [show cubeTriLin B₃.val B₃.val Y₃.val = 0 by with_unfolding_all rfl]
  simp

/-- The line through $Y_3$ and $B_3$ as `Sols`. -/
def lineY₃B₃ (a b : ℚ) : MSSMACC.Sols :=
  AnomalyFreeMk' (lineY₃B₃Charges a b) (lineY₃B₃Charges_quad a b) (lineY₃B₃Charges_cubic a b)

set_option backward.isDefEq.respectTransparency false in
lemma doublePoint_Y₃_B₃ (R : MSSMACC.LinSols) :
    cubeTriLin Y₃.val B₃.val R.val = 0 := by
  simp only [cubeTriLin, TriLinearSymm.mk₃_toFun_apply_apply, cubeTriLinToFun,
    MSSMSpecies_numberCharges]
  rw [Fin.sum_univ_three, B₃_val, Y₃_val, B₃AsCharge, Y₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv, Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp only [mul_one, Fin.isValue, toSMSpecies_apply, one_mul, mul_neg, neg_neg, neg_mul, zero_mul,
    add_zero, neg_zero, Hd_apply, Fin.reduceFinMk, Hu_apply]
  have hLin := R.linearSol
  simp only [MSSMACC_numberLinear, MSSMACC_linearACCs, Nat.reduceMul, Fin.isValue,
    Fin.reduceFinMk] at hLin
  have h1 := hLin 1
  have h2 := hLin 2
  have h3 := hLin 3
  simp only [Fin.isValue, Fin.sum_univ_three, Prod.mk_zero_zero, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.mk_one_one] at h1 h2 h3
  linear_combination (norm := ring_nf) -(12 * h2) + 9 * h1 + 3 * h3
  simp only [Nat.reduceMul, Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one, add_sub_cancel_left,
    sub_self]

set_option backward.isDefEq.respectTransparency false in
lemma lineY₃B₃_doublePoint (R : MSSMACC.LinSols) (a b : ℚ) :
    cubeTriLin (lineY₃B₃ a b).val (lineY₃B₃ a b).val R.val = 0 := by
  change cubeTriLin (a • Y₃.val + b • B₃.val) (a • Y₃.val + b • B₃.val) R.val = 0
  rw [cubeTriLin.map_add₂, cubeTriLin.map_add₁, cubeTriLin.map_add₁]
  repeat rw [cubeTriLin.map_smul₂, cubeTriLin.map_smul₁]
  rw [doublePoint_B₃_B₃, doublePoint_Y₃_Y₃, doublePoint_Y₃_B₃]
  rw [cubeTriLin.swap₁, doublePoint_Y₃_B₃]
  simp

end MSSMACC
