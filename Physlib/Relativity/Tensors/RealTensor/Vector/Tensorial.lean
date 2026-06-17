/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
/-!

# Tensorial nature of Lorentz vectors

We define the tensorial instance on `Lorentz.Vector`, and show
prove properties related to the Lorentz group action and the basis.

-/

@[expose] public section


open Module
open Matrix
open MatrixGroups
open Complex
open TensorProduct

noncomputable section

namespace Lorentz
open realLorentzTensor

namespace Vector

open TensorSpecies
open Tensor

/-!

## Tensorial

-/

/-- The equivalence between the type of indices of a Lorentz vector and
  `Fin 1 ⊕ Fin d`. -/
def indexEquiv {d : ℕ} :
    ComponentIdx (S := (realLorentzTensor d)) ![Color.up] ≃ Fin 1 ⊕ Fin d :=
  ComponentIdx.single (S := realLorentzTensor d) (c := Color.up)

instance tensorial {d : ℕ} : Tensorial (realLorentzTensor d) ![.up] (Vector d) where
  toTensor := LinearEquiv.symm <|
    Equiv.toLinearEquiv
    ((Tensor.basis (S := (realLorentzTensor d)) ![.up]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite.trans <|
  (Equiv.piCongrLeft' _ indexEquiv))
    { map_add := fun x y => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, _root_.map_smul]
        rfl}

open Tensorial

lemma toTensor_symm_apply {d : ℕ} (p : ℝT[d, .up]) :
    (toTensor (self := tensorial)).symm p =
    (Equiv.piCongrLeft' _ indexEquiv <|
    Finsupp.equivFunOnFinite <|
    (Tensor.basis (S := (realLorentzTensor d)) _).repr p) := rfl

lemma toTensor_symm_pure {d : ℕ} (p : Pure (realLorentzTensor d) ![.up]) (i : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm p.toTensor i =
    ((Lorentz.contrBasis d).repr (p 0)) (indexEquiv.symm i 0) := by
  rw [toTensor_symm_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
    Equiv.piCongrLeft'_apply, Finsupp.equivFunOnFinite_apply, Fin.isValue]
  rw [Tensor.basis_repr_pure]
  simp only [Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.prod_singleton, cons_val_zero]
  rfl

/-!

## Basis

-/

set_option backward.isDefEq.respectTransparency false in
lemma toTensor_symm_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm (Tensor.basis ![Color.up] (indexEquiv.symm μ)) =
    basis μ := by
  funext i
  simp [Tensor.basis_apply, toTensor_symm_pure, Pure.basisVector, Finsupp.single_apply,
    indexEquiv]

lemma toTensor_basis_eq_tensor_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    toTensor (basis μ) = Tensor.basis ![Color.up] (indexEquiv.symm μ) := by
  rw [← toTensor_symm_basis]
  simp

lemma basis_eq_map_tensor_basis {d} : basis =
    ((Tensor.basis
    (S := realLorentzTensor d) ![Color.up]).map toTensor.symm).reindex indexEquiv := by
  ext μ
  rw [← toTensor_symm_basis]
  simp

lemma tensor_basis_map_eq_basis_reindex {d} :
    (Tensor.basis (S := realLorentzTensor d) ![Color.up]).map toTensor.symm =
    basis.reindex indexEquiv.symm := by
  rw [basis_eq_map_tensor_basis]
  ext μ
  simp

lemma tensor_basis_repr_toTensor_apply {d : ℕ} (p : Vector d) (μ : ComponentIdx ![Color.up]) :
    (Tensor.basis ![Color.up]).repr (toTensor p) μ =
    p (indexEquiv μ) := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearEquiv.apply_symm_apply]
  apply induction_on_pure (t := p)
  · intro p
    rw [Tensor.basis_repr_pure]
    simp only [Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.prod_singleton, cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd]
    rw [toTensor_symm_pure]
    simp
    rfl
  · intro r t h
    simp [h]
  · intro t1 t2 h1 h2
    simp [h1, h2]

/-!

## The action of the Lorentz group

-/

set_option backward.isDefEq.respectTransparency false in
lemma smul_eq_sum {d : ℕ} (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : Vector d) :
    (Λ • p) i = ∑ j, Λ.1 i j * p j := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  rw [smul_toTensor_symm]
  apply induction_on_pure (t := p)
  · intro p
    rw [actionT_pure]
    rw [toTensor_symm_pure]
    conv_lhs =>
      enter [1, 2]
      change Λ.1 *ᵥ (p 0)
    rw [contrBasis_repr_apply]
    conv_lhs => simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, indexEquiv,
      cons_val_zero, Fin.cast_eq_self, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, ContrMod.mulVec_val]
    rw [mulVec_eq_sum]
    simp only [Finset.sum_apply]
    congr
    funext j
    simp only [Fin.isValue, Pi.smul_apply, transpose_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, Nat.succ_eq_add_one, Nat.reduceAdd,
      ComponentIdx.single_symm_apply, basisIdxCongr_apply, mul_eq_mul_left_iff]
    left
    rw [toTensor_symm_pure, contrBasis_repr_apply]
    rfl
  · intro r t h
    simp only [actionT_smul, _root_.map_smul]
    change r * toTensor (self := tensorial).symm (Λ • t) i = _
    rw [h]
    rw [Finset.mul_sum]
    congr
    funext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, apply_smul]
    ring
  · intro t1 t2 h1 h2
    simp only [actionT_add, map_add, h1, h2, apply_add]
    rw [← Finset.sum_add_distrib]
    congr
    funext x
    ring

lemma smul_eq_mulVec {d} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • p = Λ.1 *ᵥ p := by
  funext i
  rw [smul_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]

lemma smul_add {d : ℕ} (Λ : LorentzGroup d) (p q : Vector d) :
    Λ • (p + q) = Λ • p + Λ • q := by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma smul_sub {d : ℕ} (Λ : LorentzGroup d) (p q : Vector d) :
    Λ • (p - q) = Λ • p - Λ • q := by
  rw [smul_eq_mulVec, smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_sub]

set_option backward.isDefEq.respectTransparency false in
lemma smul_zero {d : ℕ} (Λ : LorentzGroup d) :
    Λ • (0 : Vector d) = 0 := by
  rw [smul_eq_mulVec, Matrix.mulVec_zero]

set_option backward.isDefEq.respectTransparency false in
lemma smul_neg {d : ℕ} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • (-p) = - (Λ • p) := by
  rw [smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_neg]

lemma neg_smul {d} (Λ : LorentzGroup d) (p : Vector d) :
    (-Λ) • p = - (Λ • p) := by
  funext i
  rw [smul_eq_sum, neg_apply, smul_eq_sum]
  simp

lemma _root_.LorentzGroup.eq_of_action_vector_eq {d : ℕ}
    {Λ Λ' : LorentzGroup d} (h : ∀ p : Vector d, Λ • p = Λ' • p) :
    Λ = Λ' := by
  apply LorentzGroup.eq_of_mulVec_eq
  simpa only [smul_eq_mulVec] using fun x => h x

/-!

## B. The continuous action of the Lorentz group

-/

/-- The Lorentz action on vectors as a continuous linear map. -/
def actionCLM {d : ℕ} (Λ : LorentzGroup d) :
    Vector d →L[ℝ] Vector d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Λ • v
      map_add' := smul_add Λ
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        funext i
        simp [smul_eq_sum]
        ring_nf
        congr
        rw [Finset.mul_sum]
        congr
        funext j
        ring}

lemma actionCLM_apply {d : ℕ} (Λ : LorentzGroup d) (p : Vector d) :
    actionCLM Λ p = Λ • p := rfl

lemma actionCLM_injective {d : ℕ} (Λ : LorentzGroup d) :
    Function.Injective (actionCLM Λ) := by
  intro x1 x2
  simp [actionCLM_apply]

lemma actionCLM_surjective {d : ℕ} (Λ : LorentzGroup d) :
    Function.Surjective (actionCLM Λ) := by
  intro x1
  use (actionCLM Λ⁻¹) x1
  simp [actionCLM_apply]

set_option backward.isDefEq.respectTransparency false in
lemma smul_basis {d : ℕ} (Λ : LorentzGroup d) (μ : Fin 1 ⊕ Fin d) :
    Λ • basis μ = ∑ ν, Λ.1 ν μ • basis ν := by
  funext i
  rw [smul_eq_sum]
  simp only [basis_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  trans ∑ ν, ((Λ.1 ν μ • basis ν) i)
  · simp
  rw [Fintype.sum_apply]

end Vector

end Lorentz
