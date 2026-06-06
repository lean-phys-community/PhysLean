/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.EMPotential
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic
public import Mathlib.Data.Real.Hom
/-!

# The Field Strength Tensor

## i. Overview

In this module we define the field strength tensor in terms of the electromagnetic potential.

We define a tensor version and a matrix version and prover various properties of these.

## ii. Key results

- `toFieldStrength` : The field strength tensor from an electromagnetic potential.
- `fieldStrengthMatrix` : The field strength matrix from an electromagnetic potential
  (matrix representation of the field strength tensor in the standard basis).

## iii. Table of contents

- A. The field strength tensor
  - A.1. Tensor equalities
  - A.2. Vector equalities
  - A.3. The group action acting on the field strength tensor
  - A.4. Differentiability and smoothness of the field strength tensor
  - A.5. Elements of the field strength tensor in terms of basis
  - A.6. The field strength matrix
    - A.6.1. Differentiability of the field strength matrix
  - A.7. The antisymmetry of the field strength tensor
  - A.8. Equivariance of the field strength matrix
  - A.9. Linearity of the field strength tensor

## iv. References

-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix Tensorial
open Lorentz

attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

TODO "Currently the API for the field strength tensor has the definition
  of `fieldStrengthMatrix`. This is now unneeded, and should be replaced with
  `toField {A.toFieldStrength x| [μ] [ν]}ᵀ` and suitble API around that.
  To undertake this TODO, it is likely easier to start building the API
  around `toField {A.toFieldStrength x| [μ] [ν]}ᵀ` and then remove `fieldStrengthMatrix`
  once the API is in place."

/-!

## A. The field strength tensor

We define the field strength tensor `F^{μν}` in terms of the derivative of the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/
/-- The field strength from an electromagnetic potential, as a tensor `F^{μν}`. -/
noncomputable def toFieldStrength {d} (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d := fun x =>
  Tensorial.toTensor.symm
  (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν) + - (η d | ν ν' ⊗ A.deriv x | ν' μ)}ᵀ)

/-!

### A.1. Tensor equalities

These equalities for the field strength tensor are in
terms of tensor expressions and index notation. In practice,
we don't expect them to be used explicitly. They are useful for proving some
of the API within this module.

-/

lemma toFieldStrength_eq_deriv {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id PermCond.auto {(η d | μ μ' ⊗ A.deriv x | μ' ν)
    + - (η d | ν ν' ⊗ A.deriv x | ν' μ)}ᵀ) := by
  rw [toFieldStrength]

lemma toFieldStrength_eq_tensorDeriv {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id PermCond.auto {(η d | μ μ' ⊗ tensorDeriv A x | μ' ν)
    + - (η d | ν ν' ⊗ tensorDeriv A x | ν' μ)}ᵀ) := by
  rw [toFieldStrength_eq_deriv, deriv_eq_tensorDeriv _ hA]

lemma toFieldStrength_eq_add {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] (PermCond.auto)
      {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  rw [toFieldStrength]
  simp only [map_add, map_neg]
  rw [sub_eq_add_neg]
  apply congrArg₂
  · rfl
  · rw [permT_permT]
    rfl

lemma toFieldStrength_eq_sub_tensorDeriv {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    toFieldStrength A x =
    Tensorial.toTensor.symm (permT id PermCond.auto {η d | μ μ' ⊗ tensorDeriv A x | μ' ν}ᵀ)
    - Tensorial.toTensor.symm (permT ![1, 0] PermCond.auto
    {η d | μ μ' ⊗ tensorDeriv A x | μ' ν}ᵀ) := by
  simp only [toFieldStrength_eq_tensorDeriv hA, map_add, map_neg, sub_eq_add_neg, permT_permT]
  rfl

lemma toTensor_toFieldStrength {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    Tensorial.toTensor (toFieldStrength A x) =
    (permT id (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ)
    - (permT ![1, 0] (PermCond.auto) {(η d | μ μ' ⊗ A.deriv x | μ' ν)}ᵀ) := by
  rw [toFieldStrength_eq_add]
  simp

/-!

### A.2. Vector equalities

These equalities for the field strength tensor are in terms of vector basis.
They match some of the familiar forms one might expect to see the field strength
tensor in.

-/

TODO "Generalize the proof of `toFieldStrength_eq_sum_basis_eval` so that any tensor
  can easily be written as the sum of its components times the basis.
  The likely location for this is in the `Tensorial` module.
  The TODO item with tag: 8285454220008908699 is likely a prerequisite to this."

/-- The statement that `F = F^{μν} eᵤ ⊗ eᵥ` written explicitly, with
  the components extracted via `toField`. -/
lemma toFieldStrength_eq_sum_basis_eval {d} {A : ElectromagneticPotential d} :
    A.toFieldStrength = fun x => ∑ μ, ∑ ν, toField {A.toFieldStrength x| [μ] [ν]}ᵀ •
      Vector.basis μ ⊗ₜ[ℝ] Vector.basis ν := by
  ext x
  /- This is a fairly general proof, so we can generalize our tensor. -/
  generalize (A.toFieldStrength x) = t
  apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext ⟨μ, ν⟩
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
  obtain ⟨t, rfl⟩ := toTensor.symm.surjective t
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · simp only [LinearEquiv.apply_symm_apply, basis_apply, evalT_pure, Pure.evalP, map_smul,
      toField_pure, smul_eq_mul, mul_one, Pure.evalPCoeff]
    change _ = _ * (Lorentz.contrBasis d).repr (Lorentz.contrBasis d (b 1)) ν
    /- Transforming the basis -/
    let e := ComponentIdx.prod.trans ((Vector.indexEquiv (d := d)).prodCongr Vector.indexEquiv)
    simp only [prod_basis_of_map_reindex Vector.basis_eq_map_tensor_basis
        Vector.basis_eq_map_tensor_basis, Basis.repr_reindex, Basis.map_repr,
      LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      Finsupp.mapDomain_equiv_apply, basis_repr_pure, Pure.component_basisVector, Fin.isValue,
      Pure.basisVector, Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
    simp only [Equiv.eq_symm_apply,
      show ComponentIdx.prod.trans ((Vector.indexEquiv (d := d)).prodCongr Vector.indexEquiv) b
        = (b 0, b 1) from rfl]
    by_cases hμ : b 0 = μ <;> by_cases hν : b 1 = ν <;> simp_all
  · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  · simp only [map_smul, h, smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
  · simp only [map_add, h1, h2, Finsupp.coe_add, Pi.add_apply]

/-- The statement that `F = F^{μν} eᵤ ⊗ eᵥ` written explicitly, with
  the components given by `∑ κ, (η μ κ * ∂_ κ A x ν - η ν κ * ∂_ κ A x μ)`. -/
lemma toFieldStrength_eq_sum_basis {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    A.toFieldStrength x = ∑ μ, ∑ ν, (∑ κ, (η μ κ * ∂_ κ A x ν - η ν κ * ∂_ κ A x μ)) •
      Lorentz.Vector.basis μ ⊗ₜ Lorentz.Vector.basis ν := by
  apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext ⟨μ, ν⟩
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
  simp only [prod_basis_of_map_reindex Vector.basis_eq_map_tensor_basis
        Vector.basis_eq_map_tensor_basis,
    toFieldStrength_eq_sub_tensorDeriv hA, self_toTensor_apply, ← deriv_eq_tensorDeriv _ hA,
    map_sub, Basis.repr_reindex, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapDomain_equiv_apply,
    permT_basis_repr_symm_apply, Function.comp_apply, contrT_basis_repr_apply_eq_fin,
    prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix,
    prod_tensor_basis_eq_map_reindex CoVector.basis_eq_map_tensor_basis
        Vector.basis_eq_map_tensor_basis,
    LinearEquiv.symm_apply_apply, Equiv.symm_symm, deriv_basis_repr_apply, Finset.sum_sub_distrib]
  rfl

/-- The statement that `F = F^{μν} eᵤ ⊗ eᵥ` written explicitly, with
  with the components given by `(η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ)`. -/
lemma toFieldStrength_eq_sum_basis_single {d} {A : ElectromagneticPotential d}
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    A.toFieldStrength x = ∑ μ, ∑ ν, (η μ μ * ∂_ μ A x ν - η ν ν * ∂_ ν A x μ) •
      Lorentz.Vector.basis μ ⊗ₜ Lorentz.Vector.basis ν := by
  rw [toFieldStrength_eq_sum_basis hA x]
  apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext ⟨μ, ν⟩
  simp [Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp

TODO "Add a section in this file on the evaluation of the field strength tensor's indices.
  I.e. equalitites related to `toField {A.toFieldStrength x| [μ] [ν]}ᵀ`."

/-!

## A.3. The group action acting on the field strength tensor

We show that the field strength tensor is equivariant under the action of the Lorentz group.
That is transforming the potential and then taking the field strength is the same
as taking the field strength and then transforming the resulting tensor.

-/

set_option backward.isDefEq.respectTransparency false in
lemma toFieldStrength_equivariant {d} (A : ElectromagneticPotential d) (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) (x : SpaceTime d) :
    (Λ • A).toFieldStrength x = Λ • A.toFieldStrength (Λ⁻¹ • x) := by
  rw [toFieldStrength, deriv_equivariant A Λ hf, ← actionT_contrMetric Λ, toFieldStrength]
  simp only [Tensorial.toTensor_smul, prodT_equivariant, contrT_equivariant, map_neg,
    permT_equivariant, map_add, ← Tensorial.smul_toTensor_symm, smul_add, smul_neg]

/-- This lemma expresses the component form of the transformed field strength
tensor: when a Lorentz transformation Λ acts on the potential A, the resulting field strength
tensor's components are given by the standard tensor transformation rule involving the Lorentz
matrix elements Λ^μ_κ and Λ^ν_ρ applied to the original field components. -/
lemma toFieldStrength_action_eq_sum {d} (A : ElectromagneticPotential d) (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) (x : SpaceTime d) :
    (Λ • A).toFieldStrength x = ∑ μ, ∑ ν,
      (∑ κ, ∑ ρ, Λ.1 μ κ * Λ.1 ν ρ * toField {A.toFieldStrength (Λ⁻¹ • x) | [κ] [ρ]}ᵀ) •
      Vector.basis μ ⊗ₜ[ℝ] Vector.basis ν := by
  conv_lhs => rw [toFieldStrength_equivariant A Λ hf x, toFieldStrength_eq_sum_basis_eval]
  change Tensorial.smulLinearMap _ _ = _
  simp only [map_sum, map_smul]
  simp [smulLinearMap, smul_prod, Vector.smul_basis, tmul_sum, sum_tmul,
    Finset.smul_sum, tmul_smul, smul_tmul, smul_smul]
  conv_lhs => enter [2, μ, 2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp [← Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl (fun κ _ => Finset.sum_congr rfl (fun κ _ => by ring))

/-!

## A.4. Differentiability and smoothness of the field strength tensor

-/

@[fun_prop]
lemma differentiable_toFieldStrength {d} {A : ElectromagneticPotential d} (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ A.toFieldStrength := by
  change Differentiable ℝ (A.toFieldStrength ·)
  simp only [toFieldStrength_eq_sum_basis_single (hA.differentiable (by simp))]
  fun_prop

open ContDiff

@[fun_prop]
lemma differentiable_toFieldStrength_of_smooth {d}
    {A : ElectromagneticPotential d} (hA : ContDiff ℝ ∞ A) :
    Differentiable ℝ A.toFieldStrength :=
  differentiable_toFieldStrength (hA.of_le (ENat.LEInfty.out))

@[fun_prop]
lemma contDiff_toFieldStrength {d} {n : WithTop ℕ∞} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n A.toFieldStrength := by
  change ContDiff ℝ n (A.toFieldStrength ·)
  simp only [toFieldStrength_eq_sum_basis_single (hA.differentiable (by simp))]
  fun_prop

/-!

### A.5. Elements of the field strength tensor in terms of basis

-/

TODO "For the electromagnetic field strength, we have lots of lemmas related
  to the components of the field strength tensor in terms of the basis. For example,
  `toTensor_toFieldStrength_basis_repr`, these should be removed. They are used
  downstream, so there use there should be refactored."

lemma toTensor_toFieldStrength_basis_repr {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    ∑ κ, (η (b 0) κ * ∂_ κ A x (b 1) - η (b 1) κ * ∂_ κ A x (b 0)) := by
  rw [toTensor_toFieldStrength]
  simp only [Tensorial.self_toTensor_apply, map_sub,
    Finsupp.coe_sub, Pi.sub_apply]
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [1, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (b 0) (n)
  conv_lhs =>
    enter [1, 2, n, 2]
    rw [toTensor_deriv_basis_repr_apply]
    change ∂_ (n) A x (b 1)
  rw [Tensor.permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, 2, n]
    rw [Tensor.prodT_basis_repr_apply, contrMetric_repr_apply_eq_minkowskiMatrix]
    enter [1]
    change η (b 1) (n)
  conv_lhs =>
    enter [2, 2, n, 2]
    rw [toTensor_deriv_basis_repr_apply]
    change ∂_ (n) A x (b 0)
  rw [← Finset.sum_sub_distrib]

lemma toFieldStrength_tensor_basis_eq_basis {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x)) b =
    (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr (toFieldStrength A x)
      (b 0, b 1) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.Vector.basis (d := d)).reindex Lorentz.Vector.indexEquiv.symm).tensorProduct
          (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
          ((Lorentz.Vector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
          (Lorentz.Vector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
        ext b
        match b with
        | ⟨i, j⟩ =>
        simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply]
  congr 1

lemma toFieldStrength_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) μν =
    ∑ κ, ((η μν.1 κ * ∂_ κ A x μν.2) - η μν.2 κ * ∂_ κ A x μν.1) := by
  match μν with
  | (μ, ν) =>
  trans (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x))
    (fun | 0 => μ | 1 => ν); swap
  · rw [toTensor_toFieldStrength_basis_repr]
  rw [toFieldStrength_tensor_basis_eq_basis]
  rfl

lemma toFieldStrength_basis_repr_apply_eq_single {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) μν =
    ((η μν.1 μν.1 * ∂_ μν.1 A x μν.2) - η μν.2 μν.2 * ∂_ μν.2 A x μν.1) := by
  rw [toFieldStrength_basis_repr_apply]
  simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single μν.1, Finset.sum_eq_single μν.2]
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp
  · intro b _ hb
    rw [minkowskiMatrix.off_diag_zero]
    simp only [zero_mul]
    exact id (Ne.symm hb)
  · simp

/-!

### A.6. The field strength matrix

We define the field strength matrix to be the matrix representation of the field strength tensor
in the standard basis.

This is currently not used as much as it could be.
-/
open ContDiff

/-- The matrix corresponding to the field strength in the standard basis. -/
noncomputable abbrev fieldStrengthMatrix {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :=
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x)

lemma fieldStrengthMatrix_eq {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    A.fieldStrengthMatrix x =
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (A.toFieldStrength x) := by rfl

lemma fieldStrengthMatrix_eq_tensor_basis_repr {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (μ ν : (Fin 1 ⊕ Fin d)) :
    A.fieldStrengthMatrix x (μ, ν) =
    (Tensor.basis _).repr (Tensorial.toTensor (toFieldStrength A x))
    (fun | 0 => μ | 1 => ν) := by
  rw [toFieldStrength_tensor_basis_eq_basis]
  rfl

lemma toFieldStrength_eq_fieldStrengthMatrix {d} (A : ElectromagneticPotential d) :
    toFieldStrength A = fun x => ∑ μ, ∑ ν,
      A.fieldStrengthMatrix x (μ, ν) • (Lorentz.Vector.basis μ) ⊗ₜ (Lorentz.Vector.basis ν) := by
  ext x
  apply (Lorentz.Vector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  simp only [map_sum, map_smul]
  ext κ
  match κ with
  | (μ', ν') =>
  simp [Finsupp.single_apply]
  rfl

/-!

#### A.6.1. Differentiability of the field strength matrix

-/

lemma fieldStrengthMatrix_differentiable {d} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ (A.fieldStrengthMatrix · μν) := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [SpaceTime.differentiable_vector]
    refine Differentiable.clm_apply ?_ ?_
    · exact ((contDiff_succ_iff_fderiv (n := 1)).mp hA).2.2.differentiable
        (by simp)
    · fun_prop
  conv => enter [2, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
    SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  apply Differentiable.sub
  apply Differentiable.const_mul
  · exact diff_partial _ _
  apply Differentiable.const_mul
  · exact diff_partial _ _

lemma fieldStrengthMatrix_differentiable_space {d} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ 2 A) (t : Time) {c : SpeedOfLight} :
    Differentiable ℝ (fun x => A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) μν) := by
  change Differentiable ℝ ((A.fieldStrengthMatrix · μν) ∘ fun x => (toTimeAndSpace c).symm (t, x))
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable hA
  · fun_prop

lemma fieldStrengthMatrix_differentiable_time {d} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ 2 A) (x : Space d) {c : SpeedOfLight} :
    Differentiable ℝ (fun t => A.fieldStrengthMatrix ((toTimeAndSpace c).symm (t, x)) μν) := by
  change Differentiable ℝ ((A.fieldStrengthMatrix · μν) ∘ fun t => (toTimeAndSpace c).symm (t, x))
  refine Differentiable.comp ?_ ?_
  · exact fieldStrengthMatrix_differentiable hA
  · fun_prop

lemma fieldStrengthMatrix_contDiff {d} {n : WithTop ℕ∞} {A : ElectromagneticPotential d}
    {μν} (hA : ContDiff ℝ (n + 1) A) :
    ContDiff ℝ n (A.fieldStrengthMatrix · μν) := by
  conv => enter [3, x]; rw [toFieldStrength_basis_repr_apply_eq_single,
    SpaceTime.deriv_eq, SpaceTime.deriv_eq]
  apply ContDiff.sub
  apply ContDiff.mul
  · fun_prop
  · match μν with
    | (μ, ν) =>
    simp only
    revert ν
    rw [SpaceTime.contDiff_vector]
    apply ContDiff.clm_apply
    · exact ContDiff.fderiv_right (m := n) hA (by rfl)
    · fun_prop
  apply ContDiff.mul
  · fun_prop
  · match μν with
    | (μ, ν) =>
    simp only
    revert μ
    rw [SpaceTime.contDiff_vector]
    apply ContDiff.clm_apply
    · exact ContDiff.fderiv_right (m := n) hA (by rfl)
    · fun_prop

lemma fieldStrengthMatrix_smooth {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (μν) :
    ContDiff ℝ ∞ (A.fieldStrengthMatrix · μν) := by
  apply fieldStrengthMatrix_contDiff
  simpa using hA

/-!

### A.7. The antisymmetry of the field strength tensor

We show that the field strength tensor is antisymmetric.

-/

lemma toFieldStrength_antisymmetric {d} (A : ElectromagneticPotential d) (x : SpaceTime d) :
    {A.toFieldStrength x | μ ν = - (A.toFieldStrength x | ν μ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [toTensor_toFieldStrength_basis_repr]
  rw [permT_basis_repr_symm_apply, map_neg]
  simp only [Nat.reduceAdd, Fin.isValue, Nat.reduceSucc, Finsupp.coe_neg, Pi.neg_apply]
  rw [toTensor_toFieldStrength_basis_repr]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [Fin.isValue, neg_sub]
  rfl

lemma fieldStrengthMatrix_antisymm {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ ν : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix x (μ, ν) = - A.fieldStrengthMatrix x (ν, μ) := by
  rw [toFieldStrength_basis_repr_apply, toFieldStrength_basis_repr_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  simp

@[simp]
lemma fieldStrengthMatrix_diag_eq_zero {d} (A : ElectromagneticPotential d) (x : SpaceTime d)
    (μ : Fin 1 ⊕ Fin d) :
    A.fieldStrengthMatrix x (μ, μ) = 0 := by
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp

/-!

### A.8. Equivariance of the field strength matrix

-/

set_option backward.isDefEq.respectTransparency false in
lemma fieldStrengthMatrix_equivariant {d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d) (hf : Differentiable ℝ A) (x : SpaceTime d)
    (μ : (Fin 1 ⊕ Fin d)) (ν : Fin 1 ⊕ Fin d) :
    fieldStrengthMatrix (Λ • A) x (μ, ν) =
    ∑ κ, ∑ ρ, (Λ.1 μ κ * Λ.1 ν ρ) * A.fieldStrengthMatrix (Λ⁻¹ • x) (κ, ρ) := by
  rw [fieldStrengthMatrix, toFieldStrength_equivariant A Λ hf x]
  conv_rhs =>
    enter [2, κ, 2, ρ]
    rw [fieldStrengthMatrix]
  generalize A.toFieldStrength (Λ⁻¹ • x) = F
  let P (F : Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d) : Prop :=
    ((Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (Λ • F)) (μ, ν) =
    ∑ κ, ∑ ρ, Λ.1 μ κ * Λ.1 ν ρ *
    ((Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr F) (κ, ρ)
  change P F
  apply TensorProduct.induction_on
  · simp [P]
  · intro x y
    dsimp [P]
    rw [Tensorial.smul_prod]
    simp only [Basis.tensorProduct_repr_tmul_apply, Lorentz.Vector.basis_repr_apply,
      Lorentz.CoVector.basis_repr_apply, smul_eq_mul]
    rw [Lorentz.Vector.smul_eq_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl (fun κ _ => ?_)
    rw [Lorentz.Vector.smul_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl (fun ρ _ => ?_)
    ring
  · intro F1 F2 h1 h2
    simp [P, h1, h2]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl (fun κ _ => ?_)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl (fun ρ _ => ?_)
    ring

/-!

### A.9. Linearity of the field strength tensor

We show that the field strength tensor is linear in the potential.

-/

set_option backward.isDefEq.respectTransparency false in
lemma toFieldStrength_add {d} (A1 A2 : ElectromagneticPotential d)
    (x : SpaceTime d) (hA1 : Differentiable ℝ A1) (hA2 : Differentiable ℝ A2) :
    toFieldStrength (A1 + A2) x = toFieldStrength A1 x + toFieldStrength A2 x := by
  apply (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext μν
  simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  repeat rw [toFieldStrength_basis_repr_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  repeat rw [SpaceTime.deriv_eq]
  simp only [add_val]
  rw [fderiv_add]
  simp only [ContinuousLinearMap.add_apply, Lorentz.Vector.apply_add]
  ring
  · exact hA1.differentiableAt
  · exact hA2.differentiableAt

set_option backward.isDefEq.respectTransparency false in
lemma fieldStrengthMatrix_add {d} (A1 A2 : ElectromagneticPotential d)
    (x : SpaceTime d) (hA1 : Differentiable ℝ A1) (hA2 : Differentiable ℝ A2) :
    (A1 + A2).fieldStrengthMatrix x =
    A1.fieldStrengthMatrix x + A2.fieldStrengthMatrix x := by
  rw [fieldStrengthMatrix, toFieldStrength_add A1 A2 x hA1 hA2]
  conv_rhs => rw [fieldStrengthMatrix, fieldStrengthMatrix]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma toFieldStrength_smul {d} (c : ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) (hA : Differentiable ℝ A) :
    toFieldStrength (c • A) x = c • toFieldStrength A x := by
  apply (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr.injective
  ext μν
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  repeat rw [toFieldStrength_basis_repr_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  repeat rw [SpaceTime.deriv_eq]
  simp only [smul_val]
  rw [fderiv_const_smul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, Lorentz.Vector.apply_smul]
  ring
  exact hA.differentiableAt

set_option backward.isDefEq.respectTransparency false in
lemma fieldStrengthMatrix_smul {d} (c : ℝ) (A : ElectromagneticPotential d)
    (x : SpaceTime d) (hA : Differentiable ℝ A) :
    (c • A).fieldStrengthMatrix x = c • A.fieldStrengthMatrix x := by
  rw [fieldStrengthMatrix, toFieldStrength_smul c A x hA]
  conv_rhs => rw [fieldStrengthMatrix]
  simp

end ElectromagneticPotential

end Electromagnetism
