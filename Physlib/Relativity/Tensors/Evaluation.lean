/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Product
/-!

# Evaluation of tensor indices

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

namespace Pure

variable {n : ℕ} {c : Fin (n + 1) → C}

/-!

## The evaluation coefficient.

-/

/-- Given a `i : Fin (n + 1)`, a `b : basisIdx (c i)` and a pure tensor
  `p : Pure S c`, `evalPCoeff i b p` is the `b`th component of `p i`. -/
noncomputable def evalPCoeff (i : Fin (n + 1)) (φ : basisIdx (c i)) (p : Pure S c) : k :=
  (b (c i)).repr (p i) φ

@[simp]
lemma evalPCoeff_update_self (i : Fin (n + 1)) [inst : DecidableEq (Fin (n + 1))]
    (φ : basisIdx (c i)) (p : Pure S c)
    (x : V (c i)) :
    evalPCoeff i φ (p.update i x) = (b (c i)).repr x φ := by
  simp [evalPCoeff]

@[simp]
lemma evalPCoeff_update_succAbove (i : Fin (n + 1)) [inst : DecidableEq (Fin (n + 1))]
    (j : Fin n)
    (φ : basisIdx (c i)) (p : Pure S c)
    (x : V (c (i.succAbove j))) :
    evalPCoeff i φ (p.update (i.succAbove j) x) = evalPCoeff i φ p := by
  simp [evalPCoeff]

lemma evalPCoeff_basisVector (i : Fin (n + 1)) (φ : basisIdx (c i)) (b' : ComponentIdx (S := S) c) :
    evalPCoeff i φ (Pure.basisVector c b') = if b' i = φ then (1 : k) else 0 := by
  simp [evalPCoeff, basisVector, Finsupp.single_apply]

/-!

## Evaluation for a pure tensor.

-/

/-- Given a `i : Fin (n + 1)`, a `φ : basisIdx (c i)` and a pure tensor
  `p : Pure S c`, `evalP i φ p` is the tensor formed by evaluating the `i`th index
  of `p` at `φ`. -/
noncomputable def evalP (i : Fin (n + 1)) (φ : basisIdx (c i)) (p : Pure S c) :
  Tensor S (c ∘ i.succAbove) := evalPCoeff i φ p • (drop p i).toTensor

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma evalP_update_add [inst : DecidableEq (Fin (n + 1))] (i j : Fin (n + 1))
    (φ : basisIdx (c i)) (p : Pure S c)
    (x y: V (c j)) :
    evalP i φ (p.update j (x + y)) =
    evalP i φ (p.update j x) + evalP i φ (p.update j y) := by
  simp only [evalP]
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [add_smul]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma evalP_update_smul [inst : DecidableEq (Fin (n + 1))] (i j : Fin (n + 1))
    (φ : basisIdx (c i)) (p : Pure S c)
    (r : k)
    (x : V (c j)) :
    evalP i φ (p.update j (r • x)) =
    r • evalP i φ (p.update j x) := by
  simp only [evalP]
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [smul_smul]
  · simp [smul_smul, mul_comm]

/-!

## Evaluation for a pure tensor as multilinear map.

-/

/-- The multi-linear map formed by evaluation of an index of pure tensors. -/
noncomputable def evalPMultilinear {n : ℕ} {c : Fin (n + 1)→ C}
    (i : Fin (n + 1)) (φ : basisIdx (c i)) :
    MultilinearMap k (fun i => V (c i))
      (S.Tensor (c ∘ i.succAbove)) where
  toFun p := evalP i φ p
  map_update_add' p m x y := by
    change (update p m (x + y)).evalP i φ = _
    simp only [evalP_update_add]
    rfl
  map_update_smul' p k r y := by
    change (update p k (r • y)).evalP i φ = _
    rw [Pure.evalP_update_smul]
    rfl

end Pure

/-- Given a `i : Fin (n + 1)`, a `φ : Fin (S.repDim (c i))` and a tensor
  `t : Tensor S c`, `evalT i φ t` is the tensor formed by evaluating the `i`th index
  of `t` at `φ`. -/
noncomputable def evalT {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
      (φ : basisIdx (c i)) :
    Tensor S c →ₗ[k] Tensor S (c ∘ i.succAbove) :=
  PiTensorProduct.lift (Pure.evalPMultilinear i φ)

@[simp]
lemma evalT_pure {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
    (φ : basisIdx (c i)) (p : Pure S c) :
    evalT i φ p.toTensor = Pure.evalP i φ p := by
  simp only [evalT, Pure.toTensor]
  change _ = Pure.evalPMultilinear i φ p
  conv_rhs => rw [← PiTensorProduct.lift.tprod]

lemma evalT_basis {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
    (b : ComponentIdx c) (x : basisIdx (c i)) :
    evalT i x (basis (S := S) c b) = if b i = x then basis (c ∘ i.succAbove)
      (fun j => b (i.succAbove j)) else 0 := by
  simp only [basis_apply, evalT_pure, Pure.evalP, Pure.evalPCoeff_basisVector, ite_smul, one_smul,
    zero_smul]
  rfl


TODO "Add lemmas related to the interaction of evalT and permT, prodT and contrT."


attribute [-simp] Matrix.cons_val_zero Matrix.cons_val Fin.succAbove_zero
/-- Evaluating the single-index basis tensor `basis ![c] (single.symm b)` at the index `x`
  yields the field element `1` if `b = x` (transported across `![c] 0 = c`) and `0` otherwise:
  evaluation of a one-index basis tensor is the Kronecker delta. -/
lemma evalT_basis_single {c : C} (b : basisIdx c) (x : basisIdx (![c] 0)) :
    (evalT 0 x (basis (S := S) ![c] (ComponentIdx.single.symm b))).toField =
    if basisIdxCongr (by simp) b =  x then 1 else 0 := by
  rw [evalT_basis]
  simp only [ComponentIdx.single_symm_apply]
  split_ifs
  · exact toField_basis _
  · simp

/-- Basis expansion of a one-index tensor: every `t : Tensor S ![c]` is the sum over basis
  indices `i` of its evaluation coefficient `toField (evalT 0 i t)` times the corresponding
  basis tensor. -/
lemma eq_sum_evalT_of_single_tensor_basis {c : C} (t : Tensor S ![c]) :
    t = ∑ i, toField (evalT 0 i t) • basis ![c] (ComponentIdx.single.symm
      (basisIdxCongr (by simp) i)) := by
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · obtain ⟨i, rfl⟩ := ComponentIdx.single.symm.surjective b
    conv_rhs => enter [2, i]; rw [evalT_basis_single]
    simp
  · simp
  · conv_lhs => rw [h]
    simp [Finset.smul_sum, smul_smul]
  · simp [add_smul, Finset.sum_add_distrib]
    grind

/-- Reconstruction of a tensor from the evaluations of its last index: every `t : Tensor S c`
  is the sum over basis indices `i` of the evaluation `evalT (Fin.last n) i t` tensored with
  the basis covector `basis ![c (Fin.last n)] (single.symm i)`, with the appended index
  permuted back into the last slot. -/
lemma eq_sum_evalT {n : ℕ} {c : Fin (n + 1) → C} (t : Tensor S c) :
    t = ∑ i, permT id (IsReindexing.append_succ_last c) (prodT (evalT (Fin.last n) i t)
      (basis ![c (Fin.last n)] (ComponentIdx.single.symm i)))   := by
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · conv_rhs => enter [2, i]; rw [evalT_basis]
    generalize_proofs h1 h2 h3
    rw [Finset.sum_eq_single (b (Fin.last n))]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ↓reduceIte]
      rw [prodT_basis, basis_apply, permT_pure]
      congr
      funext i
      simp only [Pure.basisVector, Pure.permP_basisVector]
      congr
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [id_eq, ComponentIdx.prod_symm_castAdd, Function.comp_apply]
        erw [basisIdxCongr_apply_apply]
        exact ComponentIdx.congr_right b _ _ (by rw [Fin.succAbove_last]; rfl)
      · simp only [id_eq, ComponentIdx.prod_symm_natAdd, ComponentIdx.single_symm_apply,
          basisIdxCongr_apply_apply]
        erw [basisIdxCongr_apply_apply]
        exact ComponentIdx.congr_right _ _ _ (by fin_cases j; rfl)
    · intro j h1 h1
      rw [if_neg (by grind)]
      simp
    · simp
  · simp
  · conv_lhs => rw [h]
    simp [Finset.smul_sum]
  · simp [Finset.sum_add_distrib]
    grind

/-- Reconstruction of a tensor from the evaluations of its first index: every `t : Tensor S c`
  is the sum over basis indices `i` of the basis covector `basis ![c 0] (single.symm i)` tensored
  with the evaluation `evalT 0 i t`, with the prepended index permuted back into the first slot.
  This is the first-index analogue of `eq_sum_evalT`. -/
lemma eq_sum_evalT_zero {n : ℕ} {c : Fin (n + 1) → C} (t : Tensor S c) :
    t = ∑ i, permT _ (IsReindexing.append_of_first c)
    (prodT (basis ![c 0] (ComponentIdx.single.symm i)) (evalT 0 i t))  := by
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · conv_rhs => enter [2, i]; rw [evalT_basis]
    generalize_proofs h1 h2 h3
    rw [Finset.sum_eq_single (b 0)]
    · simp only [↓reduceIte]
      rw [prodT_basis, basis_apply, permT_pure]
      congr
      funext i
      simp only [Pure.basisVector, Pure.permP_basisVector]
      congr
      refine Fin.cases ?_ ?_ i
      · simp only [ComponentIdx.prod, Equiv.coe_fn_symm_mk, Fin.cast_zero, Fin.addCases,
          ComponentIdx.single_symm_apply, basisIdxCongr_apply_apply]
        exact ComponentIdx.congr_right b 0 0 rfl
      · intro j
        simp only [ComponentIdx.prod, Equiv.coe_fn_symm_mk, Fin.addCases]
        rw [dif_neg (by simp)]
        simp only [eqRec_eq_cast, basisIdxCongr, Equiv.cast_apply, cast_cast]
        symm
        rw [cast_eq_iff_heq]
        congr 1
    · intro j h1 h1
      rw [if_neg (by grind)]
      simp
    · simp
  · simp
  · conv_lhs => rw [h]
    simp [Finset.smul_sum]
  · simp [Finset.sum_add_distrib]
    grind

end Tensor
end TensorSpecies
