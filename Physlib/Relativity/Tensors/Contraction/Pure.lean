/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Basic
/-!

# Contractions on pure tensors

-/

@[expose] public section

namespace TensorSpecies
open Module
variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

/-!

## Pure.contrPCoeff

-/

namespace Pure

/-!

## dropPair

-/
open Fin

set_option linter.unusedVariables false in
/-- Given `i j : Fin (n + 1 + 1)`, `c : Fin (n + 1 + 1) → C` and a pure tensor `p : Pure S c`,
  `dropPair i j _ p` is the tensor formed by dropping the `i`th and `j`th parts of `p`. -/
@[nolint unusedArguments]
def dropPair (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) :
    Pure S (c ∘ succSuccAbove i j) :=
    fun m => p (succSuccAbove i j m)

@[simp]
lemma dropPair_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) (g : G) :
    dropPair i j hij (g • p) = g • dropPair i j hij p := by
  ext m
  simp only [dropPair, actionP_eq]
  rfl

lemma dropPair_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (p : Pure S c) : dropPair i j hij p =
    permP id (by simp) (dropPair j i hij.symm p) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, id_eq]
  refine (congr_right _ _ _ ?_).symm
  rw [succSuccAbove_symm]

lemma dropPair_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (p : Pure S c) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPair i2 j2 hij2 (dropPair i1 j1 hij1 p) =
    permP id (PermCond.succSuccAbove_comm i1 j1 i2 j2 hij1 hij2)
    ((dropPair i1' j1' (by simp [i1', j1', hij1]) (dropPair i2' j2' hi2j2' p))) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, id_eq]
  apply (congr_right _ _ _ ?_).symm
  rw [succSuccAbove_comm_apply]
  · simp [hij1]
  · simp [hij2]

@[simp]
lemma dropPair_update_fst {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (x : V (c i)) :
    dropPair i j hij (p.update i x) = dropPair i j hij p := by
  ext m
  simp only [Function.comp_apply, dropPair, update]
  rw [Function.update_of_ne]
  exact Ne.symm (fst_ne_succSuccAbove_pre i j m)

@[simp]
lemma dropPair_update_snd {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (x : V (c j)) :
    dropPair i j hij (p.update j x) = dropPair i j hij p := by
  rw [dropPair_symm]
  simp only [dropPair_update_fst]
  conv_rhs => rw [dropPair_symm]

@[simp]
lemma dropPair_update_succSuccAbove {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (m : Fin n)
    (x : V (c (succSuccAbove i j m))) :
    dropPair i j hij (p.update (succSuccAbove i j m) x) =
    (dropPair i j hij p).update m x := by
  ext m'
  simp only [Function.comp_apply, dropPair, update]
  by_cases h : m' = m
  · subst h
    simp
  · rw [Function.update_of_ne, Function.update_of_ne]
    · rfl
    · simp [h]
    · simp [h]

TODO "Prove lemmas relating to the commutation rules of `dropPair` and `prodP`."

@[simp]
lemma dropPair_permP {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin (n1 + 1 + 1) → C} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : PermCond c c1 σ) (p : Pure S c) :
    dropPair i j hij (permP σ hσ p) = permP _ (hσ.succSuccAbove i j hij)
    (dropPair (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij]) p) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, funPredPredAbove]
  apply congr_mid
  · simp
  · simp [hσ.2]
  · simp [hσ.2]

/-!

## Contraction coefficient

-/

/-- Given a pure tensor `p : Pure S c` and a `i j : Fin n`
  corresponding to dual colors in `c`, `contrPCoeff i j _ p` is the
  element of the underlying ring `k` formed by contracting `p i` and `p j`. -/
noncomputable def contrPCoeff {n : ℕ} {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) : k :=
  S.contr (c i) (p i ⊗ₜ (LinearEquiv.cast (R := k) (by simp [hij.2]) (p j)))

attribute [-simp] LinearEquiv.cast_apply

@[simp]
lemma contrPCoeff_permP {n n1 : ℕ} {c : Fin n → C}
    {c1 : Fin n1 → C} (i j : Fin n1) (hij : i ≠ j ∧ S.τ (c1 i) = c1 j)
    (σ : Fin n1 → Fin n) (hσ : PermCond c c1 σ) (p : Pure S c) :
    contrPCoeff i j hij (permP σ hσ p) =
    contrPCoeff (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij, hσ.2]) p := by
  simp only [contrPCoeff, permP]
  generalize_proofs h1 h2 h3 h4 h5
  generalize p (σ j) = pj at *
  generalize p (σ i) = pi at *
  generalize c (σ j) = cj at *
  generalize c (σ i) = ci at *
  subst h2
  subst h4
  rfl

@[simp]
lemma contrPCoeff_update_succSuccAbove {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (m : Fin n)
    (p : Pure S c) (x : V (c (succSuccAbove i j m))) :
    contrPCoeff i j hij (p.update (succSuccAbove i j m) x) =
    contrPCoeff i j hij p := by
  simp only [contrPCoeff]
  congr
  · simp [update]
  · simp [update]

open TensorProduct
@[simp]
lemma contrPCoeff_update_fst_add {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : V (c i)) :
    contrPCoeff i j hij (p.update i (x + y)) =
    contrPCoeff i j hij (p.update i x) + contrPCoeff i j hij (p.update i y) := by
  simp only [contrPCoeff, update_same, add_tmul, map_add]
  repeat rw [Pure.update_diff]
  all_goals grind

@[simp]
lemma contrPCoeff_update_snd_add {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : V (c j)) :
    contrPCoeff i j hij (p.update j (x + y)) =
    contrPCoeff i j hij (p.update j x) + contrPCoeff i j hij (p.update j y) := by
  simp only [contrPCoeff, update_same, tmul_add, map_add]
  repeat rw [Pure.update_diff]
  all_goals grind

@[simp]
lemma contrPCoeff_update_fst_smul {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : V (c i)) :
    contrPCoeff i j hij (p.update i (r • x)) =
    r * contrPCoeff i j hij (p.update i x) := by
  simp only [contrPCoeff, update_same, smul_tmul]
  repeat rw [Pure.update_diff]
  simp only [tmul_smul, map_smul, smul_eq_mul]
  all_goals grind

@[simp]
lemma contrPCoeff_update_snd_smul {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : V (c j)) :
    contrPCoeff i j hij (p.update j (r • x)) =
    r * contrPCoeff i j hij (p.update j x) := by
  simp only [contrPCoeff, update_same, tmul_smul, map_smul]
  repeat rw [Pure.update_diff]
  simp only [smul_eq_mul]
  all_goals grind

lemma contrPCoeff_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (a b : Fin (n + 1 + 1)) (hab : a ≠ b)
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c (succSuccAbove a b i)) = (c (succSuccAbove a b j)))
    (p : Pure S c) : (p.dropPair a b hab).contrPCoeff i j hij =
    p.contrPCoeff (succSuccAbove a b i) (succSuccAbove a b j)
      (by simpa using hij) := by rfl

lemma contrPCoeff_symm {n : ℕ} {c : Fin n → C} {i j : Fin n} {hij : i ≠ j ∧ S.τ (c i) = c j}
    {p : Pure S c} :
    p.contrPCoeff i j hij = p.contrPCoeff j i ⟨hij.1.symm, by simp [← hij.2]⟩ := by
  rw [contrPCoeff, contrPCoeff, S.contr_tmul_symm]
  generalize_proofs h1 h2 h3 h4
  generalize p j = pj at *
  generalize p i = pi at *
  generalize c j = cj at *
  generalize c i = ci at *
  subst h2
  rfl

lemma contrPCoeff_mul_dropPair {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1 ∧ S.τ (c i1) = (c j1))
    (hij2 : i2 ≠ j2 ∧ S.τ (c (succSuccAbove i1 j1 i2)) = (c (succSuccAbove i1 j1 j2)))
    (p : Pure S c) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    (p.contrPCoeff i1 j1 hij1) * (dropPair i1 j1 hij1.1 p).contrPCoeff i2 j2 hij2 =
    (p.contrPCoeff i2' j2' (by simp [i2', j2', hij2])) *
    (dropPair i2' j2' (by simp [i2', j2', hij2]) p).contrPCoeff i1' j1'
      (by simp [i1', j1', hij1]) := by
  simp only [contrPCoeff_dropPair, succSuccAbove_predPredAbove]
  rw [mul_comm]

@[simp]
lemma contrPCoeff_invariant {n : ℕ} {c : Fin n → C} {i j : Fin n}
    {hij : i ≠ j ∧ S.τ (c i) = c j} {p : Pure S c}
    (g : G) : (g • p).contrPCoeff i j hij = p.contrPCoeff i j hij := by
  simp only [contrPCoeff, actionP_eq, Pure.rep_cast]
  generalize_proofs h1 h2
  generalize p j = pj at *
  generalize p i = pi at *
  generalize c i = ci at *
  generalize (LinearEquiv.cast (R := k) h2) pj = pj' at *
  trans (S.contr ci) (((rep ci).tprod (rep (S.τ ci))) g (pi ⊗ₜ[k] pj'))
  · simp
  rw [(S.contr _).isIntertwining]
  simp

/-!

## Contractions

-/

/-- For `c : Fin (n + 1 + 1) → C`, `i j : Fin (n + 1 + 1)` with dual color, and a pure tensor
  `p : Pure S c`, `contrP i j _ p` is the tensor (not pure due to the `n = 0` case)
  formed by contracting the `i`th index of `p`
  with the `j`th index. -/
noncomputable def contrP {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) :
    S.Tensor (c ∘ succSuccAbove i j) :=
  (p.contrPCoeff i j hij) • (p.dropPair i j hij.1).toTensor

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrP_update_add {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j m : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : V (c m)) :
    contrP i j hij (p.update m (x + y)) =
    contrP i j hij (p.update m x) + contrP i j hij (p.update m y) := by
  rcases eq_or_exists_succSuccAbove i j hij.1 m with rfl | rfl | ⟨m', rfl⟩
  · simp [contrP, add_smul]
  · simp [contrP, add_smul]
  · simp [contrP]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma contrP_update_smul {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j m : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : V (c m)) :
    contrP i j hij (p.update m (r • x)) =
    r • contrP i j hij (p.update m x) := by
  rcases eq_or_exists_succSuccAbove i j hij.1 m with rfl | rfl | ⟨m', rfl⟩
  · simp [contrP, smul_smul]
  · simp [contrP, smul_smul]
  · simp [contrP, smul_smul, mul_comm]

@[simp]
lemma contrP_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) (g : G) :
    contrP i j hij (g • p) = g • contrP i j hij p := by
  simp [contrP, contrPCoeff_invariant, dropPair_equivariant, actionT_pure]

lemma contrP_symm {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j} {p : Pure S c} :
    contrP i j hij p = permT id (by simp)
    (contrP j i ⟨hij.1.symm, by simp [← hij.2]⟩ p) := by
  rw [contrP, contrPCoeff_symm, dropPair_symm]
  simp [contrP, permT_pure]

/-!

## contrP as a multilinear map

-/

/-- The multi-linear map formed by contracting a pair of indices of pure tensors. -/
noncomputable def contrPMultilinear {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) :
    MultilinearMap k (fun i => V (c i))
      (S.Tensor (c ∘ succSuccAbove i j))where
  toFun p := contrP i j hij p
  map_update_add' p m x y := by
    change (update p m (x + y)).contrP i j hij = _
    simp only [contrP_update_add]
    rfl
  map_update_smul' p k r y := by
    change (update p k (r • y)).contrP i j hij = _
    rw [Pure.contrP_update_smul]
    rfl

end Pure

end Tensor

end TensorSpecies
