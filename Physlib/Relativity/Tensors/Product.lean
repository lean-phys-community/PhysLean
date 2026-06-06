/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Basic
/-!

# The product of tensors

## i. Overview

In this module we define the tensor product of
- index components of tensors,
- pure tensors, and
- tensors.
We prove a number of properties about these products, for example,
permutation of the factors, equivariance, and associativity.

## ii. Key results

- `Pure.prodP` : The tensor product of two pure tensors.
- `prodT` : The tensor product of two tensors.

The following results exist for both `prodP` and `prodT` :
- `prodT_swap` : Swapping the order of the product of two tensors.
- `prodT_permT_left` : Permuting the indices of the left tensor commute with the product.
- `prodT_permT_right` : Permuting the indices of the right tensor commute with the product.
- `prodT_equivariant` : The product of two tensors is equivariant.
- `prodT_assoc` : The product of three tensors is associative.
- `prodT_assoc'` : The product of three tensors is associative in the other direction.

## iii. Table of contents

- A. Products of index components
  - A.1. The product of component indices as an equivalence
- B. Products of pure tensors
  - B.1. Indexing pure tensors by `Fin n1 ⊕ Fin n2` rather than `Fin (n1 + n2)`
  - B.2. The product of two pure tensors
  - B.3. The vectors making up product of two pure tensors
  - B.4. The product of two pure basis vectors
  - B.5. The basis components of the product of two pure tensors
  - B.6. Equivariance of the product of two pure tensors
  - B.7. Product with a tensor with no indices on the right
  - B.8. Swapping the order of the product of two pure tensors
  - B.9. Permuting the indices of the left tensor in a product
  - B.10. Permuting the indices of the right tensor in a product
  - B.11. Associativity of the product of three pure tensors in one direction
  - B.12. Associativity of the product of three pure tensors in the other direction
- C. Products of tensors
  - C.1. Indexing tensors by `Fin n1 ⊕ Fin n2` rather than `Fin (n1 + n2)`
  - C.2. The product of two tensors
  - C.3. The product of two pure tensors as a tensor
  - C.4. The product of basis vectors
  - C.5. The product as an equivalence
  - C.6. Rewriting the basis for the product in terms of the tensor product basis
  - C.7. Equivariance of the product of two tensors
  - C.8. The product with the default tensor with no indices on the right
  - C.9. Swapping the order of the product of two tensors
  - C.10. Permuting the indices of the left tensor in a product
  - C.11. Permuting the indices of the right tensor in a product
  - C.12. Associativity of the product of three tensors in one direction
  - C.13. Associativity of the product of three tensors in the other direction

## iv. References

- arXiv:2411.07667

-/

@[expose] public section

namespace TensorSpecies

namespace Tensor
open Module

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b} {n n' n2 : ℕ} {c : Fin n → C} {c' : Fin n' → C}
    {c2 : Fin n2 → C}

/-!

## A. Products of index components

-/

/-!

### A.1 The product of component indices as an equivalence

-/

/-- The equivalence between `ComponentIdx (Fin.append c c1)` and
  `ComponentIdx c × ComponentIdx c1` formed by products. -/
def ComponentIdx.prod {n1 n2 : ℕ} {c : Fin n1 → C} {c1 : Fin n2 → C} :
    ComponentIdx (S := S) (Fin.append c c1) ≃
    ComponentIdx (S := S) c × ComponentIdx (S := S) c1 where
  toFun p := (fun i => basisIdxCongr (by simp) (p (Fin.castAdd n2 i)),
    fun i => basisIdxCongr (by simp) (p (Fin.natAdd n1 i)))
  invFun p := Fin.addCases (fun i => basisIdxCongr (by simp) (p.1 i))
    (fun i => basisIdxCongr (by simp) (p.2 i))
  left_inv p := by
    ext1 i
    revert i
    simp [Fin.forall_fin_add]
  right_inv p := by simp

/-!

## B. Products of pure tensors

-/

/-!

### B.1. Indexing pure tensors by `Fin n1 ⊕ Fin n2` rather than `Fin (n1 + n2)`

-/

/-!

### B.2. The product of two pure tensors

-/

/-- Given two pure tensors `p1 : Pure S c` and `p2 : Pure S c`, `prodP p p2` is the tensor
  product of those tensors returning an element in
  `Pure S (Sum.elim c c1 ∘ ⇑finSumFinEquiv.symm)`. -/
def Pure.prodP {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) : Pure S (Fin.append c c1) :=
  Fin.addCases (fun i => LinearEquiv.cast (R := k) (by simp) (p1 i))
  (fun i => LinearEquiv.cast (R := k) (by simp) (p2 i))

/-!

### B.3. The vectors making up product of two pure tensors

-/

@[simp]
lemma Pure.prodP_apply_castAdd {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n1) :
    Pure.prodP p1 p2 (Fin.castAdd n2 i) =
    LinearEquiv.cast (R := k) (by simp) (p1 i) := by
  simp [Pure.prodP]

@[simp]
lemma Pure.prodP_apply_natAdd {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n2) :
    Pure.prodP p1 p2 (Fin.natAdd n1 i) =
    LinearEquiv.cast (R := k) (by simp) (p2 i) := by
  simp [Pure.prodP]

lemma Pure.prodP_apply_finSumFinEquiv {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n1 ⊕ Fin n2) :
    Pure.prodP p1 p2 (finSumFinEquiv i) =
    match i with
    | Sum.inl i => LinearEquiv.cast (R := k) (by simp) (p1 i)
    | Sum.inr i => LinearEquiv.cast (R := k) (by simp) (p2 i) := by
  rw [Pure.prodP]
  match i with
  | Sum.inl i =>
    simp only [finSumFinEquiv_apply_left, LinearEquiv.cast_apply, Fin.addCases_left]
    rfl
  | Sum.inr i =>
    simp only [finSumFinEquiv_apply_right, LinearEquiv.cast_apply, Fin.addCases_right]
    rfl

/-!

### B.4. The product of two pure basis vectors

-/

lemma Pure.prodP_basisVector {n n1 : ℕ} {c : Fin n → C} {c1 : Fin n1 → C}
    (φ : ComponentIdx c) (φ1 : ComponentIdx (S := S) c1) :
    Pure.prodP (Pure.basisVector c φ) (Pure.basisVector c1 φ1) =
    Pure.basisVector _ (ComponentIdx.prod.symm (φ, φ1)) := by
  ext i
  revert i
  rw [Fin.forall_fin_add]
  simp only [prodP_apply_castAdd, prodP_apply_natAdd]
  constructor
  · intro i
    symm
    simp only [basisVector, ComponentIdx.prod, Equiv.coe_fn_symm_mk, Fin.addCases_left,
      LinearEquiv.cast_apply]
    rw [basis_congr (c1 := (c i)) (by simp)]
    simp
  · intro i
    symm
    simp only [basisVector, ComponentIdx.prod, Equiv.coe_fn_symm_mk, Fin.addCases_right,
      LinearEquiv.cast_apply]
    rw [basis_congr (c1 := (c1 i)) (by simp)]
    simp
/-!

### B.5. The basis components of the product of two pure tensors

-/

lemma Pure.prodP_component {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (p : Pure S c) (p1 : Pure S c1)
    (φ : ComponentIdx (Fin.append c c1)) :
    (p.prodP p1).component φ = p.component (ComponentIdx.prod φ).1 *
    p1.component (ComponentIdx.prod φ).2 := by
  simp [component]
  rw [← finSumFinEquiv.prod_comp]
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Fintype.prod_sum_type]
  congr
  · funext x
    simp only [prodP_apply_castAdd, LinearEquiv.cast_apply, ComponentIdx.prod, Equiv.coe_fn_mk]
    generalize_proofs h1 h2 h3
    generalize p x = p'
    generalize c x = c' at *
    subst h3
    rfl
  · funext x
    simp only [prodP_apply_natAdd, LinearEquiv.cast_apply, ComponentIdx.prod, Equiv.coe_fn_mk]
    generalize_proofs h1 h2 h3
    generalize p1 x = p1'
    generalize c1 x = c1' at *
    subst h3
    rfl

/-!

### B.6. Equivariance of the product of two pure tensors

-/

@[simp]
lemma Pure.prodP_equivariant {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (g : G) (p : Pure S c) (p1 : Pure S c1) :
    prodP (g • p) (g • p1) = g • prodP p p1 := by
  ext i
  revert i
  rw [Fin.forall_fin_add]
  simp only [actionP_eq, prodP_apply_castAdd, prodP_apply_natAdd]
  constructor
  · intro j
    generalize_proofs h1 h2
    generalize p j = p'
    generalize c j = c' at *
    subst h2
    rfl
  · intro j
    generalize_proofs h1 h2
    generalize p1 j = p1'
    generalize c1 j = c1' at *
    subst h2
    rfl

/-!

### B.7. Product with a tensor with no indices on the right

-/

lemma Pure.prodP_zero_right_permCond {n} {c : Fin n → C}
    {c1 : Fin 0 → C} : PermCond c (Fin.append c c1) id := by
  simp only [Nat.add_zero, PermCond.on_id]
  have P : ∀ (i : Fin (n + 0)), c i = Fin.append c c1 i := by
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right, IsEmpty.forall_iff, and_true]
    simp only [Fin.castAdd_zero, Fin.cast_eq_self, implies_true]
  exact P

lemma Pure.prodP_zero_right {n} {c : Fin n → C}
    {c1 : Fin 0 → C} (p : Pure S c) (p0 : Pure S c1) :
    prodP p p0 = permP id prodP_zero_right_permCond p := by
  ext i
  obtain ⟨j, hi⟩ := finSumFinEquiv.surjective (Fin.cast (by rfl) i : Fin (n + 0))
  simp only [Nat.add_zero, Fin.cast_eq_self] at hi
  subst hi
  rw (transparency := .instances) [prodP_apply_finSumFinEquiv]
  match j with
  | Sum.inl j => rfl
  | Sum.inr j => exact Fin.elim0 j

/-!

### B.8. Swapping the order of the product of two pure tensors

-/

/-- The map between `Fin (n1 + n2)` and `Fin (n2 + n1)` formed by swapping elements. -/
def prodSwapMap (n1 n2 : ℕ) : Fin (n1 + n2) → Fin (n2 + n1) :=
    finSumFinEquiv ∘ Sum.swap ∘ finSumFinEquiv.symm

@[simp]
lemma prodSwapMap_permCond {n1 n2 : ℕ} {c : Fin n1 → C} {c2 : Fin n2 → C} :
    PermCond (Fin.append c c2) (Fin.append c2 c) (prodSwapMap n2 n1) := by
  apply And.intro
  · dsimp only [prodSwapMap]
    refine (Equiv.comp_bijective (Sum.swap ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm Sum.swap).mpr ?_
    exact Function.bijective_iff_has_inverse.mpr ⟨Sum.swap, by simp⟩
  · rw [Fin.forall_fin_add]
    simp [prodSwapMap]

set_option backward.isDefEq.respectTransparency false in
lemma Pure.prodP_swap {n n1} {c : Fin n → C}
    {c1 : Fin n1 → C}
    (p : Pure S c) (p1 : Pure S c1) :
    Pure.prodP p p1 = permP (prodSwapMap n n1) prodSwapMap_permCond (Pure.prodP p1 p) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    simp only [finSumFinEquiv_apply_left, prodP_apply_castAdd, permP]
    rw [← congr_right (p1.prodP p) _ (Fin.natAdd n1 i) (by simp [prodSwapMap])]
    simp
  | Sum.inr i =>
    simp only [finSumFinEquiv_apply_right, prodP_apply_natAdd, permP]
    rw [← congr_right (p1.prodP p) _ (Fin.castAdd n i) (by simp [prodSwapMap])]
    simp

/-!

### B.9. Permuting the indices of the left tensor in a product

-/

/-- Given a map `σ : Fin n → Fin n'`, the induced map `Fin (n + n2) → Fin (n' + n2)`. -/
def prodLeftMap (n2 : ℕ) (σ : Fin n → Fin n') : Fin (n + n2) → Fin (n' + n2) :=
    finSumFinEquiv ∘ Sum.map σ id ∘ finSumFinEquiv.symm

@[simp]
lemma prodLeftMap_id {n2 n: ℕ} :
    prodLeftMap (n := n) n2 id = id := by
  simp [prodLeftMap]

@[simp]
lemma prodLeftMap_permCond {σ : Fin n' → Fin n} (c2 : Fin n2 → C) (h : PermCond c c' σ) :
    PermCond (Fin.append c c2) (Fin.append c' c2) (prodLeftMap n2 σ) := by
  apply And.intro
  · rw [prodLeftMap]
    refine (Equiv.comp_bijective (Sum.map σ id ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm (Sum.map σ id)).mpr ?_
    refine Sum.map_bijective.mpr ?_
    apply And.intro
    · exact h.1
    · exact Function.bijective_id
  · simp [Fin.forall_fin_add, prodLeftMap, h.2]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Pure.prodP_permP_left {n n'} {c : Fin n → C} {c' : Fin n' → C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (p : Pure S c) (p2 : Pure S c2) :
    Pure.prodP (permP σ h p) p2 = permP (prodLeftMap n2 σ)
      (prodLeftMap_permCond c2 h) (Pure.prodP p p2) := by
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    simp only [permP, prodLeftMap]
    simp only [Function.comp_apply]
    have h1 := congr_right (p.prodP p2)
      (finSumFinEquiv (Sum.map σ id (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))))
      (finSumFinEquiv (Sum.inl (σ i)))
      (by simp)
    rw [← h1]
    simp [finSumFinEquiv_apply_left, prodP_apply_castAdd, permP]
  | Sum.inr i =>
    simp only [permP, prodLeftMap]
    simp only [Function.comp_apply]
    have h1 := congr_right (p.prodP p2)
      (finSumFinEquiv (Sum.map σ id (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))))
      (finSumFinEquiv (Sum.inr i))
      (by simp)
    rw [← h1]
    simp

/-!

### B.10. Permuting the indices of the right tensor in a product

-/

/-- Given a map `σ : Fin n → Fin n'`, the induced map `Fin (n2 + n) → Fin (n2 + n')`. -/
def prodRightMap (n2 : ℕ) (σ : Fin n → Fin n') : Fin (n2 + n) → Fin (n2 + n') :=
    finSumFinEquiv ∘ Sum.map id σ ∘ finSumFinEquiv.symm

@[simp]
lemma prodRightMap_id {n2 n: ℕ} :
    prodRightMap (n := n) n2 id = id := by
  simp [prodRightMap]

@[simp]
lemma prodRightMap_permCond {σ : Fin n' → Fin n} (c2 : Fin n2 → C) (h : PermCond c c' σ) :
    PermCond (Fin.append c2 c) (Fin.append c2 c') (prodRightMap n2 σ) := by
  apply And.intro
  · rw [prodRightMap]
    refine (Equiv.comp_bijective (Sum.map id σ ∘ ⇑finSumFinEquiv.symm) finSumFinEquiv).mpr ?_
    refine (Equiv.bijective_comp finSumFinEquiv.symm (Sum.map id σ)).mpr ?_
    refine Sum.map_bijective.mpr ?_
    apply And.intro
    · exact Function.bijective_id
    · exact h.1
  · simp [Fin.forall_fin_add, prodRightMap, h.2]

@[simp]
lemma Pure.prodP_permP_right {n n'} {c : Fin n → C} {c' : Fin n' → C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (p : Pure S c) (p2 : Pure S c2) :
    prodP p2 (permP σ h p) = permP (prodRightMap n2 σ)
      (prodRightMap_permCond c2 h) (Pure.prodP p2 p) := by
  conv_lhs => rw [prodP_swap]
  conv_rhs => rw [prodP_swap]
  simp only [prodP_permP_left, prodSwapMap_permCond, permP_permP]
  apply Pure.permP_congr
  · ext i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp only [prodLeftMap, prodSwapMap, Function.comp_apply, Equiv.symm_apply_apply, prodRightMap]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => rfl
  · rfl

/-!

### B.11. Associativity of the product of three pure tensors in one direction

-/

/-- The map between `Fin (n1 + n2 + n3)` and `Fin (n1 + (n2 + n3))` formed by casting. -/
def prodAssocMap (n1 n2 n3 : ℕ) : Fin (n1 + n2 + n3) → Fin (n1 + (n2 + n3)) :=
    Fin.cast (Nat.add_assoc n1 n2 n3)

@[simp]
lemma prodAssocMap_castAdd_castAdd {n1 n2 n3 : ℕ} (i : Fin n1) :
    prodAssocMap n1 n2 n3 (Fin.castAdd n3 (Fin.castAdd n2 i)) =
    finSumFinEquiv (Sum.inl i) := by
  simp [prodAssocMap, Fin.castAdd]

@[simp]
lemma prodAssocMap_castAdd_natAdd {n1 n2 n3 : ℕ} (i : Fin n2) :
    prodAssocMap n1 n2 n3 (Fin.castAdd n3 (Fin.natAdd n1 i)) =
    finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i))) := by
  simp [prodAssocMap, Fin.castAdd, Fin.ext_iff]

@[simp]
lemma prodAssocMap_natAdd {n1 n2 n3 : ℕ} (i : Fin (n3)) :
    prodAssocMap n1 n2 n3 (Fin.natAdd (n1 + n2) i) =
    finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i))) := by
  simp only [prodAssocMap, finSumFinEquiv_apply_right, Fin.ext_iff, Fin.val_cast, Fin.val_natAdd]
  omega

@[simp]
lemma prodAssocMap_permCond {n1 n2 n3 : ℕ} {c : Fin n1 → C} {c2 : Fin n2 → C}
    {c3 : Fin n3 → C} : PermCond (Fin.append c (Fin.append c2 c3)) (Fin.append (Fin.append c c2) c3)
    (prodAssocMap n1 n2 n3) := by
  apply And.intro
  · simp only [prodAssocMap]
    change Function.Bijective (finCongr (by ring))
    exact (finCongr _).bijective
  · simp [Fin.forall_fin_add]

set_option backward.isDefEq.respectTransparency false in
lemma Pure.prodP_assoc {n n1 n2} {c : Fin n → C}
    {c1 : Fin n1 → C} {c2 : Fin n2 → C}
    (p : Pure S c) (p1 : Pure S c1) (p2 : Pure S c2) :
    prodP (Pure.prodP p p1) p2 =
    permP (prodAssocMap n n1 n2) prodAssocMap_permCond (Pure.prodP p (Pure.prodP p1 p2)) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | Sum.inl i =>
      simp only [finSumFinEquiv_apply_left, prodP_apply_castAdd, permP]
      rw [← congr_right (p.prodP (p1.prodP p2)) _ _ (prodAssocMap_castAdd_castAdd i)]
      simp
    | Sum.inr i =>
      simp only [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left, prodP_apply_castAdd,
        prodP_apply_natAdd, permP]
      rw [← congr_right (p.prodP (p1.prodP p2)) _ _ (prodAssocMap_castAdd_natAdd i)]
      simp
  | Sum.inr i =>
    simp only [finSumFinEquiv_apply_right, prodP_apply_natAdd, permP]
    rw [← congr_right (p.prodP (p1.prodP p2)) _ _ (prodAssocMap_natAdd i)]
    simp

/-!

### B.12. Associativity of the product of three pure tensors in the other direction

-/

/-- The map between `Fin (n1 + (n2 + n3))` and `Fin (n1 + n2 + n3)` formed by casting. -/
def prodAssocMap' (n1 n2 n3 : ℕ) : Fin (n1 + (n2 + n3)) → Fin (n1 + n2 + n3) :=
    Fin.cast (Nat.add_assoc n1 n2 n3).symm

@[simp]
lemma prodAssocMap'_castAdd {n1 n2 n3 : ℕ} (i : Fin n1) :
    prodAssocMap' n1 n2 n3 (Fin.castAdd (n2 + n3) i) =
    finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))) := by
  simp [prodAssocMap', Fin.castAdd]

@[simp]
lemma prodAssocMap'_natAdd_castAdd {n1 n2 n3 : ℕ} (i : Fin n2) :
    prodAssocMap' n1 n2 n3 (Fin.natAdd n1 (Fin.castAdd n3 i)) =
    finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i))) := by
  simp [prodAssocMap', Fin.castAdd, Fin.ext_iff]

@[simp]
lemma prodAssocMap'_natAdd_natAdd {n1 n2 n3 : ℕ} (i : Fin n3) :
    prodAssocMap' n1 n2 n3 (Fin.natAdd n1 (Fin.natAdd n2 i)) =
    finSumFinEquiv (Sum.inr i) := by
  simp only [prodAssocMap', finSumFinEquiv_apply_right, Fin.ext_iff, Fin.val_cast, Fin.val_natAdd]
  omega

@[simp]
lemma prodAssocMap'_permCond {n1 n2 n3 : ℕ} {c : Fin n1 → C} {c2 : Fin n2 → C}
    {c3 : Fin n3 → C} : PermCond
      (Fin.append (Fin.append c c2) c3)
      (Fin.append c (Fin.append c2 c3))
      (prodAssocMap' n1 n2 n3) := by
  apply And.intro
  · simp only [prodAssocMap']
    change Function.Bijective (finCongr (by ring))
    exact (finCongr _).bijective
  · simp [Fin.forall_fin_add]

set_option backward.isDefEq.respectTransparency false in
lemma Pure.prodP_assoc' {n n1 n2} {c : Fin n → C}
    {c1 : Fin n1 → C} {c2 : Fin n2 → C}
    (p : Pure S c) (p1 : Pure S c1) (p2 : Pure S c2) :
    prodP p (prodP p1 p2) =
    permP (prodAssocMap' n n1 n2) (prodAssocMap'_permCond) (prodP (prodP p p1) p2) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  match i with
  | Sum.inl i =>
    simp only [finSumFinEquiv_apply_left, prodP_apply_castAdd, permP]
    rw [← congr_right ((p.prodP p1).prodP p2) _ _ (prodAssocMap'_castAdd i)]
    simp
  | Sum.inr i =>
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | Sum.inl i =>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, prodP_apply_natAdd,
        prodP_apply_castAdd, permP]
      rw [← congr_right ((p.prodP p1).prodP p2) _ _ (prodAssocMap'_natAdd_castAdd i)]
      simp
    | Sum.inr i =>
      simp only [finSumFinEquiv_apply_right, prodP_apply_natAdd, permP]
      rw [← congr_right ((p.prodP p1).prodP p2) _ _ (prodAssocMap'_natAdd_natAdd i)]
      simp

/-!

### B.13. Linearity of the product

-/

attribute [-simp] LinearEquiv.cast_apply

@[simp]
lemma Pure.prodP_update_left {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n1) (x : V (c i)) :
    Pure.prodP (Pure.update p1 i x) p2
    = Pure.update (Pure.prodP p1 p2) (Fin.castAdd n2 i)
      (LinearEquiv.cast (R := k) (by simp) x) := by
  ext i
  revert i
  rw [Fin.forall_fin_add]
  simp only [prodP_apply_castAdd, prodP_apply_natAdd]
  constructor
  · intro j
    generalize_proofs h1 h2 h3
    by_cases h : j = i
    · subst h
      simp
    · rw [update_diff _ _ _ _ (by grind), update_diff _ _ _ _ (by simp; grind)]
      simp
  · intro j
    generalize_proofs h1 h2 h3
    rw [update_diff]
    · simp
    · simp [Fin.ext_iff]
      grind

@[simp]
lemma Pure.prodP_update_right {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n2) (x : V (c1 i)) :
    Pure.prodP p1 (Pure.update p2 i x)
    = Pure.update (Pure.prodP p1 p2) (Fin.natAdd n1 i)
      (LinearEquiv.cast (R := k) (by simp) x) := by
  ext i
  revert i
  rw [Fin.forall_fin_add]
  simp only [prodP_apply_castAdd, prodP_apply_natAdd]
  constructor
  · intro j
    generalize_proofs h1 h2 h3
    rw [update_diff]
    · simp
    · simp [Fin.ext_iff]
      grind
  · intro j
    generalize_proofs h1 h2 h3
    by_cases h : j = i
    · subst h
      simp
    · rw [update_diff _ _ _ _ (by grind), update_diff _ _ _ _ (by simp; grind)]
      simp

lemma Pure.prodP_update_add_toTensor_left {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (p1 : Pure S c) (p2 : Pure S c1) (i : Fin n2) (x y : V (c1 i)) :
    (Pure.prodP p1 (Pure.update p2 i (x + y))).toTensor
    = (Pure.prodP p1 (Pure.update p2 i x)).toTensor
    + (Pure.prodP p1 (Pure.update p2 i y)).toTensor := by simp
/-!

## C. Products of tensors

-/

/-!

### C.2. The product of two tensors

-/
open TensorProduct
/-- The tensor product of two tensors as a bi-linear map from
  `S.Tensor c` and `S.Tensor c1` to `S.Tensor (Fin.append c c1)`. -/
noncomputable def prodT {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C} :
    S.Tensor c →ₗ[k] S.Tensor c1 →ₗ[k] S.Tensor (Fin.append c c1) := by
  refine PiTensorProduct.lift (MultilinearMap.mk' (fun p1 => PiTensorProduct.lift
    (MultilinearMap.mk' (fun p2 => (Pure.prodP p1 p2).toTensor) ?_ ?_)) ?_ ?_)
  · intro p2 i x y
    simp only
    repeat rw [← Pure.update_eq_function_update (S := S)]
    simp
  · intro p2 i r p2'
    simp only
    repeat rw [← Pure.update_eq_function_update (S := S)]
    simp
  · intro p1 i x y
    ext p2
    simp only
    repeat rw [← Pure.update_eq_function_update (S := S)]
    simp
  · intro p1 i r p1'
    ext p2
    simp only
    repeat rw [← Pure.update_eq_function_update (S := S)]
    simp

/-!

### C.3. The product of two pure tensors as a tensor

-/

lemma prodT_pure {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (t : Pure S c) (t1 : Pure S c1) :
    (t.toTensor).prodT (t1.toTensor) = (Pure.prodP t t1).toTensor := by
  simp [prodT, Pure.toTensor]

/-!

### C.4. The product of basis vectors

-/

open TensorProduct

lemma prodT_basis {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (b : ComponentIdx c) (b1 : ComponentIdx (S := S) c1) :
    (basis c b).prodT (basis c1 b1) =
    (Pure.basisVector _ (ComponentIdx.prod.symm (b, b1))).toTensor := by
  rw [basis_apply, basis_apply, prodT_pure]
  congr
  rw [Pure.prodP_basisVector]

/-!

### C.5. The product as an equivalence

-/

set_option synthInstance.maxHeartbeats 0 in
/-- The linear equivalence between `S.Tensor c ⊗[k] S.Tensor c1` and
    `S.Tensor (Fin.append c c1)`. -/
noncomputable def tensorEquivProd {n n2 : ℕ} {c : Fin n → C} {c1 : Fin n2 → C} :
    S.Tensor c ⊗[k] S.Tensor c1 ≃ₗ[k] S.Tensor (Fin.append c c1) where
  toLinearMap := TensorProduct.lift prodT
  invFun := (Tensor.basis (Fin.append c c1)).constr k (fun b =>
    (Tensor.basis c) (ComponentIdx.prod b).1 ⊗ₜ[k]
    (Tensor.basis c1) (ComponentIdx.prod b).2)
  left_inv x := by
    let f : S.Tensor (Fin.append c c1) →ₗ[k]
      S.Tensor c ⊗[k] S.Tensor c1 :=
      (Tensor.basis (Fin.append c c1)).constr k (fun b =>
        (Tensor.basis c) (ComponentIdx.prod b).1 ⊗ₜ[k]
        (Tensor.basis c1) (ComponentIdx.prod b).2)
    let P (x : S.Tensor c ⊗[k] S.Tensor c1) := f (TensorProduct.lift prodT x) = x
    change P x
    apply TensorProduct.induction_on
    · simp [P]
    · intro t1 t2
      apply induction_on_basis (t := t1)
      · intro b1
        · apply induction_on_basis (t := t2)
          intro b2
          dsimp [P]
          rw [prodT_basis]
          simp [f]
          · simp [P]
          · intro r t h
            simp [tmul_smul, P] at *
            rw [h]
          · intro t1 t2 h1 h2
            simp [tmul_add, P] at *
            rw [h1, h2]
      · simp [P]
      · intro r t h
        simp [smul_tmul, P] at *
        rw [h]
      · intro t1 t2 h1 h2
        simp [add_tmul, P] at *
        rw [h1, h2]
    · intro x y h1 h2
      simp [P] at *
      rw [h1, h2]
  right_inv x := by
    simp only [Basis.constr_apply_fintype, Basis.equivFun_apply, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, map_sum, map_smul, lift.tmul]
    conv_rhs => rw [← (basis (Fin.append c c1)).sum_repr x]
    congr
    funext φ
    congr 1
    simp only [prodT_basis, Prod.mk.eta, Equiv.symm_apply_apply]
    exact (basis_apply (Fin.append c c1) φ).symm

/-!

### C.6. Rewriting the basis for the product in terms of the tensor product basis

-/

/-- Rewriting basis for the product in terms of the tensor product basis. -/
lemma basis_prod_eq {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C} :
    basis (S := S) (Fin.append c c1) =
    (((Tensor.basis (S := S) c).tensorProduct (Tensor.basis (S := S) c1)).reindex
    (ComponentIdx.prod.symm)).map tensorEquivProd := by
  ext b
  simp [ComponentIdx.prod, tensorEquivProd]
  rw [prodT_basis]
  rw [← basis_apply]
  congr
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [ComponentIdx.prod]
  match i with
  | Sum.inl i => simp
  | Sum.inr i => simp

lemma prodT_basis_repr_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (t : Tensor S c) (t1 : Tensor S c1)
    (b : ComponentIdx (Fin.append c c1)) :
    (basis (Fin.append c c1)).repr (prodT t t1) b =
    (basis c).repr t (ComponentIdx.prod b).1 *
    (basis c1).repr t1 (ComponentIdx.prod b).2 := by
  apply induction_on_pure (t := t)
  · apply induction_on_pure (t := t1)
    · intro p p1
      rw [prodT_pure]
      rw [basis_repr_pure, basis_repr_pure, basis_repr_pure]
      rw [Pure.prodP_component]
    · intro r t hp p
      simp only [basis_repr_pure, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hp ⊢
      rw [hp]
      ring
    · intro t1 t2 hp1 hp2 p
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, hp1, basis_repr_pure, hp2]
      ring_nf
  · intro r t hp
    simp only [map_smul, LinearMap.smul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hp ⊢
    rw [hp]
    ring
  · intro t1 t2 hp1 hp2
    simp only [map_add, LinearMap.add_apply, Finsupp.coe_add, Pi.add_apply, hp1, hp2]
    ring_nf
/-!

### C.7. Equivariance of the product of two tensors

-/

@[simp]
lemma prodT_equivariant {n1 n2} {c : Fin n1 → C} {c1 : Fin n2 → C}
    (g : G) (t : S.Tensor c) (t1 : S.Tensor c1) :
    prodT (g • t) (g • t1) = g • prodT t t1 := by
  let P (t : S.Tensor c) := prodT (g • t) (g • t1) = g • prodT t t1
  change P t
  apply induction_on_pure
  · intro p
    let P (t1 : S.Tensor c1) := prodT (g • p.toTensor) (g • t1) = g • prodT p.toTensor t1
    change P t1
    apply induction_on_pure
    · intro q
      simp only [P]
      rw [prodT_pure, actionT_pure, actionT_pure, prodT_pure, actionT_pure]
      simp
    · intro r t h1
      simp_all only [actionT_smul, map_smul, P]
    · intro t1 t2 h1 h2
      simp_all only [actionT_add, map_add, P]
  · intro r t h1
    simp_all only [actionT_smul, map_smul, LinearMap.smul_apply, P]
  · intro t1 t2 h1 h2
    simp_all only [actionT_add, map_add, LinearMap.add_apply, P]

/-!

### C.8. The product with the default tensor with no indices on the right

-/

lemma prodT_default_right {n} {c : Fin n → C}
    {c1 : Fin 0 → C} (t : S.Tensor c) :
    prodT t (Pure.toTensor default : S.Tensor c1) =
    permT id (Pure.prodP_zero_right_permCond) t := by
  let P (t : S.Tensor c) := prodT t (Pure.toTensor default : S.Tensor c1)
    = permT id (Pure.prodP_zero_right_permCond) t
  change P t
  apply induction_on_pure
  · intro p
    simp only [Nat.add_zero, P]
    rw (transparency := .instances) [prodT_pure]
    rw [Pure.prodP_zero_right]
    rw [permT_pure]
  · intro r t h1
    simp_all only [map_smul, LinearMap.smul_apply, P]
  · intro t1 t2 h1 h2
    simp_all only [map_add, LinearMap.add_apply, P]

/-!

### C.9. Swapping the order of the product of two tensors

-/

lemma prodT_swap {n n1} {c : Fin n → C}
    {c1 : Fin n1 → C}
    (t : S.Tensor c) (t1 : S.Tensor c1) :
    prodT t t1 = permT (prodSwapMap n n1) (prodSwapMap_permCond) (prodT t1 t) := by
  let P (t : S.Tensor c) := prodT t t1 = permT (prodSwapMap n n1) (prodSwapMap_permCond)
    (prodT t1 t)
  change P t
  apply induction_on_pure
  · intro p
    let P (t1 : S.Tensor c1) := prodT p.toTensor t1 = permT (prodSwapMap n n1)
      (prodSwapMap_permCond) (prodT t1 p.toTensor)
    change P t1
    apply induction_on_pure
    · intro q
      simp only [P]
      rw [prodT_pure, prodT_pure, permT_pure, Pure.prodP_swap]
    · intro r t h1
      simp_all only [map_smul, LinearMap.smul_apply, P]
    · intro t1 t2 h1 h2
      simp_all only [map_add, LinearMap.add_apply, P]
  · intro r t h1
    simp_all only [map_smul, LinearMap.smul_apply, P]
  · intro t1 t2 h1 h2
    simp_all only [map_add, LinearMap.add_apply, P]

/-!

### C.10. Permuting the indices of the left tensor in a product

-/

@[simp]
lemma prodT_permT_left {n n'} {c : Fin n → C} {c' : Fin n' → C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (t : S.Tensor c) (t2 : S.Tensor c2) :
    prodT (permT σ h t) t2 = permT (prodLeftMap n2 σ) (prodLeftMap_permCond c2 h) (prodT t t2) := by
  let P (t : S.Tensor c) := prodT (permT σ h t) t2 =
    permT (prodLeftMap n2 σ) (prodLeftMap_permCond c2 h) (prodT t t2)
  change P t
  apply induction_on_pure
  · intro p
    let P (t2 : S.Tensor c2) := prodT (permT σ h p.toTensor) t2 =
      permT (prodLeftMap n2 σ) (prodLeftMap_permCond c2 h) (prodT p.toTensor t2)
    change P t2
    apply induction_on_pure
    · intro q
      simp only [P]
      rw [prodT_pure, permT_pure, permT_pure, prodT_pure]
      congr
      simp
    · intro r t h1
      simp_all only [map_smul, P]
    · intro t1 t2 h1 h2
      simp_all only [map_add, P]
  · intro r t h1
    simp_all only [map_smul, LinearMap.smul_apply, P]
  · intro t1 t2 h1 h2
    simp_all only [map_add, LinearMap.add_apply, P]

/-!

### C.11. Permuting the indices of the right tensor in a product

-/

@[simp]
lemma prodT_permT_right {n n'} {c : Fin n → C} {c' : Fin n' → C}
    (σ : Fin n' → Fin n) (h : PermCond c c' σ) (t : S.Tensor c) (t2 : S.Tensor c2) :
    prodT t2 (permT σ h t) = permT (prodRightMap n2 σ)
    (prodRightMap_permCond c2 h) (prodT t2 t) := by
  conv_lhs => rw [prodT_swap]
  conv_rhs => rw [prodT_swap]
  simp only [prodT_permT_left, prodSwapMap_permCond, permT_permT]
  apply permT_congr
  · ext i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    simp only [prodLeftMap, prodSwapMap, Function.comp_apply, Equiv.symm_apply_apply, prodRightMap]
    match i with
    | Sum.inl i => rfl
    | Sum.inr i => rfl
  · rfl

/-!

### C.12. Associativity of the product of three tensors in one direction

-/

lemma prodT_assoc {n n1 n2} {c : Fin n → C}
    {c1 : Fin n1 → C} {c2 : Fin n2 → C}
    (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) :
    prodT (prodT t t1) t2 =
    permT (prodAssocMap n n1 n2) prodAssocMap_permCond (prodT t (prodT t1 t2)) := by
  let P (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) := prodT (prodT t t1) t2 =
    permT (prodAssocMap n n1 n2) prodAssocMap_permCond (prodT t (prodT t1 t2))
  let P1 (t : S.Tensor c) := P t t1 t2
  change P1 t
  refine induction_on_pure ?_
    (fun r t h1 => by simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap_permCond, P1, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap_permCond, P1, P]) t
  intro p
  let P2 (t1 : S.Tensor c1) := P p.toTensor t1 t2
  change P2 t1
  refine induction_on_pure ?_
    (fun r t h1 => by
      simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap_permCond, P2, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap_permCond, P2, P]) t1
  intro p1
  let P3 (t2 : S.Tensor c2) := P p.toTensor p1.toTensor t2
  change P3 t2
  refine induction_on_pure ?_
    (fun r t h1 => by
      simp_all only [map_smul, prodAssocMap_permCond, P3, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, prodAssocMap_permCond, P3, P]) t2
  intro p2
  simp only [P3, P,]
  rw [prodT_pure, prodT_pure, prodT_pure, prodT_pure, permT_pure, Pure.prodP_assoc]

/-!

### C.13. Associativity of the product of three tensors in the other direction

-/

lemma prodT_assoc' {n n1 n2} {c : Fin n → C}
    {c1 : Fin n1 → C} {c2 : Fin n2 → C}
    (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) :
    prodT t (prodT t1 t2) =
    permT (prodAssocMap' n n1 n2) (prodAssocMap'_permCond) (prodT (prodT t t1) t2) := by
  let P (t : S.Tensor c) (t1 : S.Tensor c1) (t2 : S.Tensor c2) := prodT t (prodT t1 t2) =
    permT (prodAssocMap' n n1 n2) (prodAssocMap'_permCond) (prodT (prodT t t1) t2)
  let P1 (t : S.Tensor c) := P t t1 t2
  change P1 t
  refine induction_on_pure ?_
    (fun r t h1 => by simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap'_permCond, P1, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap'_permCond, P1, P]) t
  intro p
  let P2 (t1 : S.Tensor c1) := P p.toTensor t1 t2
  change P2 t1
  refine induction_on_pure ?_
    (fun r t h1 => by
      simp_all only [map_smul, LinearMap.smul_apply, prodAssocMap'_permCond, P2, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, LinearMap.add_apply, prodAssocMap'_permCond, P2, P]) t1
  intro p1
  let P3 (t2 : S.Tensor c2) := P p.toTensor p1.toTensor t2
  change P3 t2
  refine induction_on_pure ?_
    (fun r t h1 => by
      simp_all only [map_smul, prodAssocMap'_permCond, P3, P])
    (fun t1 t2 h1 h2 => by
      simp_all only [map_add, prodAssocMap'_permCond, P3, P]) t2
  intro p2
  simp only [P3, P]
  rw [prodT_pure, prodT_pure, prodT_pure, prodT_pure, permT_pure, Pure.prodP_assoc']

open TensorProduct

end Tensor

end TensorSpecies
