/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Contraction.Pure
/-!

# Contractions on tensors

-/

@[expose] public section

namespace TensorSpecies
open Module

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

TODO "docs: The files on contractions of tensors are currently lacking documentation.
  These should be added, mirroring good examples within Physlib."

namespace Tensor
open Fin
/-!

## contrT

-/

open Pure

lemma contrT_decide {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (hx : S.τ (c i) = c j) (hij : i ≠ j := by decide) :
    i ≠ j ∧ S.τ (c i) = c j := by
  apply And.intro hij hx

/-- For `c : Fin (n + 1 + 1) → C`, `i j : Fin (n + 1 + 1)` with dual color, and a tensor
  `t : Tensor S c`, `contrT i j _ t` is the tensor
  formed by contracting the `i`th index of `t`
  with the `j`th index. -/
noncomputable def contrT (n : ℕ) {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
      (hij : i ≠ j ∧ S.τ (c i) = c j) :
    Tensor S c →ₗ[k] Tensor S (c ∘ succSuccAbove i j) :=
  PiTensorProduct.lift (Pure.contrPMultilinear i j hij)

lemma contrT_congr {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j}
    (i' j' : Fin (n + 1 + 1)) (t : S.Tensor c)
    (hii' : i = i' := by decide)
    (hjj' : j = j' := by decide) :
    contrT n i j hij t = permT id (And.intro (Function.bijective_id) (by subst hii' hjj'; simp))
      (contrT n i' j' (by subst hii' hjj'; exact hij) t) := by
  subst hii' hjj'
  simp

@[simp]
lemma contrT_pure {n : ℕ} {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) :
    contrT n i j hij p.toTensor = p.contrP i j hij := by
  simp only [contrT, Pure.toTensor, PiTensorProduct.lift.tprod]
  rfl

@[simp]
lemma contrT_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (g : G)
    (t : Tensor S c) :
    contrT n i j hij (g • t) = g • contrT n i j hij t := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · simp only [actionT_pure, contrT_pure, contrP, contrPCoeff_invariant, dropPair_equivariant,
      actionT_smul]
  · simp [ht]
  · simp [ht1, ht2]

lemma contrT_permT {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin (n1 + 1 + 1) → C}
    (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j ∧ S.τ (c1 i) = (c1 j))
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1))
    (hσ : PermCond c c1 σ) (t : Tensor S c) :
    contrT n1 i j hij (permT σ hσ t) = permT _ (hσ.succSuccAbove i j hij.1)
      (contrT n (σ i) (σ j) (by simp [hσ.2, hij, hσ.1.injective.eq_iff]) t) := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · simp only [permT_pure, contrT_pure, contrP, contrPCoeff_permP, dropPair_permP, map_smul]
  · simp_all
  · simp_all

lemma contrT_symm {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j} (t : Tensor S c) :
    contrT n i j hij t = permT id (by simp)
      (contrT n j i ⟨hij.1.symm, by simp [← hij.2]⟩ t) := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · simpa only [contrT_pure] using contrP_symm
  · simp [ht]
  · simp [ht1, ht2]

lemma contrT_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1 ∧ S.τ (c i1) = (c j1))
    (hij2 : i2 ≠ j2 ∧ S.τ (c (succSuccAbove i1 j1 i2)) = (c (succSuccAbove i1 j1 j2)))
    (t : Tensor S c) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    contrT n i2 j2 hij2 (contrT (n + 1 + 1) i1 j1 hij1 t) =
    permT id (PermCond.succSuccAbove_comm i1 j1 i2 j2 hij1.left hij2.left)
      (contrT n i1' j1' (by simp [i1', j1', i2', j2', hij1])
      (contrT (n + 1 + 1) i2' j2' (by simp [i2', j2', hij2]) t)) := by
  induction' t using induction_on_pure with p r t ht t1 t2 ht1 ht2
  · simp only [contrT_pure, contrP, map_smul, permT_pure, smul_smul]
    rw [dropPair_comm, contrPCoeff_mul_dropPair]
  · simp [ht]
  · simp [ht1, ht2]

end Tensor

end TensorSpecies
