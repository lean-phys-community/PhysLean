/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Contraction.Basic
public import Physlib.Relativity.Tensors.ComponentIdx.Contraction
/-!

# Contractions on basis tensors

-/

@[expose] public section

open Module

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

open ComponentIdx

set_option backward.isDefEq.respectTransparency false in
lemma Pure.dropPair_basisVector {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx c) :
    Pure.dropPair i j hij (basisVector c b) =
    basisVector (S := S) (c ∘ Fin.succSuccAbove i j) fun m => b (Fin.succSuccAbove i j m) := by
  funext l
  simp [dropPair, basisVector]

attribute [-simp] LinearEquiv.cast_apply
lemma contrT_basis_repr_apply {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ S.τ (c i) = c j) (t : Tensor S c)
    (φ : ComponentIdx (c ∘ Fin.succSuccAbove i j)) :
    (basis (c ∘ Fin.succSuccAbove i j)).repr (contrT n i j h t) φ =
    ∑ (b' : DropPairSection φ), (basis c).repr t b'.1 *
      (S.contr (c i) (b (c i) (b'.1 i) ⊗ₜ[k] b (S.τ (c i))
      (basisIdxCongr (by rw [h.2]) (b'.1 j)))) := by
  apply induction_on_basis _ _ _ _ t
  · intro b'
    conv_lhs =>
      rw [basis_apply, contrT_pure]
      simp [Pure.contrP, Pure.dropPair_basisVector]
      change if b'.dropPair i j = φ then _ else 0
    split_ifs
    · rename_i h
      subst h
      rw [Finset.sum_eq_single ⟨b', by simp⟩]
      · simp [Pure.contrPCoeff]
        simp [Pure.basisVector]
        congr 2
        generalize_proofs h1 h2
        generalize b' j = bj
        generalize c j = cj at *
        subst h2
        rfl
      · intro b'' _ hb
        simp only [Basis.repr_self]
        apply mul_eq_zero_of_left
        rw [@MonoidAlgebra.single_apply]
        rw [if_neg]
        by_contra hn
        apply hb
        exact Subtype.coe_eq_of_eq_mk (id (Eq.symm hn))
      · simp
    · symm
      apply Finset.sum_eq_zero
      intro b'' hbf
      apply mul_eq_zero_of_left
      simp only [Basis.repr_self]
      rw [@MonoidAlgebra.single_apply]
      rw [if_neg]
      by_contra hn
      obtain ⟨b'', hb''⟩ := b''
      subst hn
      simp [DropPairSection] at hb''
      rename_i _ hb _
      exact hb hb''
  · simp
  · intro r t h1
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [h1, Finset.mul_sum]
    ring_nf
  · intro t1 t2 h1 h2
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    rw [h1, h2, ← Finset.sum_add_distrib]
    congr 1
    funext x
    rw [← add_mul]

lemma contrT_basis_repr_apply_eq_sum_fin {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ S.τ (c i) = c j) (t : Tensor S c)
    (φ : ComponentIdx (c ∘ Fin.succSuccAbove i j)) :
    (basis (c ∘ Fin.succSuccAbove i j)).repr (contrT n i j h t) φ =
    ∑ (x1 : basisIdx (c i)), ∑ (x2 : basisIdx (c j)),
    (basis c).repr t (DropPairSection.ofFinEquiv h.1 φ (x1, x2)).1 *
    ((S.contr (c i))
    (b (c i) x1 ⊗ₜ[k] b (S.τ (c i)) (basisIdxCongr (by rw [h.2]) x2))) := by
  rw [contrT_basis_repr_apply h t φ, ← (DropPairSection.ofFinEquiv h.1 φ).sum_comp,
    Fintype.sum_prod_type]
  simp

lemma contrT_basis {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ S.τ (c i) = c j) (b : ComponentIdx (S := S) c) :
    contrT n i j h (basis c b) =
    Pure.contrPCoeff i j h (Pure.basisVector c b) •
      basis (c ∘ Fin.succSuccAbove i j) (b.dropPair i j) := by
  simp only [basis_apply, contrT_pure, Pure.contrP, Pure.dropPair_basisVector]
  rfl

end Tensor

end TensorSpecies
