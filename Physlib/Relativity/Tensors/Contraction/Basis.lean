/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Contraction.Basic
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

/-!

-/
namespace ComponentIdx

/-- The `ComponentIdx` obtained by dropping two components. -/
def dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (b : ComponentIdx (S := S) c) :
    ComponentIdx (S := S) (c ∘ Fin.succSuccAbove i j) :=
  fun m => b (Fin.succSuccAbove i j m)

/-- Given a coordinate parameter
  `b : Π k, Fin (S.repDim ((c ∘ i.succAbove ∘ j.succAbove) k)))`, the
  coordinate parameter `Π k, Fin (S.repDim (c k))` which map down to `b`. -/
def DropPairSection {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i : Fin (n + 1 + 1)} {j : Fin (n + 1 + 1)}
    (b : ComponentIdx (S := S) (c ∘ Fin.succSuccAbove i j)) :
    Finset (ComponentIdx (S := S) c) :=
  {b' : ComponentIdx c | dropPair i j b' = b}

namespace DropPairSection

lemma mem_iff_apply_succSuccAbove_eq {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)}
    (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (b' : ComponentIdx c) :
    b' ∈ DropPairSection (S := S) b ↔
      ∀ m, b' (Fin.succSuccAbove i j m) = b m := by
  simp only [DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [funext_iff]
  simp [dropPair]

@[simp]
lemma mem_self_of_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)}
    (b : ComponentIdx (c)) :
    b ∈ DropPairSection (S := S) (b.dropPair i j) := by
  simp [DropPairSection]

/-- Given a `b` in `ComponentIdx (c ∘ Fin.succSuccAbove i j))` and
  an `x` in `Fin (S.repDim (c i)) × Fin (S.repDim (c j))`, the corresponding
  coordinate parameter in `ComponentIdx c`. -/
def ofFin {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (S := S) (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    ComponentIdx (S := S) c := fun m =>
  if hi : m = i then basisIdxCongr (by subst hi; rfl) x.1
  else if hj : m = j then basisIdxCongr (by subst hj; rfl) x.2
  else
    basisIdxCongr (by simp)
    (b (Fin.predPredAbove i j hij m (by omega)))

@[simp]
lemma ofFin_apply_fst {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    ofFin (S := S) hij b x i = x.1 := by
  simp [ofFin]

@[simp]
lemma ofFin_apply_snd {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    ofFin (S := S) hij b x j = x.2 := by
  simp [ofFin]
  intro h
  omega

lemma ofFin_mem_succSuccAboveSection {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    ofFin (S := S) hij b x ∈ DropPairSection b := by
  simp only [DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
  ext m
  simp only [ofFin, dropPair, Fin.succSuccAbove_ne_fst, ↓reduceDIte, Fin.succSuccAbove_ne_snd,
    Function.comp_apply]
  symm
  apply ComponentIdx.congr_right
  simp

/-- The equivalence between `ContrSection b` and
  `basisIdx (c i) × basisIdx (c j)`. -/
def ofFinEquiv {n : ℕ} {c : Fin n.succ.succ → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
    (b : ComponentIdx (c ∘ Fin.succSuccAbove i j)) :
    basisIdx (c i) × basisIdx (c j) ≃ DropPairSection (S := S) b where
  invFun b' := ⟨b'.1 i, b'.1 j⟩
  toFun x := ⟨ofFin hij b x, ofFin_mem_succSuccAboveSection hij b x⟩
  right_inv b' := by
    ext m
    simp
    rcases Fin.eq_or_exists_succSuccAbove i j hij m with rfl | rfl | ⟨m, rfl⟩
    · simp
    · simp
    · simp [ofFin]
      obtain ⟨b', hb'⟩ := b'
      simp only [mem_iff_apply_succSuccAbove_eq] at hb'
      simp [hb']
      symm
      apply ComponentIdx.congr_right
      simp
  left_inv x := by
    simp

@[simp]
lemma ofFinEquiv_apply_fst {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    (ofFinEquiv (S := S) hij b x).1 i = x.1 := by
  simp [ofFinEquiv]

@[simp]
lemma ofFinEquiv_apply_snd {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    (ofFinEquiv (S := S) hij b x).1 j = x.2 := by
  simp [ofFinEquiv]

end DropPairSection

end ComponentIdx
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
