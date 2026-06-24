/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Contraction.Basic
public import Physlib.Relativity.Tensors.Contraction.Basis
public import Mathlib.Algebra.Star.Basic

/-!

# Conjugation structure on a tensor species

## i. Overview

Each index of a tensor carries a colour naming the representation it transforms in. A species
already has the variance dual `τ c`, the colour an index must meet to contract. Conjugation adds a
second involution, the conjugate colour `bar c`: the colour an index transforms in after complex
conjugation. A spinor index is the textbook example: complex conjugation sends a left-handed Weyl
spinor to a right-handed one, `(ψ_α)* = ψ̄_α̇`, so `bar` swaps the left- and right-handed colours
while fixing a real vector colour. Variance is untouched, so `bar` commutes with `τ`. In an N=1
chiral sector `bar` swaps chiral and anti-chiral indices.

`conjT` conjugates a tensor at the basis level: `star` each coordinate in the species basis and
place it at the conjugate colour. Reality and Hermiticity are stated through it, a tensor is real
when conjugation fixes it and a metric is Hermitian when conjugating it swaps its two indices.

Conjugation is intrinsic species data, not a detachable add-on: a `ConjTensorSpecies` is a
`TensorSpecies` bundled (`extends`) with the conjugate-colour involution `bar` and the coherence
the recipe needs. `bar c` shares basis labels with `c` (`barIdx_eq`) and the contraction
coefficients survive `star` (`conj_contrComm`), which together make conjugation commute with
contraction. `conjT` is then `conj`-semilinear, involutive, and commutes with contraction; the
last makes reality and Hermiticity compatible with raising and lowering indices.

## ii. Key results

- `ConjTensorSpecies` is a tensor species bundled with its conjugation.
- `ConjTensorSpecies.conjT` is the conjugation of a tensor.
- `ConjTensorSpecies.conjT_conjT` proves that conjugation is an involution.
- `ConjTensorSpecies.conjT_contrT` proves that conjugation commutes with contraction.
- `ConjTensorSpecies.conjT_eq_permT_iff` is the componentwise criterion for `conjT t = permT σ h t'`,
  the workhorse for proving reality and Hermiticity conditions.

## iii. Table of contents

- A. The conjugation structure
- B. Conjugation of tensors
- C. The involution law
- D. Commutation with contraction

-/

@[expose] public section
noncomputable section

open Module TensorSpecies TensorSpecies.Tensor

/-!

## A. The conjugation structure

A `ConjTensorSpecies` bundles a `TensorSpecies` (`extends`) with the conjugation data. Conjugation is
defined at the basis level, where it is "`star` the components" (§B). Four of the new fields are
bookkeeping on colours and index sets, trivial to supply per instance: `bar` (the conjugate-colour
involution), `bar_involution`, `bar_tau` (it commutes with `τ`), and `barIdx_eq` (a colour and its
conjugate share basis labels). The one substantive field is `conj_contrComm`, that the contraction
coefficients are unchanged by `star`; this is what makes conjugation commute with contraction (§D),
and for a real (δ) contraction it is `star δ = δ`.

-/

/-- A tensor species bundled with a conjugation. Beyond the `TensorSpecies` it `extends`, it carries
the conjugate-colour involution `bar`, the index-set identification `barIdx_eq`, and the
contraction-coherence `conj_contrComm`. Also carries `bar_involution` and `bar_tau` (that `bar` is
involutive and commutes with the variance dual). -/
structure ConjTensorSpecies (k : Type) [CommRing k] [StarRing k] (C : Type) (G : Type) [Group G]
    (V : C → Type) [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    (basisIdx : C → Type) [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    (rep : (c : C) → Representation k G (V c)) (b : (c : C) → Basis (basisIdx c) k (V c))
    extends TensorSpecies k C G V basisIdx rep b where
  /-- The conjugate colour: flips holomorphy, preserves variance. -/
  bar : C → C
  /-- `bar` is an involution. -/
  bar_involution : Function.Involutive bar
  /-- `bar` commutes with the variance dual `τ`. -/
  bar_tau : ∀ c, bar (toTensorSpecies.τ c) = toTensorSpecies.τ (bar c)
  /-- Conjugation fixes the index set: the conjugate colour reuses the same basis labels.
  Conjugation conjugates components in an adapted basis; it never permutes labels, so the label
  sets of `c` and `bar c` coincide. -/
  barIdx_eq : ∀ c, basisIdx (bar c) = basisIdx c
  /-- Conjugation is compatible with contraction at the basis level: `star` of the contraction
  coefficient at colour `d` equals the coefficient at the conjugate colour `bar d`, with basis
  labels carried over by `barIdx_eq`. For a real (δ) contraction this is `star δ = δ`. -/
  conj_contrComm : ∀ (d : C) (x₁ : basisIdx d) (x₂ : basisIdx (toTensorSpecies.τ d)),
      star (toTensorSpecies.contr d (b d x₁ ⊗ₜ[k] b (toTensorSpecies.τ d) x₂))
        = toTensorSpecies.contr (bar d) (b (bar d) ((Equiv.cast (barIdx_eq d)).symm x₁) ⊗ₜ[k]
            b (toTensorSpecies.τ (bar d)) (basisIdxCongr (bar_tau d)
              ((Equiv.cast (barIdx_eq (toTensorSpecies.τ d))).symm x₂)))

namespace TensorSpecies

variable {k : Type} [CommRing k] [StarRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

omit [StarRing k] in
/-- `componentMap` is the basis representation `(Tensor.basis c).repr` definitionally; this bridges
the two notations in the contraction and involution proofs below, and in the consuming reality and
Hermiticity proofs. -/
lemma componentMap_eq_repr {n : ℕ} (c : Fin n → C) (t : S.Tensor c)
    (ψ : ComponentIdx (S := S) c) : componentMap c t ψ = (Tensor.basis c).repr t ψ := rfl

omit [StarRing k] in
/-- Two tensors with the same colour sequence are equal when all their components agree. -/
private lemma componentMap_ext {n : ℕ} {c : Fin n → C} {t₁ t₂ : S.Tensor c}
    (h : ∀ b, componentMap c t₁ b = componentMap c t₂ b) : t₁ = t₂ := by
  rw [← ofComponents_componentMap c t₁, ← ofComponents_componentMap c t₂]
  congr 1; funext b; exact h b

end TensorSpecies

namespace ConjTensorSpecies

open Tensor

variable {k : Type} [CommRing k] [StarRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b)

/-!

## B. Conjugation of tensors

We define the conjugation map `conjT` through its action on components, record that it conjugates
components in place (`componentMap_conjT`), and show it is `conj`-semilinear and additive.

-/

/-- Reindex component labels of `bar ∘ c` back to `c`, slotwise via the cast `barIdx_eq`. -/
def componentReindex {n : ℕ} (c : Fin n → C) :
    ComponentIdx (S := S.toTensorSpecies) (S.bar ∘ c) ≃ ComponentIdx (S := S.toTensorSpecies) c :=
  Equiv.piCongrRight fun i => Equiv.cast (S.barIdx_eq (c i))

/-- Conjugation of a tensor: conjugate the components and reindex the basis to the conjugate
colours. `conj`-semilinear by construction (see `conjT_smul`). -/
def conjT {n : ℕ} {c : Fin n → C} (t : S.Tensor c) : S.Tensor (S.bar ∘ c) :=
  ofComponents (S.bar ∘ c)
    (fun b => star (componentMap c t (S.componentReindex c b)))

/-- Components of a conjugated tensor: the `star` of the original components, reindexed. -/
@[simp] lemma componentMap_conjT {n : ℕ} {c : Fin n → C} (t : S.Tensor c)
    (b : ComponentIdx (S := S.toTensorSpecies) (S.bar ∘ c)) :
    componentMap (S.bar ∘ c) (S.conjT t) b
      = star (componentMap c t (S.componentReindex c b)) := by
  simp only [conjT, componentMap_ofComponents]

/-- Conjugation is semilinear: scalar multiplication pulls out as `star r`. -/
@[simp] lemma conjT_smul {n : ℕ} {c : Fin n → C} (r : k) (t : S.Tensor c) :
    S.conjT (r • t) = star r • S.conjT t := by
  apply TensorSpecies.componentMap_ext
  intro b
  simp only [componentMap_conjT, map_smul, Pi.smul_apply, smul_eq_mul, star_mul']

/-- Conjugation is additive. -/
@[simp] lemma conjT_add {n : ℕ} {c : Fin n → C} (t₁ t₂ : S.Tensor c) :
    S.conjT (t₁ + t₂) = S.conjT t₁ + S.conjT t₂ := by
  apply TensorSpecies.componentMap_ext
  intro b
  simp only [componentMap_conjT, map_add, Pi.add_apply, star_add]

/-- Componentwise criterion for `conjT t = permT σ h t'`. The conjugate of `t` equals the
recolouring `permT σ h t'` exactly when, at every component, the `star`-conjugated reindexed
component of `t` matches the corresponding component of `permT σ h t'`. This packages the
`componentMap_conjT` expansion and the `repr`/`componentMap` bridge that the reality and Hermiticity
proofs downstream would otherwise repeat by hand; the caller is left only with the species-specific
permutation bookkeeping on the right-hand side. -/
lemma conjT_eq_permT_iff {n m : ℕ} {c : Fin n → C} {c' : Fin m → C}
    {σ : Fin n → Fin m} (h : PermCond c' (S.bar ∘ c) σ)
    (t : S.Tensor c) (t' : S.Tensor c') :
    S.conjT t = permT σ h t' ↔
      ∀ φ : ComponentIdx (S := S.toTensorSpecies) (S.bar ∘ c),
        star (componentMap c t (S.componentReindex c φ))
          = (Tensor.basis (S.bar ∘ c)).repr (permT σ h t') φ := by
  constructor
  · intro H φ
    rw [← H, ← componentMap_eq_repr, componentMap_conjT]
  · intro H
    apply TensorSpecies.componentMap_ext
    intro φ
    rw [componentMap_conjT]
    exact H φ

/-!

## C. The involution law

We prove `conjT_conjT`: conjugating a tensor twice returns it, up to the identity recolouring
`bar ∘ bar ∘ c = c`. The supporting lemmas reconcile the iterated basis-label casts.

-/

/-- Undoing the two cast reindexings (at `bar c` then at `c`) on a label of the doubly-conjugated
colour returns the `bar_involution` cast. Free from `barIdx_eq` by `cast_cast` + proof
irrelevance, with no coherence field needed. -/
private lemma barIdx_involutive_symm (c : C) (y : basisIdx (S.bar (S.bar c))) :
    Equiv.cast (S.barIdx_eq c) (Equiv.cast (S.barIdx_eq (S.bar c)) y)
      = basisIdxCongr (S.bar_involution c) y := by
  simp only [basisIdxCongr, Equiv.cast_apply, cast_cast]

/-- The identity permutation satisfies `PermCond` from `c` to `bar ∘ bar ∘ c`, as `bar` is an
involution. -/
lemma permCond_bar_bar {n : ℕ} (c : Fin n → C) :
    PermCond c (S.bar ∘ S.bar ∘ c) (id : Fin n → Fin n) :=
  ⟨Function.bijective_id, fun i => (S.bar_involution (c i)).symm⟩

/-- Conjugation is an involution: conjugating twice returns the original tensor, up to the
`bar_involution` recolouring (the identity permutation `permT`). -/
lemma conjT_conjT {n : ℕ} {c : Fin n → C} (t : S.Tensor c) :
    S.conjT (S.conjT t)
      = permT id (S.permCond_bar_bar c) t := by
  apply TensorSpecies.componentMap_ext
  intro φ
  rw [componentMap_conjT, componentMap_conjT, star_star]
  rw [componentMap_eq_repr (S.bar ∘ S.bar ∘ c), permT_basis_repr_symm_apply,
    ← componentMap_eq_repr c]
  refine congrArg (fun ψ => (componentMap c) t ψ) ?_
  funext i
  have hinv : (PermCond.inv id (S.permCond_bar_bar c)) i = i :=
    PermCond.inv_apply_apply id _ i
  show Equiv.cast (S.barIdx_eq (c i)) (Equiv.cast (S.barIdx_eq (S.bar (c i))) (φ i)) = _
  rw [S.barIdx_involutive_symm]
  exact basisIdxCongr_heq_arg _ _ (by rw [hinv]; exact HEq.rfl)

/-!

## D. Commutation with contraction

We prove `conjT_contrT`: conjugation commutes with contracting two dual-coloured slots. The
contraction expands as a sum over the contracted index pair, and `conj_contrComm` matches the
conjugated coefficients to those on the `bar`-images.

-/

/-- Slots with dual colour in `c` have dual colour in `bar ∘ c`, as `bar` commutes with `τ`. -/
lemma contrCond_bar {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ S.τ (c i) = c j) :
    i ≠ j ∧ S.τ ((S.bar ∘ c) i) = (S.bar ∘ c) j :=
  ⟨h.1, by rw [Function.comp_apply, Function.comp_apply, ← S.bar_tau, h.2]⟩

/-- Conjugation commutes with contraction: conjugating a contracted tensor equals contracting the
conjugate on the `bar`-images of the same two slots. -/
lemma conjT_contrT {n : ℕ} {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (h : i ≠ j ∧ S.τ (c i) = c j) (t : S.Tensor c) :
    S.conjT (contrT n i j h t)
      = contrT n i j (S.contrCond_bar h) (S.conjT t) := by
  apply TensorSpecies.componentMap_ext
  intro φ
  rw [componentMap_conjT, componentMap_eq_repr, Tensor.contrT_basis_repr_apply]
  have hrhs := Tensor.contrT_basis_repr_apply (S := S.toTensorSpecies) (c := S.bar ∘ c)
    (i := i) (j := j) (S.contrCond_bar h) (S.conjT t) φ
  rw [componentMap_eq_repr]
  refine Eq.trans ?_ hrhs.symm
  rw [star_sum]
  -- `componentReindex` carries the `bar`-side contraction section onto the `c`-side one: it
  -- commutes with `dropPair` definitionally, so the section bijection is just `subtypeEquiv`.
  have hmem : ∀ a : ComponentIdx (S := S.toTensorSpecies) (S.bar ∘ c),
      a ∈ ComponentIdx.DropPairSection φ ↔
        S.componentReindex c a ∈
          ComponentIdx.DropPairSection (S.componentReindex (c ∘ i.succSuccAbove j) φ) := by
    intro a
    simp only [ComponentIdx.DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Equiv.apply_eq_iff_eq (S.componentReindex (c ∘ i.succSuccAbove j))).symm
  refine (Finset.sum_equiv (Equiv.subtypeEquiv (S.componentReindex c) hmem)
    (fun _ => by simp) ?_).symm
  intro b'' _
  simp only [Equiv.subtypeEquiv_apply]
  rw [← componentMap_eq_repr (S.bar ∘ c), componentMap_conjT, componentMap_eq_repr c t,
    star_mul']
  congr 1
  rw [S.conj_contrComm (c i) ((S.componentReindex c b''.1) i)
        (basisIdxCongr (by rw [h.2]) ((S.componentReindex c b''.1) j)),
    show (S.componentReindex c b''.1) i = Equiv.cast (S.barIdx_eq (c i)) (b''.1 i) from rfl,
    show (S.componentReindex c b''.1) j = Equiv.cast (S.barIdx_eq (c j)) (b''.1 j) from rfl,
    Equiv.symm_apply_apply]
  congr 2
  exact congrArg (b (S.τ (S.bar (c i)))) (basisIdxCongr_heq_arg _ _
    (HEq.symm ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)))))

end ConjTensorSpecies
end
end
