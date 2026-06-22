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

The components of a complex tensor are complex numbers, and conjugating them is a basic operation.
On a tensor it does more than conjugate numbers: each index carries a colour naming the
representation it transforms in, and conjugation sends every index to the conjugate
representation. For spinor colours this swaps, for instance, left- and right-handed indices.

Reality and Hermiticity conditions are expressed through this operation: a tensor is real when
conjugation fixes it, and a metric is Hermitian when conjugating it swaps its two indices. We
package conjugation abstractly so these conditions can be stated once for any tensor species.

There are two places one could define this conjugation: on the abstract tensor, or on its
components. At the tensor level it would be an antilinear map on `S.Tensor c`, built through the
tensor product without reference to a basis. At the basis level it is just "`star` the components":
read a tensor's coordinates in the basis the species carries, conjugate each, and reinterpret them
at the conjugate colours. We take the basis level. It is the concrete, direct one, and the
basis-free construction, though possible, is heavier machinery that buys nothing here.
Conjugate-linearity, `conjT (r • t) = star r • conjT t`, then follows for free from `star`.

The rest of `Conj` is what that recipe needs to be well-defined. A component sits at a basis label
of a colour `c`; after `star`-ing it we file it at the same label of the conjugate colour `bar c`,
so `bar c` must carry the same labels as `c` (`barIdx_eq`). Contraction sums products of components
weighted by the contraction coefficients, so for `star`-ing the components to commute with
contracting them, those coefficients must be unchanged by conjugation (`conj_contrComm`); for the
Kronecker-δ contractions here that is immediate. From this we build the `conj`-semilinear map
`conjT` and prove its two laws: conjugation is an involution, and it commutes with contraction. The
second makes reality and Hermiticity compatible with raising and lowering indices, which are
contractions against a metric.

## ii. Key results

- `Conj` is the conjugation structure on a tensor species.
- `Conj.conjT` is the conjugation of a tensor.
- `Conj.conjT_conjT` proves that conjugation is an involution.
- `Conj.conjT_contrT` proves that conjugation commutes with contraction.
- `Conj.conjT_eq_permT_iff` is the componentwise criterion for `conjT t = permT σ h t'`, the
  workhorse for proving reality and Hermiticity conditions.

## iii. Table of contents

- A. The conjugation structure
- B. Conjugation of tensors
- C. The involution law
- D. Commutation with contraction

-/

@[expose] public section
noncomputable section

namespace TensorSpecies

open Module Tensor

variable {k : Type} [CommRing k] [StarRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}

/-!

## A. The conjugation structure

We define `Conj`. Conjugation could be put directly on `S.Tensor c` as an antilinear map built
through the tensor product, but we define it at the basis level instead, where it is simply
"`star` the components" (§B) in the basis the species carries; the coordinate definition is the
concrete one. The structure records what that recipe needs. Beyond `bar` (which colour is the conjugate of which) and its compatibility with
the variance dual `τ`, it carries `barIdx_eq`, that a colour and its conjugate share basis labels so
a `star`-ed component can be filed at the same label of the conjugate colour, and `conj_contrComm`,
that the contraction coefficients are unchanged by `star`, the single condition that makes
conjugation commute with contraction. Only `conj_contrComm` touches the scalars; the others are
bookkeeping on colours.

-/

/-- A conjugation on a tensor species. Carries the conjugate-colour involution `bar`, the
index-set identification `barIdx_eq`, and the contraction-coherence `conj_contrComm`. Also carries
`bar_involution` and `bar_tau` (that `bar` is involutive and commutes with the variance dual). -/
structure Conj (S : TensorSpecies k C G V basisIdx rep b) where
  /-- The conjugate colour: flips holomorphy, preserves variance. -/
  bar : C → C
  /-- `bar` is an involution. -/
  bar_involution : Function.Involutive bar
  /-- `bar` commutes with the variance dual `τ`. -/
  bar_tau : ∀ c, bar (S.τ c) = S.τ (bar c)
  /-- Conjugation fixes the index set: the conjugate colour reuses the same basis labels.
  Conjugation conjugates components in an adapted basis; it never permutes labels, so the label
  sets of `c` and `bar c` coincide. -/
  barIdx_eq : ∀ c, basisIdx (bar c) = basisIdx c
  /-- Conjugation is compatible with contraction at the basis level: `star` of the contraction
  coefficient at colour `d` equals the coefficient at the conjugate colour `bar d`, with basis
  labels carried over by `barIdx_eq`. For a real (δ) contraction this is `star δ = δ`. -/
  conj_contrComm : ∀ (d : C) (x₁ : basisIdx d) (x₂ : basisIdx (S.τ d)),
      star (S.contr d (b d x₁ ⊗ₜ[k] b (S.τ d) x₂))
        = S.contr (bar d) (b (bar d) ((Equiv.cast (barIdx_eq d)).symm x₁) ⊗ₜ[k]
            b (S.τ (bar d)) (basisIdxCongr (bar_tau d) ((Equiv.cast (barIdx_eq (S.τ d))).symm x₂)))

variable {S : TensorSpecies k C G V basisIdx rep b} (cj : Conj S)

/-!

## B. Conjugation of tensors

We define the conjugation map `conjT` through its action on components, record that it conjugates
components in place (`componentMap_conjT`), and show it is `conj`-semilinear and additive.

-/

/-- Reindex component labels of `bar ∘ c` back to `c`, slotwise via the cast `barIdx_eq`. -/
def Conj.componentReindex {n : ℕ} (c : Fin n → C) :
    ComponentIdx (S := S) (cj.bar ∘ c) ≃ ComponentIdx (S := S) c :=
  Equiv.piCongrRight fun i => Equiv.cast (cj.barIdx_eq (c i))

/-- Conjugation of a tensor: conjugate the components and reindex the basis to the conjugate
colours. `conj`-semilinear by construction (see `conjT_smul`). -/
def Conj.conjT {n : ℕ} {c : Fin n → C} (t : S.Tensor c) : S.Tensor (cj.bar ∘ c) :=
  ofComponents (cj.bar ∘ c)
    (fun b => star (componentMap c t (cj.componentReindex c b)))

/-- Components of a conjugated tensor: the `star` of the original components, reindexed. -/
@[simp] lemma Conj.componentMap_conjT {n : ℕ} {c : Fin n → C} (t : S.Tensor c)
    (b : ComponentIdx (S := S) (cj.bar ∘ c)) :
    componentMap (cj.bar ∘ c) (cj.conjT t) b
      = star (componentMap c t (cj.componentReindex c b)) := by
  simp only [Conj.conjT, componentMap_ofComponents]

omit [StarRing k] in
/-- `componentMap` is the basis representation `(Tensor.basis c).repr` definitionally; this bridges
the two notations in the contraction and involution proofs below, and in the consuming reality and
Hermiticity proofs. -/
lemma componentMap_eq_repr {n : ℕ} (c : Fin n → C) (t : S.Tensor c)
    (ψ : ComponentIdx (S := S) c) : componentMap c t ψ = (Tensor.basis c).repr t ψ := rfl

omit [StarRing k] in
/-- Two tensors with the same colour sequence are equal when all their components agree. -/
private lemma Conj.componentMap_ext {n : ℕ} {c : Fin n → C} {t₁ t₂ : S.Tensor c}
    (h : ∀ b, componentMap c t₁ b = componentMap c t₂ b) : t₁ = t₂ := by
  rw [← ofComponents_componentMap c t₁, ← ofComponents_componentMap c t₂]
  congr 1; funext b; exact h b

/-- Conjugation is semilinear: scalar multiplication pulls out as `star r`. -/
@[simp] lemma Conj.conjT_smul {n : ℕ} {c : Fin n → C} (r : k) (t : S.Tensor c) :
    cj.conjT (r • t) = star r • cj.conjT t := by
  apply Conj.componentMap_ext
  intro b
  simp only [componentMap_conjT, map_smul, Pi.smul_apply, smul_eq_mul, star_mul']

/-- Conjugation is additive. -/
@[simp] lemma Conj.conjT_add {n : ℕ} {c : Fin n → C} (t₁ t₂ : S.Tensor c) :
    cj.conjT (t₁ + t₂) = cj.conjT t₁ + cj.conjT t₂ := by
  apply Conj.componentMap_ext
  intro b
  simp only [componentMap_conjT, map_add, Pi.add_apply, star_add]

/-- Componentwise criterion for `conjT t = permT σ h t'`. The conjugate of `t` equals the
recolouring `permT σ h t'` exactly when, at every component, the `star`-conjugated reindexed
component of `t` matches the corresponding component of `permT σ h t'`. This packages the
`componentMap_conjT` expansion and the `repr`/`componentMap` bridge that the reality and Hermiticity
proofs downstream would otherwise repeat by hand; the caller is left only with the species-specific
permutation bookkeeping on the right-hand side. -/
lemma Conj.conjT_eq_permT_iff {n m : ℕ} {c : Fin n → C} {c' : Fin m → C}
    {σ : Fin n → Fin m} (h : PermCond c' (cj.bar ∘ c) σ)
    (t : S.Tensor c) (t' : S.Tensor c') :
    cj.conjT t = permT σ h t' ↔
      ∀ φ : ComponentIdx (S := S) (cj.bar ∘ c),
        star (componentMap c t (cj.componentReindex c φ))
          = (Tensor.basis (cj.bar ∘ c)).repr (permT σ h t') φ := by
  constructor
  · intro H φ
    rw [← H, ← componentMap_eq_repr, componentMap_conjT]
  · intro H
    apply Conj.componentMap_ext
    intro φ
    rw [componentMap_conjT]
    exact H φ

/-!

## C. The involution law

We prove `conjT_conjT`: conjugating a tensor twice returns it, up to the identity recolouring
`bar ∘ bar ∘ c = c`. The supporting lemmas reconcile the iterated basis-label casts.

-/

omit [StarRing k] [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)] in
/-- `basisIdxCongr` only depends on its endpoints up to `HEq` of the arguments: equal target
colours and heterogeneously equal labels give equal casts. -/
private lemma basisIdxCongr_heq_arg {c₁ c₂ d : C} (h₁ : c₁ = d) (h₂ : c₂ = d)
    {x : basisIdx c₁} {y : basisIdx c₂} (hxy : HEq x y) :
    basisIdxCongr h₁ x = basisIdxCongr h₂ y := by
  subst h₁; subst h₂; cases hxy; rfl

/-- Undoing the two cast reindexings (at `bar c` then at `c`) on a label of the doubly-conjugated
colour returns the `bar_involution` cast. Free from `barIdx_eq` by `cast_cast` + proof
irrelevance, with no coherence field needed. -/
private lemma Conj.barIdx_involutive_symm (c : C) (y : basisIdx (cj.bar (cj.bar c))) :
    Equiv.cast (cj.barIdx_eq c) (Equiv.cast (cj.barIdx_eq (cj.bar c)) y)
      = basisIdxCongr (cj.bar_involution c) y := by
  simp only [basisIdxCongr, Equiv.cast_apply, cast_cast]

/-- The identity permutation satisfies `PermCond` from `c` to `bar ∘ bar ∘ c`, as `bar` is an
involution. -/
lemma Conj.permCond_bar_bar {n : ℕ} (c : Fin n → C) :
    PermCond c (cj.bar ∘ cj.bar ∘ c) (id : Fin n → Fin n) :=
  ⟨Function.bijective_id, fun i => (cj.bar_involution (c i)).symm⟩

/-- Conjugation is an involution: conjugating twice returns the original tensor, up to the
`bar_involution` recolouring (the identity permutation `permT`). -/
lemma Conj.conjT_conjT {n : ℕ} {c : Fin n → C} (t : S.Tensor c) :
    cj.conjT (cj.conjT t)
      = permT id (cj.permCond_bar_bar c) t := by
  apply Conj.componentMap_ext
  intro φ
  rw [Conj.componentMap_conjT, Conj.componentMap_conjT, star_star]
  rw [componentMap_eq_repr (cj.bar ∘ cj.bar ∘ c), permT_basis_repr_symm_apply,
    ← componentMap_eq_repr c]
  refine congrArg (fun ψ => (componentMap c) t ψ) ?_
  funext i
  have hinv : (PermCond.inv id (cj.permCond_bar_bar c)) i = i :=
    PermCond.inv_apply_apply id _ i
  show Equiv.cast (cj.barIdx_eq (c i)) (Equiv.cast (cj.barIdx_eq (cj.bar (c i))) (φ i)) = _
  rw [cj.barIdx_involutive_symm]
  exact basisIdxCongr_heq_arg _ _ (by rw [hinv]; exact HEq.rfl)

/-!

## D. Commutation with contraction

We prove `conjT_contrT`: conjugation commutes with contracting two dual-coloured slots. The
contraction expands as a sum over the contracted index pair, and `conj_contrComm` matches the
conjugated coefficients to those on the `bar`-images.

-/

/-- Slots with dual colour in `c` have dual colour in `bar ∘ c`, as `bar` commutes with `τ`. -/
lemma Conj.contrCond_bar {n : ℕ} {c : Fin (n + 1 + 1) → C} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ S.τ (c i) = c j) :
    i ≠ j ∧ S.τ ((cj.bar ∘ c) i) = (cj.bar ∘ c) j :=
  ⟨h.1, by rw [Function.comp_apply, Function.comp_apply, ← cj.bar_tau, h.2]⟩

/-- Conjugation commutes with contraction: conjugating a contracted tensor equals contracting the
conjugate on the `bar`-images of the same two slots. -/
lemma Conj.conjT_contrT {n : ℕ} {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (h : i ≠ j ∧ S.τ (c i) = c j) (t : S.Tensor c) :
    cj.conjT (contrT n i j h t)
      = contrT n i j (cj.contrCond_bar h) (cj.conjT t) := by
  apply Conj.componentMap_ext
  intro φ
  rw [Conj.componentMap_conjT, componentMap_eq_repr, Tensor.contrT_basis_repr_apply]
  have hrhs := Tensor.contrT_basis_repr_apply (S := S) (c := cj.bar ∘ c) (i := i) (j := j)
    (cj.contrCond_bar h) (cj.conjT t) φ
  rw [componentMap_eq_repr]
  refine Eq.trans ?_ hrhs.symm
  rw [star_sum]
  -- `componentReindex` carries the `bar`-side contraction section onto the `c`-side one: it
  -- commutes with `dropPair` definitionally, so the section bijection is just `subtypeEquiv`.
  have hmem : ∀ a : ComponentIdx (cj.bar ∘ c),
      a ∈ ComponentIdx.DropPairSection φ ↔
        cj.componentReindex c a ∈
          ComponentIdx.DropPairSection (cj.componentReindex (c ∘ i.succSuccAbove j) φ) := by
    intro a
    simp only [ComponentIdx.DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Equiv.apply_eq_iff_eq (cj.componentReindex (c ∘ i.succSuccAbove j))).symm
  refine (Finset.sum_equiv (Equiv.subtypeEquiv (cj.componentReindex c) hmem)
    (fun _ => by simp) ?_).symm
  intro b'' _
  simp only [Equiv.subtypeEquiv_apply]
  rw [← componentMap_eq_repr (cj.bar ∘ c), Conj.componentMap_conjT, componentMap_eq_repr c t,
    star_mul']
  congr 1
  rw [cj.conj_contrComm (c i) ((cj.componentReindex c b''.1) i)
        (basisIdxCongr (by rw [h.2]) ((cj.componentReindex c b''.1) j)),
    show (cj.componentReindex c b''.1) i = Equiv.cast (cj.barIdx_eq (c i)) (b''.1 i) from rfl,
    show (cj.componentReindex c b''.1) j = Equiv.cast (cj.barIdx_eq (c j)) (b''.1 j) from rfl,
    Equiv.symm_apply_apply]
  congr 2
  exact congrArg (b (S.τ (cj.bar (c i)))) (basisIdxCongr_heq_arg _ _
    (HEq.symm ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)))))

end TensorSpecies
end
end
