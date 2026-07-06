/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Mathematics.KroneckerDelta.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
/-!

# Contraction identities for the generalized Kronecker delta

## i. Overview

This file proves the combinatorial contraction facts for the `generalizedKroneckerDelta`
(defined in `Physlib.Mathematics.KroneckerDelta.Basic`). Everything here is purely about the
abstract generalized Kronecker delta on a finite type; no tensor or physics content appears.
These facts are the reusable backbone of the Levi-Civita epsilon-epsilon contraction
identities proved in `Physlib.Relativity.Tensors.LeviCivita.Contractions`.

The central fact is that summing a `generalizedKroneckerDelta` over one shared index lowers
its rank by one and multiplies it by `card α - n` (`generalizedKroneckerDelta_sum_snoc`).
Iterating that fact, together with the product identity
`generalizedKroneckerDelta μ ν = generalizedKroneckerDelta μ id * generalizedKroneckerDelta ν id`
(`generalizedKroneckerDelta_mul`), gives the fully-, singly-, and doubly-free
contractions `sum_generalizedKroneckerDelta_self`, `sum_generalizedKroneckerDelta_cons`, and
`sum_generalizedKroneckerDelta_cons₂` over `Fin 4`.

The proof of `generalizedKroneckerDelta_sum_snoc` borders the delta matrix with the appended
index (a Schur-complement reduction) and then applies the ring-general rank-one determinant
update lemma `Matrix.det_add_rankOne`, which is proved here because Mathlib only provides the
matrix determinant lemma when `det A` is a unit and Kronecker-delta matrices are singular.

## ii. Key results

- `generalizedKroneckerDelta_sum_snoc` : summing over one shared index lowers the rank by one.
- `sum_generalizedKroneckerDelta_mul_self`, `sum_generalizedKroneckerDelta_mul_cons`,
  `sum_generalizedKroneckerDelta_mul_cons₂` : the fully-, singly-, and doubly-free symbol-level
  contractions over `Fin 4`.

## iii. Table of contents

- A. The rank-one determinant update
- B. Contraction identities

## iv. References

-/

@[expose] public section

open Matrix

/-!

## A. The rank-one determinant update

-/

namespace Matrix

/-- Expanding the determinant of a rank-one row update over a finite set of rows.
For `i ∈ s` the row `A i` is replaced by `A i + w i • b`; the other rows are untouched. -/
private lemma det_add_rankOne_aux {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*}
    [CommRing R] (A : Matrix ι ι R) (w b : ι → R) (s : Finset ι) :
    (A + Matrix.of fun i j => (if i ∈ s then w i else 0) * b j).det
      = A.det + ∑ i ∈ s, w i * (A.updateRow i b).det := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h0 : (Matrix.of fun (i : ι) (j : ι) =>
        (if i ∈ (∅ : Finset ι) then w i else 0) * b j) = 0 := by
      ext i j; simp
    rw [h0, add_zero, Finset.sum_empty, add_zero]
  | @insert i₀ s hi₀ ih =>
    -- The new matrix differs from the `s`-matrix only in row `i₀`, by `+ w i₀ • b`.
    set Ms : Matrix ι ι R := A + Matrix.of fun i j => (if i ∈ s then w i else 0) * b j with hMs
    have hrow : Ms i₀ = A i₀ := by
      funext j; simp [hMs, hi₀]
    have key : (A + Matrix.of fun i j => (if i ∈ insert i₀ s then w i else 0) * b j)
        = Ms.updateRow i₀ (A i₀ + w i₀ • b) := by
      ext i j
      by_cases hi : i = i₀
      · subst hi
        simp [Matrix.updateRow_self, hi₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · rw [Matrix.updateRow_ne hi]
        simp [hMs, Finset.mem_insert, hi]
    rw [key, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
    -- The `A i₀` part rebuilds `Ms`; the `b` part is `det (updateRow A i₀ b)` after column ops.
    have h1 : (Ms.updateRow i₀ (A i₀)).det = Ms.det := by
      rw [← hrow, Matrix.updateRow_eq_self]
    have h2 : (Ms.updateRow i₀ b).det = (A.updateRow i₀ b).det := by
      refine Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun i => if i ∈ s then w i else 0) i₀ (by simp [hi₀]) ?_
      intro i j
      by_cases hi : i = i₀
      · subst hi
        simp [Matrix.updateRow_self, hi₀]
      · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, Matrix.updateRow_self, hMs]
        simp [Matrix.add_apply]
    rw [h1, h2, ih, Finset.sum_insert hi₀]
    ring

/-- **Rank-one determinant update** (the ring-general matrix determinant lemma for an outer
product, valid even when `A` is singular). Adding the rank-one matrix `w ⊗ b` to `A` changes the
determinant by `∑ i, w i * det (A.updateRow i b)`.

Mathlib only provides this when `det A` is a unit (`Matrix.det_add_replicateCol_mul_replicateRow`);
the singular case is needed here because Kronecker-delta matrices are typically singular. -/
private lemma det_add_rankOne {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*}
    [CommRing R] (A : Matrix ι ι R) (w b : ι → R) :
    (A + Matrix.of fun i j => w i * b j).det = A.det + ∑ i, w i * (A.updateRow i b).det := by
  have h := det_add_rankOne_aux A w b Finset.univ
  simpa using h

end Matrix

open KroneckerDelta

open Matrix

/-!

## B. Contraction identities

-/

section Generalized

variable {α : Type} [DecidableEq α] [Fintype α]

/-- The product of two Levi-Civita-type symbols is a generalized Kronecker delta:
`δ^{μ}_{·} · δ^{ν}_{·} = δ^{μ}_{ν}`, where each single factor is a Kronecker matrix against the
identity. This is the Lean form of `ε^{μ₁…μₙ} ε_{ν₁…νₙ} = δ^{μ₁…μₙ}_{ν₁…νₙ}`. -/
lemma generalizedKroneckerDelta_mul (μ ν : α → α) :
    generalizedKroneckerDelta μ id * generalizedKroneckerDelta ν id
      = generalizedKroneckerDelta μ ν := by
  rw [show generalizedKroneckerDelta ν id
        = (Matrix.of fun i j => ((kroneckerDelta (ν i) (id j) : ℕ) : ℤ)).det from rfl,
    ← Matrix.det_transpose,
    show generalizedKroneckerDelta μ id
        = (Matrix.of fun i j => ((kroneckerDelta (μ i) (id j) : ℕ) : ℤ)).det from rfl,
    ← Matrix.det_mul,
    show generalizedKroneckerDelta μ ν
        = (Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)).det from rfl]
  congr 1
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.transpose_apply, id_eq, ← Nat.cast_mul]
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.sum_congr rfl fun k _ => by rw [KroneckerDelta.symm (ν j) k]]
  exact KroneckerDelta.sum_mul (μ i) (ν j)

/-- **Generalized Kronecker delta contraction.** Summing a `generalizedKroneckerDelta` over one
shared index appended at the end lowers the rank by one and pulls out a factor of `card α - n`.
This is the reusable combinatorial fact behind all epsilon-epsilon identities. -/
lemma generalizedKroneckerDelta_sum_snoc {n : ℕ} (μ ν : Fin n → α) :
    ∑ a : α, generalizedKroneckerDelta (Fin.snoc μ a) (Fin.snoc ν a)
      = ((Fintype.card α : ℤ) - n) * generalizedKroneckerDelta μ ν := by
  classical
  set A : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ) with hA
  -- The `n × n` δ-matrix is exactly `generalizedKroneckerDelta μ ν`.
  have hAdet : A.det = generalizedKroneckerDelta μ ν := rfl
  -- Step 1: Schur complement. Border the matrix with the appended index and reduce dimension.
  have step1 : ∀ a : α, generalizedKroneckerDelta (Fin.snoc μ a) (Fin.snoc ν a)
      = (A - Matrix.of fun i j =>
          ((kroneckerDelta (μ i) a : ℕ) : ℤ) * ((kroneckerDelta a (ν j) : ℕ) : ℤ)).det := by
    intro a
    have hblk : (Matrix.of fun (i j : Fin (n + 1)) =>
          ((kroneckerDelta ((Fin.snoc μ a : Fin (n + 1) → α) i)
            ((Fin.snoc ν a : Fin (n + 1) → α) j) : ℕ) : ℤ)).submatrix
            finSumFinEquiv finSumFinEquiv
        = Matrix.fromBlocks A
            (Matrix.of fun i (_ : Fin 1) => ((kroneckerDelta (μ i) a : ℕ) : ℤ))
            (Matrix.of fun (_ : Fin 1) j => ((kroneckerDelta a (ν j) : ℕ) : ℤ))
            (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
      have hcast : ∀ i : Fin n, (Fin.castAdd 1 i : Fin (n + 1)) = Fin.castSucc i := fun _ => rfl
      have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := by
        apply Fin.ext; simp
      ext x y
      cases x with
      | inl i =>
        cases y with
        | inl j =>
          simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, Matrix.of_apply,
            Matrix.fromBlocks_apply₁₁, hA]
          rw [hcast i, hcast j, Fin.snoc_castSucc, Fin.snoc_castSucc]
        | inr j =>
          simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
            Matrix.of_apply, Matrix.fromBlocks_apply₁₂]
          rw [hcast i, Fin.snoc_castSucc, Subsingleton.elim j 0, hlast, Fin.snoc_last]
      | inr i =>
        cases y with
        | inl j =>
          simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
            Matrix.of_apply, Matrix.fromBlocks_apply₂₁]
          rw [hcast j, Fin.snoc_castSucc, Subsingleton.elim i 0, hlast, Fin.snoc_last]
        | inr j =>
          simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, Matrix.of_apply,
            Matrix.fromBlocks_apply₂₂]
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0, hlast]
          simp [Fin.snoc_last]
    rw [show generalizedKroneckerDelta (Fin.snoc μ a) (Fin.snoc ν a)
          = (Matrix.of fun (i j : Fin (n + 1)) =>
              ((kroneckerDelta ((Fin.snoc μ a : Fin (n + 1) → α) i)
                ((Fin.snoc ν a : Fin (n + 1) → α) j) : ℕ) : ℤ)).det from rfl,
      ← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblk, Matrix.det_fromBlocks_one₂₂]
    congr 1
  -- Step 2: the rank-one determinant lemma applied per `a`.
  have step2 : ∀ a : α, (A - Matrix.of fun i j =>
        ((kroneckerDelta (μ i) a : ℕ) : ℤ) * ((kroneckerDelta a (ν j) : ℕ) : ℤ)).det
      = A.det - ∑ i, ((kroneckerDelta (μ i) a : ℕ) : ℤ)
          * (A.updateRow i (fun j => ((kroneckerDelta a (ν j) : ℕ) : ℤ))).det := by
    intro a
    have h := Matrix.det_add_rankOne A (fun i => -((kroneckerDelta (μ i) a : ℕ) : ℤ))
      (fun j => ((kroneckerDelta a (ν j) : ℕ) : ℤ))
    have hmat : (A - Matrix.of fun i j =>
          ((kroneckerDelta (μ i) a : ℕ) : ℤ) * ((kroneckerDelta a (ν j) : ℕ) : ℤ))
        = (A + Matrix.of fun i j => (-((kroneckerDelta (μ i) a : ℕ) : ℤ))
            * ((kroneckerDelta a (ν j) : ℕ) : ℤ)) := by
      ext i j; simp [Matrix.sub_apply, Matrix.add_apply, neg_mul, sub_eq_add_neg]
    rw [hmat, h]
    simp only [neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  -- Step 3: collect the sums.
  rw [← hAdet]
  have hkey : ∀ i : Fin n, ∑ a : α, ((kroneckerDelta (μ i) a : ℕ) : ℤ)
        * (A.updateRow i (fun j => ((kroneckerDelta a (ν j) : ℕ) : ℤ))).det = A.det := by
    intro i
    rw [Finset.sum_eq_single (μ i)]
    · have : (fun j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)) = A i := by
        funext j; simp [hA]
      rw [KroneckerDelta.eq_one_of_same, Nat.cast_one, one_mul, this, Matrix.updateRow_eq_self]
    · intro a _ hane
      rw [KroneckerDelta.eq_zero_of_ne (Ne.symm hane), Nat.cast_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ (μ i)) h
  calc ∑ a : α, generalizedKroneckerDelta (Fin.snoc μ a) (Fin.snoc ν a)
      = ∑ a : α, (A.det - ∑ i, ((kroneckerDelta (μ i) a : ℕ) : ℤ)
          * (A.updateRow i (fun j => ((kroneckerDelta a (ν j) : ℕ) : ℤ))).det) := by
        exact Finset.sum_congr rfl fun a _ => by rw [step1 a, step2 a]
    _ = (Fintype.card α : ℤ) * A.det
          - ∑ i, ∑ a : α, ((kroneckerDelta (μ i) a : ℕ) : ℤ)
            * (A.updateRow i (fun j => ((kroneckerDelta a (ν j) : ℕ) : ℤ))).det := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.sum_comm]
    _ = (Fintype.card α : ℤ) * A.det - ∑ _i : Fin n, A.det := by
        rw [Finset.sum_congr rfl fun i _ => hkey i]
    _ = ((Fintype.card α : ℤ) - n) * A.det := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Split a sum over `(k+1)`-tuples into the last entry and the initial `k`-tuple. -/
private lemma sum_over_snoc {X : Type*} [Fintype X] {M : Type*} [AddCommMonoid M] {k : ℕ}
    (F : (Fin (k + 1) → X) → M) :
    ∑ h : Fin (k + 1) → X, F h = ∑ h' : Fin k → X, ∑ c : X, F (Fin.snoc h' c) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ => X)) F, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- **Full contraction.** Iterating the snoc contraction over all four indices:
`∑_f δ^{f}_{f} = 4!`. Here `f` ranges over all maps `Fin 4 → Fin 4`. -/
lemma sum_generalizedKroneckerDelta_self (k : ℕ) :
    ∑ h : Fin k → Fin 4, generalizedKroneckerDelta h h
      = ∏ j ∈ Finset.range k, ((4 : ℤ) - j) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero, Fintype.sum_unique]
    exact Matrix.det_fin_zero
  | succ k ih =>
    rw [sum_over_snoc]
    have hstep : ∀ h' : Fin k → Fin 4, ∑ c : Fin 4,
        generalizedKroneckerDelta (Fin.snoc h' c) (Fin.snoc h' c)
          = ((4 : ℤ) - k) * generalizedKroneckerDelta h' h' := by
      intro h'
      rw [generalizedKroneckerDelta_sum_snoc h' h', Fintype.card_fin]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun h' _ => hstep h', ← Finset.mul_sum, ih,
      Finset.prod_range_succ]
    ring

/-- **Single contraction.** Contracting the last `k` of `k+1` index pairs leaves one free pair
`σ, τ`, with the factorial factor `(4-1)(4-2)…`. -/
lemma sum_generalizedKroneckerDelta_cons (σ τ : Fin 4) (k : ℕ) :
    ∑ h : Fin k → Fin 4,
        generalizedKroneckerDelta (Fin.cons σ h) (Fin.cons τ h)
      = (∏ j ∈ Finset.range k, ((3 : ℤ) - j)) * ((kroneckerDelta σ τ : ℕ) : ℤ) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero, one_mul, Fintype.sum_unique]
    exact Matrix.det_fin_one _
  | succ k ih =>
    rw [sum_over_snoc]
    have hstep : ∀ h' : Fin k → Fin 4, ∑ c : Fin 4,
        generalizedKroneckerDelta (Fin.cons σ (Fin.snoc h' c)) (Fin.cons τ (Fin.snoc h' c))
          = ((3 : ℤ) - k) * generalizedKroneckerDelta (Fin.cons σ h') (Fin.cons τ h') := by
      intro h'
      rw [Finset.sum_congr rfl fun c _ => by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons],
        generalizedKroneckerDelta_sum_snoc (Fin.cons σ h') (Fin.cons τ h'), Fintype.card_fin]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun h' _ => hstep h', ← Finset.mul_sum, ih,
      Finset.prod_range_succ]
    ring

/-- **Double contraction.** Contracting the last `k` of `k+2` index pairs leaves two free pairs,
with value a `2×2` generalized Kronecker delta times the factorial factor. -/
lemma sum_generalizedKroneckerDelta_cons₂ (ρ σ τ ω : Fin 4) (k : ℕ) :
    ∑ h : Fin k → Fin 4,
        generalizedKroneckerDelta (Fin.cons ρ (Fin.cons σ h)) (Fin.cons τ (Fin.cons ω h))
      = (∏ j ∈ Finset.range k, ((2 : ℤ) - j))
        * generalizedKroneckerDelta ![ρ, σ] ![τ, ω] := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero, one_mul, Fintype.sum_unique]
    have e1 : ∀ d : Fin 0 → Fin 4, (Fin.cons ρ (Fin.cons σ d) : Fin 2 → Fin 4) = ![ρ, σ] := by
      intro d; funext i; fin_cases i <;> rfl
    have e2 : ∀ d : Fin 0 → Fin 4, (Fin.cons τ (Fin.cons ω d) : Fin 2 → Fin 4) = ![τ, ω] := by
      intro d; funext i; fin_cases i <;> rfl
    rw [e1, e2]
  | succ k ih =>
    rw [sum_over_snoc]
    have hstep : ∀ h' : Fin k → Fin 4, ∑ c : Fin 4,
        generalizedKroneckerDelta (Fin.cons ρ (Fin.cons σ (Fin.snoc h' c)))
          (Fin.cons τ (Fin.cons ω (Fin.snoc h' c)))
          = ((2 : ℤ) - k) * generalizedKroneckerDelta (Fin.cons ρ (Fin.cons σ h'))
              (Fin.cons τ (Fin.cons ω h')) := by
      intro h'
      rw [Finset.sum_congr rfl fun c _ => by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons,
          Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons],
        generalizedKroneckerDelta_sum_snoc (Fin.cons ρ (Fin.cons σ h'))
          (Fin.cons τ (Fin.cons ω h')), Fintype.card_fin]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun h' _ => hstep h', ← Finset.mul_sum, ih,
      Finset.prod_range_succ]
    ring

/-- Symbol-level full contraction over `Fin 4 → Fin 4`. -/
lemma sum_generalizedKroneckerDelta_mul_self :
    ∑ g : Fin 4 → Fin 4,
      generalizedKroneckerDelta g id * generalizedKroneckerDelta g id = (24 : ℤ) := by
  rw [Finset.sum_congr rfl fun g _ => generalizedKroneckerDelta_mul g g,
    sum_generalizedKroneckerDelta_self 4]
  norm_num [Finset.prod_range_succ]

/-- Symbol-level triple contraction, one free pair `σ, τ`. -/
lemma sum_generalizedKroneckerDelta_mul_cons (σ τ : Fin 4) :
    ∑ h : Fin 3 → Fin 4,
        generalizedKroneckerDelta (Fin.cons σ h) id
          * generalizedKroneckerDelta (Fin.cons τ h) id
      = 6 * ((kroneckerDelta σ τ : ℕ) : ℤ) := by
  rw [Finset.sum_congr rfl fun h _ =>
      generalizedKroneckerDelta_mul (Fin.cons σ h) (Fin.cons τ h),
    sum_generalizedKroneckerDelta_cons σ τ 3]
  norm_num [Finset.prod_range_succ]

/-- Symbol-level double contraction, two free pairs. -/
lemma sum_generalizedKroneckerDelta_mul_cons₂ (ρ σ τ ω : Fin 4) :
    ∑ h : Fin 2 → Fin 4,
        generalizedKroneckerDelta (Fin.cons ρ (Fin.cons σ h)) id
          * generalizedKroneckerDelta (Fin.cons τ (Fin.cons ω h)) id
      = 2 * (((kroneckerDelta ρ τ : ℕ) : ℤ) * ((kroneckerDelta σ ω : ℕ) : ℤ)
          - ((kroneckerDelta ρ ω : ℕ) : ℤ) * ((kroneckerDelta σ τ : ℕ) : ℤ)) := by
  have hdet : generalizedKroneckerDelta ![ρ, σ] ![τ, ω]
      = ((kroneckerDelta ρ τ : ℕ) : ℤ) * ((kroneckerDelta σ ω : ℕ) : ℤ)
        - ((kroneckerDelta ρ ω : ℕ) : ℤ) * ((kroneckerDelta σ τ : ℕ) : ℤ) := by
    rw [show generalizedKroneckerDelta ![ρ, σ] ![τ, ω]
          = (Matrix.of fun i j => ((kroneckerDelta (![ρ, σ] i) (![τ, ω] j) : ℕ) : ℤ)).det from rfl,
      Matrix.det_fin_two]
    simp
  rw [Finset.sum_congr rfl fun h _ =>
      generalizedKroneckerDelta_mul (Fin.cons ρ (Fin.cons σ h)) (Fin.cons τ (Fin.cons ω h)),
    sum_generalizedKroneckerDelta_cons₂ ρ σ τ ω 2, hdet]
  norm_num [Finset.prod_range_succ]

end Generalized
