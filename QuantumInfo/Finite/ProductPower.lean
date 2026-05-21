/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import QuantumInfo.ClassicalInfo.Hellinger
public import QuantumInfo.Finite.AxiomatizedEntropy.Defs

public import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite product powers

This file contains product-power API for finite probability distributions and finite quantum
states, using the canonical coordinate type `Fin n → d`.
-/

@[expose] public section

noncomputable section
universe u v

open scoped BigOperators
open scoped ENNReal
open scoped Kronecker
open scoped HermitianMat
open ComplexOrder

namespace ProbDistribution

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type v} [∀ i, Fintype (α i)]

/-- Product of finitely many probability distributions, indexed by a Pi type. -/
def piProd (P : ∀ i, ProbDistribution (α i)) : ProbDistribution (∀ i, α i) :=
  mk' (α := ∀ i, α i) (fun x => ∏ i, (P i (x i) : ℝ))
    (fun x => Finset.prod_nonneg fun i _ => (P i (x i)).2.1)
    (by simpa using (Fintype.prod_sum (fun i x => ((P i) x : ℝ))).symm)

@[simp]
theorem piProd_apply_coe (P : ∀ i, ProbDistribution (α i)) (x : ∀ i, α i) :
    ((piProd P x : Prob) : ℝ) = ∏ i, (P i (x i) : ℝ) :=
  rfl

variable {d : Type u} [Fintype d]

/-- The `n`-fold independent product power of a probability distribution. -/
def npow (P : ProbDistribution d) (n : ℕ) : ProbDistribution (Fin n → d) :=
  piProd fun _ => P

@[simp]
theorem npow_apply_coe (P : ProbDistribution d) (n : ℕ) (x : Fin n → d) :
    ((npow P n x : Prob) : ℝ) = ∏ i, (P (x i) : ℝ) :=
  rfl

theorem hellingerOverlap_piProd (P Q : ∀ i, ProbDistribution (α i)) :
    hellingerOverlap (piProd P) (piProd Q) = ∏ i, hellingerOverlap (P i) (Q i) := by
  rw [hellingerOverlap]
  calc
    (∑ x : ∀ i, α i,
        Real.sqrt (((piProd P x : Prob) : ℝ) * ((piProd Q x : Prob) : ℝ))) =
        ∑ x : ∀ i, α i, ∏ i, Real.sqrt ((P i (x i) : ℝ) * (Q i (x i) : ℝ)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [piProd_apply_coe, piProd_apply_coe, ← Finset.prod_mul_distrib,
        Real.sqrt_prod]
      exact fun i _ => mul_nonneg (P i (x i)).2.1 (Q i (x i)).2.1
    _ = ∏ i, hellingerOverlap (P i) (Q i) := by
      simpa [hellingerOverlap] using
        (Fintype.prod_sum fun i x => Real.sqrt ((P i x : ℝ) * (Q i x : ℝ))).symm

/-- Hellinger overlap of independent product powers. -/
theorem hellingerOverlap_npow (P Q : ProbDistribution d) (n : ℕ) :
    hellingerOverlap (npow P n) (npow Q n) = (hellingerOverlap P Q) ^ n := by
  simpa [npow] using hellingerOverlap_piProd (fun _ : Fin n => P) fun _ : Fin n => Q

end ProbDistribution

namespace HermitianMat

variable {m n : Type u} [Fintype m] [Fintype n]
variable {A B : HermitianMat m ℂ} {C D : HermitianMat n ℂ}

omit [Fintype m] in
private theorem reindex_le_reindex_iff {m' : Type u} [Fintype m']
    (e : m ≃ m') (A B : HermitianMat m ℂ) :
    A.reindex e ≤ B.reindex e ↔ A ≤ B := by
  rw [HermitianMat.le_iff, HermitianMat.le_iff]
  simp only [HermitianMat.reindex_sub, HermitianMat.mat_reindex]
  change ((B - A).mat.submatrix e.symm e.symm).PosSemidef ↔ (B - A).mat.PosSemidef
  exact Matrix.posSemidef_submatrix_equiv e.symm

private theorem kronecker_mono (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hAB : A ≤ B) (hCD : C ≤ D) :
    A ⊗ₖ C ≤ B ⊗ₖ D := by
  rw [← sub_nonneg]
  have hEq : B ⊗ₖ D - A ⊗ₖ C = A ⊗ₖ (D - C) + (B - A) ⊗ₖ D := by
    ext ⟨i, k⟩ ⟨j, l⟩
    change (B ⊗ₖ D - A ⊗ₖ C).mat (i, k) (j, l) =
      (A ⊗ₖ (D - C) + (B - A) ⊗ₖ D).mat (i, k) (j, l)
    simp only [HermitianMat.mat_sub, HermitianMat.mat_add, HermitianMat.kronecker_mat,
      Matrix.sub_apply, Matrix.add_apply, Matrix.kroneckerMap_apply]
    ring
  simpa [hEq] using add_nonneg
    (HermitianMat.kronecker_nonneg hA (sub_nonneg.mpr hCD))
    (HermitianMat.kronecker_nonneg (sub_nonneg.mpr hAB) hD)

end HermitianMat

namespace MState

variable {d : Type u} [Fintype d] [DecidableEq d]

/-- Classical states commute with finite product powers. -/
theorem ofClassical_npow (P : ProbDistribution d) (n : ℕ) :
    (MState.ofClassical P) ⊗ᴹ^ n = MState.ofClassical (ProbDistribution.npow P n) := by
  apply MState.ext_m
  ext x y
  change (∏ i : Fin n, if x i = y i then (((P (x i)) : Prob) : ℂ) else 0) =
    if x = y then (((ProbDistribution.npow P n x) : Prob) : ℂ) else 0
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    simp only [↓reduceIte]
    exact_mod_cast (ProbDistribution.npow_apply_coe P n x).symm
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    rw [if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

def npowSuccEquiv (n : ℕ) (d : Type u) :
    (Fin (n + 1) → d) ≃ (Fin n → d) × d :=
  (Fin.snocEquiv (fun _ : Fin (n + 1) => d)).symm.trans
    (Equiv.prodComm d (Fin n → d))

/-- Product powers unfold by splitting off the last tensor factor. -/
theorem npow_succ (ρ : MState d) (n : ℕ) :
    MState.npow ρ (n + 1) = ((MState.npow ρ n) ⊗ᴹ ρ).relabel (npowSuccEquiv n d) := by
  apply MState.ext_m
  ext x y
  simp [MState.npow, MState.piProd, MState.prod, MState.relabel_m, Matrix.piProd,
    npowSuccEquiv, Fin.snocEquiv]
  change (∏ i : Fin (n + 1), ρ.m (x i) (y i)) =
    (∏ i : Fin n, ρ.m (x i.castSucc) (y i.castSucc)) *
      ρ.m (x (Fin.last n)) (y (Fin.last n))
  rw [Fin.prod_univ_castSucc]

/-- Product powers preserve exponential Loewner bounds. -/
theorem npow_le_exp_smul {ρ σ : MState d} {x : ℝ}
    (h : ρ.M ≤ Real.exp x • σ.M) :
    ∀ n, (MState.npow ρ n).M ≤ Real.exp ((n : ℝ) * x) • (MState.npow σ n).M := by
  intro n
  induction n with
  | zero =>
      have hσ0 : MState.npow σ 0 = MState.npow ρ 0 := by
        apply MState.ext_m; ext x y; simp [MState.npow, MState.piProd, Matrix.piProd]
      simp [hσ0]
  | succ n ih =>
      rw [MState.npow_succ ρ n, MState.npow_succ σ n]
      rw [MState.relabel_M, MState.relabel_M, ← HermitianMat.reindex_smul,
        HermitianMat.reindex_le_reindex_iff]
      have hscale :
          ((Real.exp ((n : ℝ) * x) • (MState.npow σ n).M) ⊗ₖ
              (Real.exp x • σ.M) :
                HermitianMat ((Fin n → d) × d) ℂ) =
            Real.exp (((n + 1 : ℕ) : ℝ) * x) •
              ((MState.npow σ n).M ⊗ₖ σ.M) := by
        ext1
        simp [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
        rw [mul_comm (Real.exp x), ← Real.exp_add]
        ring_nf
      simpa [MState.prod, hscale] using
        HermitianMat.kronecker_mono (MState.npow ρ n).nonneg
          (smul_nonneg (by positivity) σ.nonneg) ih h

end MState

namespace RelEntropy

variable (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → HermitianMat d ℂ → ℝ≥0∞)
variable {d : Type u} [Fintype d] [DecidableEq d]

/-- Relative entropy is additive over finite product powers. -/
theorem of_npow [RelEntropy f] (ρ σ : MState d) :
    ∀ n, f (MState.npow ρ n) (MState.npow σ n).M = ((n : ℕ) : ENNReal) * f ρ σ := by
  intro n
  induction n with
  | zero =>
      have hσ0 : MState.npow σ 0 = MState.npow ρ 0 := by
        apply MState.ext_m
        ext x y
        simp [MState.npow, MState.piProd, Matrix.piProd]
      simp [hσ0]
  | succ n ih =>
      rw [MState.npow_succ ρ n, MState.npow_succ σ n]
      rw [RelEntropy.relabel_eq (f := f) (MState.npowSuccEquiv n d),
        RelEntropy.of_kron (f := f), ih, Nat.cast_succ, add_mul, one_mul, add_comm]

end RelEntropy
