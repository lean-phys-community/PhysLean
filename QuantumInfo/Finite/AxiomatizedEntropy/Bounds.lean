/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

import QuantumInfo.Finite.ProductPower
public import QuantumInfo.Finite.AxiomatizedEntropy.Defs
public import QuantumInfo.Finite.CPTPMap.CQPrepare
public import QuantumInfo.ForMathlib.HermitianMat.Order
public import QuantumInfo.ForMathlib.HermitianMat.Proj

@[expose] public section

/-! # Bounds for axiomatized relative entropies

This file contains the relative max-entropy and the proof that every axiomatized relative entropy
lies below `max` on state inputs.
-/

noncomputable section
universe u

open ComplexOrder
open scoped NNReal
open scoped ENNReal
open scoped Kronecker
open scoped HermitianMat

variable (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → HermitianMat d ℂ → ℝ≥0∞)

namespace RelEntropy

variable {d : Type u} [Fintype d] [DecidableEq d]

open Classical in
/-- Quantum relative max-entropy. -/
noncomputable def max (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  if ∃ (x : ℝ), ρ.M ≤ Real.exp x • σ then
    some (sInf { x : NNReal | ρ.M ≤ Real.exp x • σ })
  else
    ⊤

@[aesop (rule_sets := [finiteness]) simp]
protected theorem max_not_top (ρ : MState d) (σ : HermitianMat d ℂ) (hσ : 0 ≤ σ) :
    (max ρ σ) ≠ ⊤ ↔ σ.ker ≤ ρ.M.ker := by
  open ComplexOrder in
  constructor
  · intro h
    have hx : ∃ x : ℝ, ρ.M ≤ Real.exp x • σ := by
      by_contra hx
      exact h (by simp [max, hx])
    obtain ⟨x, hx⟩ := hx
    exact HermitianMat.ker_le_of_le_smul (Real.exp_pos x).ne' ρ.nonneg hx
  · intro hker
    let P := σ.supportProj
    have hright : ρ.M.mat * P.mat = ρ.M.mat := by
      dsimp [P]; simpa using HermitianMat.mul_supportProj_of_ker_le (A := ρ.M) (B := σ) hker
    have hleft : P.mat * ρ.M.mat = ρ.M.mat := by
      simpa only [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat] using
        congrArg Matrix.conjTranspose hright
    have hP_idem : P.mat * P.mat = P.mat := by
      rw [← pow_two, ← HermitianMat.mat_pow]
      congr 1
      dsimp [P]
      rw [HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_pow,
        ← HermitianMat.cfc_comp_apply]
      exact HermitianMat.cfc_congr_of_nonneg hσ fun x _ => by
        by_cases hx : x = 0 <;> simp [hx]
    have hρ_le_P : ρ.M ≤ P := calc
      ρ.M = ρ.M.conj P.mat := by
        symm; apply HermitianMat.ext
        simp only [HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat,
          hright, hleft]
      _ ≤ (1 : HermitianMat d ℂ).conj P.mat := HermitianMat.conj_mono ρ.le_one
      _ = P := by apply HermitianMat.ext; simp [HermitianMat.conj_apply_mat, hP_idem]
    let α : ℝ := ∑ i, if σ.H.eigenvalues i = 0 then 0 else (σ.H.eigenvalues i)⁻¹
    have hterm j : 0 ≤ if σ.H.eigenvalues j = 0 then 0 else (σ.H.eigenvalues j)⁻¹ := by
      split_ifs
      · rfl
      · exact inv_nonneg.mpr (HermitianMat.eigenvalues_nonneg hσ j)
    have hα_nonneg : 0 ≤ α := Finset.sum_nonneg fun i _ => hterm i
    have hP_le : P ≤ α • σ := by
      dsimp [P, α]
      rw [← sub_nonneg, show (∑ i, if σ.H.eigenvalues i = 0 then 0 else (σ.H.eigenvalues i)⁻¹) • σ =
        σ.cfc (fun x => (∑ i, if σ.H.eigenvalues i = 0 then 0 else (σ.H.eigenvalues i)⁻¹) * x) from by
        simp,
        HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_sub_apply, HermitianMat.cfc_nonneg_iff]
      intro i
      by_cases hi : σ.H.eigenvalues i = 0
      · simp [hi]
      · have hsingle : (σ.H.eigenvalues i)⁻¹ ≤ α := by
          dsimp [α]; simpa [hi] using
            Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
        have := mul_le_mul_of_nonneg_right hsingle (HermitianMat.eigenvalues_nonneg hσ i)
        simp [hi]; linarith [inv_mul_cancel₀ hi]
    rw [max, if_pos ⟨Real.log (α + 1), by
      calc ρ.M ≤ P := hρ_le_P
        _ ≤ α • σ := hP_le
        _ ≤ (α + 1) • σ := smul_le_smul_of_nonneg_right (by linarith) hσ
        _ = Real.exp (Real.log (α + 1)) • σ := by
            rw [Real.exp_log (by positivity : (0 : ℝ) < α + 1)]⟩]
    simp

protected theorem toReal_max (ρ : MState d) (σ : HermitianMat d ℂ) :
    (max ρ σ).toReal = sInf ((↑) '' { x : ℝ≥0 | ρ.M ≤ Real.exp x • σ }) := by
  rw [max]
  split_ifs with h
  · have hs : ({ x : ℝ≥0 | ρ.M ≤ Real.exp x • σ } : Set ℝ≥0).Nonempty := by
      rcases h with ⟨x, hx⟩
      have hσ_nonneg : 0 ≤ σ :=
        (smul_le_smul_iff_of_pos_left (Real.exp_pos x)).mp (by simpa using le_trans ρ.nonneg hx)
      refine ⟨⟨Max.max x 0, le_max_right _ _⟩, ?_⟩
      exact hx.trans <|
        smul_le_smul_of_nonneg_right
          (Real.exp_le_exp.mpr (show x ≤ Max.max x 0 from le_max_left _ _)) hσ_nonneg
    simp [ENNReal.some_eq_coe, NNReal.coe_sInf]
  · push Not at h
    have hs : ({ x : ℝ≥0 | ρ.M ≤ Real.exp x • σ } : Set ℝ≥0) = ∅ := by
      ext x
      simp [h (x : ℝ)]
    simp [hs]

@[simp]
theorem max_self_eq_zero (ρ : MState d) : max ρ ρ.M = 0 := by
  rw [max, if_pos ⟨0, by simp⟩]
  simp [show sInf { x : ℝ≥0 | ρ.M ≤ Real.exp x • ρ.M } = 0 from
    le_antisymm (csInf_le ⟨0, fun x _ => x.2⟩ (by simp))
      (le_csInf ⟨0, by simp⟩ fun x _ => x.2)]

private def tauOfLE (N : ℕ) (hN : 0 < N) (ρ σ : MState d)
    (h : ρ.M ≤ ((N + 1 : ℝ) • σ.M)) : MState d where
  M := ((N : ℝ)⁻¹) • (((N + 1 : ℝ) • σ.M) - ρ.M)
  nonneg := smul_nonneg (by positivity) (sub_nonneg.mpr h)
  tr := by
    have hN' : (N : ℝ) ≠ 0 := by positivity
    simp [HermitianMat.trace_sub, σ.tr, ρ.tr, hN']

private theorem cqPrepareCPTP_uniform_tauOfLE
    (M : ℕ) (hM_pos : 0 < M) (ρ σ : MState d)
    (h : ρ.M ≤ ((M + 1 : ℝ) • σ.M)) :
    CPTPMap.cqPrepare (d := d) (fun i : ULift (Fin (M + 1)) =>
      if i = ⟨0⟩ then ρ else tauOfLE (d := d) M hM_pos ρ σ h)
      (MState.uniform : MState (ULift (Fin (M + 1)))) = σ := by
  let x0 : ULift (Fin (M + 1)) := ⟨0⟩
  let τr := tauOfLE (d := d) M hM_pos ρ σ h
  let τ : ULift (Fin (M + 1)) → MState d := fun i => if i = x0 then ρ else τr
  change CPTPMap.cqPrepare (d := d) τ (MState.uniform : MState (ULift (Fin (M + 1)))) = σ
  apply MState.ext_m
  change (CPTPMap.cqPrepare (d := d) τ
      (MState.ofClassical ProbDistribution.uniform)).m = σ.m
  rw [CPTPMap.cqPrepare_apply_ofClassical (d := d) τ ProbDistribution.uniform]
  ext i j
  simp only [ProbDistribution.uniform_def, Matrix.sum_apply, Matrix.smul_apply,
    Complex.real_smul, Finset.card_univ, Fintype.card_ulift, Fintype.card_fin, one_div,
    Nat.cast_add, Nat.cast_one, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]
  rw [(Finset.sum_erase_add (s := Finset.univ) (a := x0)
    (f := fun x : ULift (Fin (M + 1)) =>
      (↑M + 1 : ℂ)⁻¹ * (if x = x0 then ρ else τr).m i j) (by simp)).symm]
  have hrest :
      Finset.sum (Finset.erase Finset.univ x0)
        (fun x : ULift (Fin (M + 1)) =>
          (↑M + 1 : ℂ)⁻¹ * (if x = x0 then ρ else τr).m i j)
        =
      M * ((↑M + 1 : ℂ)⁻¹ * τr.m i j) := by
    trans Finset.sum (Finset.erase Finset.univ x0)
      (fun _ : ULift (Fin (M + 1)) => (↑M + 1 : ℂ)⁻¹ * τr.m i j)
    · exact Finset.sum_congr rfl fun x hx => by simp [(Finset.mem_erase.mp hx).1]
    · simp [x0]
  rw [hrest]
  dsimp [τr]
  simp [tauOfLE, MState.m]
  field_simp [show (M : ℂ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hM_pos,
    show (M + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero M]
  simp only [← HermitianMat.mat_apply, HermitianMat.mat_sub, HermitianMat.mat_smul,
    Matrix.sub_apply, Matrix.smul_apply]
  rw [Complex.real_smul]
  norm_num

private theorem integer_bound_aux [RelEntropy f] (N : ℕ) (ρ σ : MState d)
    (h : ρ.M ≤ ((N + 1 : ℝ) • σ.M)) :
    f ρ σ.M ≤ ENNReal.ofReal (Real.log (N + 1)) := by
  cases N with
  | zero =>
      have hEq : ρ = σ := MState.ext <| (eq_of_sub_eq_zero (HermitianMat.ext <|
          (Matrix.PosSemidef.trace_eq_zero_iff (HermitianMat.zero_le_iff.mp <|
            show 0 ≤ σ.M - ρ.M by simpa using sub_nonneg.mpr (show ρ.M ≤ σ.M by
              simpa using h))).1 <|
            (HermitianMat.trace_eq_zero_iff (A := σ.M - ρ.M)).1
              (by simp [σ.tr, ρ.tr]))).symm
      subst hEq
      simp
  | succ N =>
      let κ := ULift (Fin (N + 2))
      let x0 : κ := ⟨0⟩
      let τrest := tauOfLE (d := d) (N + 1) (Nat.succ_pos _) ρ σ h
      let τ : κ → MState d := fun i => if i = x0 then ρ else τrest
      let Λ : CPTPMap κ d := CPTPMap.cqPrepare (d := d) τ
      have hconst : Λ (MState.ofClassical (.constant x0)) = ρ := by
        apply MState.ext_m
        rw [CPTPMap.cqPrepare_apply_ofClassical (d := d) τ (.constant x0)]
        ext i j
        rw [Finset.sum_eq_single x0]
        · simp [τ, ProbDistribution.constant_eq]
        · intro y _ hyx
          simp [ProbDistribution.constant_eq, hyx, eq_comm]
        · simp
      have huniform : Λ (MState.uniform : MState κ) = σ := by
        simpa [Λ, κ, τ, τrest] using
          cqPrepareCPTP_uniform_tauOfLE (d := d) (N + 1) (Nat.succ_pos _) ρ σ h
      calc
        f ρ σ.M =
            f (Λ (MState.ofClassical (.constant x0)))
              ((Λ (MState.uniform : MState κ)).M) := by
          rw [hconst, huniform]
        _ ≤ f (MState.ofClassical (.constant x0)) (MState.uniform : MState κ).M := DPI _ _ Λ
        _ = ENNReal.ofReal (Real.log (N + 2)) := by
          simpa [κ, ENNReal.some_eq_coe,
            ENNReal.ofReal_eq_coe_nnreal (Real.log_nonneg
              (by
                have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
                linarith : (1 : ℝ) ≤ (N + 2 : ℝ)))] using
            (RelEntropy.normalized (f := f) (d := κ) x0)
        _ = ENNReal.ofReal (Real.log (↑(N + 1) + 1)) := by
          norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]

/-- If `ρ ≤ exp x • σ`, then every axiomatized relative entropy is bounded by `x`. -/
theorem le_of_le_exp [RelEntropy f] (ρ σ : MState d) {x : ℝ}
    (hx : 0 ≤ x) (h : ρ.M ≤ Real.exp x • σ.M) :
    f ρ σ.M ≤ ENNReal.ofReal x := by
  have hfin : f ρ σ.M ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top <|
      integer_bound_aux (f := f) (N := Nat.ceil (Real.exp x)) ρ σ <| by
      exact h.trans <| smul_le_smul_of_nonneg_right
        ((Nat.le_ceil _).trans (by norm_num)) σ.nonneg
  by_contra hfx
  let δ : ℝ := (f ρ σ.M).toReal - x
  have hδ : 0 < δ := by
    dsimp [δ]; linarith [(ENNReal.ofReal_lt_iff_lt_toReal hx hfin).1 (lt_of_not_ge hfx)]
  let n : ℕ := Nat.ceil (Real.log 3 / δ) + 1
  have hgap : Real.log 3 < (n : ℝ) * δ := by
    rw [← div_lt_iff₀ hδ]
    dsimp [n]
    exact lt_of_le_of_lt (Nat.le_ceil (Real.log 3 / δ))
      (by exact_mod_cast Nat.lt_succ_self (Nat.ceil (Real.log 3 / δ)))
  let y : ℝ := (n : ℝ) * x
  have hpow_bound' :
      (((n : ℕ) : ENNReal) * f ρ σ.M) ≤
        ENNReal.ofReal (Real.log (Nat.ceil (Real.exp y) + 1)) := by
    simpa [RelEntropy.of_npow (f := f) ρ σ n] using
      integer_bound_aux (f := f) (N := Nat.ceil (Real.exp y))
        (MState.npow ρ n) (MState.npow σ n) (by
          exact (MState.npow_le_exp_smul h n).trans <| smul_le_smul_of_nonneg_right
            (by dsimp [y]; exact (Nat.le_ceil _).trans (by norm_num))
            (MState.npow σ n).nonneg)
  have hpow_bound_real :
      (n : ℝ) * (f ρ σ.M).toReal ≤
        Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (Real.log_nonneg
        (show (1 : ℝ) ≤ Nat.ceil (Real.exp y) + 1 by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)))] using
      (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hfin) ENNReal.ofReal_ne_top).2
        hpow_bound'
  have hlog_upper : Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) ≤ y + Real.log 3 := by
    refine (show Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) ≤ Real.log (3 * Real.exp y) from
      Real.log_le_log (by positivity) ?_).trans_eq ?_
    · nlinarith [(Nat.ceil_lt_add_one (Real.exp_nonneg y)).le,
        (show (1 : ℝ) ≤ Real.exp y by rw [Real.one_le_exp_iff]; dsimp [y]; positivity)]
    · rw [Real.log_mul (by positivity : (3 : ℝ) ≠ 0) (Real.exp_pos y).ne', Real.log_exp]
      ring
  dsimp [y, δ] at hgap
  nlinarith

/-- The relative max-entropy is a lower bound on all relative entropies. -/
theorem le_max [RelEntropy f] (ρ σ : MState d) : f ρ σ.M ≤ max ρ σ.M := by
  by_cases hx : ∃ x : ℝ, ρ.M ≤ Real.exp x • σ.M
  · obtain ⟨x, hx⟩ := hx
    let y : ℝ := Max.max x 0
    have hy0 : 0 ≤ y := by simp [y]
    have hy : ρ.M ≤ Real.exp y • σ.M := by
      exact hx.trans <| smul_le_smul_of_nonneg_right
        (Real.exp_le_exp.mpr (show x ≤ y by dsimp [y]; exact le_max_left _ _)) σ.nonneg
    have hfin : f ρ σ.M ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_le_exp (f := f) ρ σ hy0 hy)
    exact (ENNReal.toReal_le_toReal hfin
      (by simp [max, (show ∃ x : ℝ, ρ.M ≤ Real.exp x • σ.M from ⟨x, hx⟩)])).1 <| by
      rw [RelEntropy.toReal_max (ρ := ρ) (σ := σ.M)]
      let S : Set ℝ := ((↑) '' {x : ℝ≥0 | ρ.M ≤ Real.exp x • σ.M})
      refine le_csInf ⟨(⟨y, hy0⟩ : ℝ≥0), ⟨⟨y, hy0⟩, hy, rfl⟩⟩ ?_
      intro a ha
      rcases ha with ⟨z, hz, rfl⟩
      simpa [ENNReal.toReal_ofReal z.2] using
        (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2
          (le_of_le_exp (f := f) ρ σ z.2 hz)
  · simp [max, hx]

end RelEntropy
