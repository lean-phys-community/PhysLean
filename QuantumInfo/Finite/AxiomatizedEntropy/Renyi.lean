/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Finite.AxiomatizedEntropy.Defs
public import QuantumInfo.Finite.Entropy.DPI
public import QuantumInfo.Finite.Entanglement

/-! # Quantum Relative Entropy and α-Renyi Entropy -/

@[expose] public section


variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped RealInnerProductSpace

namespace AxiomatizedEntropy

/-- A conservative wrapper around the actual quantum relative entropy. On normalized PSD inputs
it agrees with `_root_.qRelativeEnt`; away from the state space we leave the value at `0`. -/
@[irreducible]
noncomputable def qRelativeEnt (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  open Classical in
  if hσ : σ.trace = 1 ∧ 0 ≤ σ then
    let σ' : MState d := { M := σ, nonneg := hσ.2, tr := hσ.1 }
    _root_.qRelativeEnt ρ σ'
  else
    0

@[simp]
theorem qRelativeEnt_state (ρ σ : MState d) :
    qRelativeEnt ρ (σ : HermitianMat d ℂ) = _root_.qRelativeEnt ρ σ := by
  rw [qRelativeEnt, dif_pos ⟨σ.tr, σ.nonneg⟩]

private lemma uniform_log [Nonempty d] :
    (MState.uniform : MState d).M.log =
      HermitianMat.diagonal ℂ (fun _ => - Real.log (Fintype.card d)) := by
  rw [MState.uniform, MState.ofClassical, HermitianMat.log, HermitianMat.cfc_diagonal]
  congr 1
  funext _
  simp [ProbDistribution.uniform_def, Real.log_inv]

instance : RelEntropy qRelativeEnt where
  DPI := by
    intro d₁ d₂ _ _ _ _ ρ σ Λ
    simpa [qRelativeEnt_state] using
      (sandwichedRenyiEntropy_DPI_of_one_le (d := d₁) (d₂ := d₂) (α := 1)
        (hα := le_rfl) (ρ := ρ) (σ := σ) (Φ := Λ))
  of_kron := by
    intro d₁ d₂ _ _ _ _ ρ₁ σ₁ ρ₂ σ₂
    rw [qRelativeEnt_state, qRelativeEnt_state, qRelativeEnt_state]
    exact _root_.qRelativeEnt_additive ρ₁ σ₁ ρ₂ σ₂
  normalized := by
    intro d _ _ _ i
    let x : NNReal := ⟨Real.log (Fintype.card d), Real.log_nonneg (mod_cast Fintype.card_pos)⟩
    have hker : (MState.uniform : MState d).M.ker ≤ (MState.ofClassical (.constant i)).M.ker := by
      rw [(HermitianMat.nonSingular_iff_ker_bot (A := (MState.uniform : MState d).M)).mp
        (HermitianMat.nonSingular_of_posDef MState.uniform_posDef)]
      exact bot_le
    have hicul : ⟪(MState.ofClassical (.constant i)).M, (MState.uniform : MState d).M.log⟫ =
        - Real.log (Fintype.card d) := by
      rw [uniform_log, HermitianMat.inner_eq_re_trace, MState.ofClassical,
        HermitianMat.diagonal_mat, HermitianMat.diagonal_mat, Matrix.diagonal_mul_diagonal,
        Matrix.trace_diagonal]
      classical
      rw [Finset.sum_eq_single i]
      · simp [ProbDistribution.constant_eq]
        simpa using (Complex.log_ofReal_re (Fintype.card d : ℝ))
      · intro j _ hj; rw [ProbDistribution.constant_eq, if_neg fun h => hj h.symm]; simp
      · intro h; exact (h (Finset.mem_univ i)).elim
    apply EReal.coe_ennreal_injective
    have hq := _root_.qRelativeEnt_eq_neg_Sᵥₙ_add
      (ρ := MState.ofClassical (.constant i)) (σ := MState.uniform)
    rw [if_pos hker, Sᵥₙ_ofClassical, Hₛ_constant_eq_zero, hicul] at hq
    simp [qRelativeEnt_state, hq, EReal.coe_nnreal_eq_coe_real]

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    (qRelativeEnt ρ σ : EReal) = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simpa [qRelativeEnt_state] using (_root_.qRelativeEnt_ker (ρ := ρ) (σ := σ) h)

end AxiomatizedEntropy
