/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.States.Pure.Braket
public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled
public import QuantumInfo.ClassicalInfo.Entropy

/-!
Quantum notions of information and entropy.

We start with quantities of _entropy_, namely the von Neumann entropy and its derived quantities:
 * Quantum conditional entropy, `qConditionalEnt`
 * Quantum mutual information, `qMutualInfo`
 * Coherent information, `coherentInfo`
 * Quantum conditional mutual information, `qcmi`.
and then prove facts about them.
-/

@[expose] public section

/- # TODO / Goals:

--QConditionalEnt chain rule

--Quantum discord

--Entanglement:
-- * Entanglement entropy
-- * Entanglement of formation
-- * Relative entropy of entanglement
-- * Squashed entanglement
-- * Negativity (+ facts here: https://www.quantiki.org/wiki/strong-sub-additivity)
-- * Distillable entanglement (One way, Two way, --> Coherent Information)
-- * Entanglement cost (!= EoF, prove; asymptotically == EoF.)
-- Bound entanglement (Prop)

-- https://arxiv.org/pdf/quant-ph/0406162

--https://en.wikipedia.org/wiki/Von_Neumann_entropy#Properties
--  in particular https://www.quantiki.org/wiki/strong-sub-additivity

--https://en.wikipedia.org/wiki/Quantum_relative_entropy#Relation_to_other_quantum_information_quantities

--QMutualInfo is symmetric

--TODO:
-- * Classical conditional entropy is nonnegative
-- * Not true of qConditionalEnt
-- * These measures track their classical values on `MState.ofClassical` states
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}

open scoped InnerProductSpace RealInnerProductSpace

section entropy

/-- Von Neumann entropy of a mixed state. -/
def Sᵥₙ (ρ : MState d) : ℝ :=
  Hₛ ρ.spectrum

/-- The Quantum Conditional Entropy S(ρᴬ|ρᴮ) is given by S(ρᴬᴮ) - S(ρᴮ). -/
def qConditionalEnt (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ - Sᵥₙ ρ.traceLeft

/-- The Quantum Mutual Information I(A:B) is given by S(ρᴬ) + S(ρᴮ) - S(ρᴬᴮ). -/
def qMutualInfo (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ

/-- The Coherent Information of a state ρ passing through a channel Λ is the negative conditional
  entropy of the image under Λ of the purification of ρ. -/
def coherentInfo (ρ : MState d₁) (Λ : CPTPMap d₁ d₂) : ℝ :=
  let ρPure : MState (d₁ × d₁) := MState.pure ρ.purify
  let ρImg : MState (d₂ × d₁) := Λ.prod (CPTPMap.id (dIn := d₁)) ρPure
  (- qConditionalEnt ρImg)

/-- The Quantum Conditional Mutual Information, I(A;C|B) = S(A|B) - S(A|BC). -/
def qcmi (ρ : MState (dA × dB × dC)) : ℝ :=
  qConditionalEnt ρ.assoc'.traceRight - qConditionalEnt ρ

/-- von Neumman entropy is nonnegative. -/
theorem Sᵥₙ_nonneg (ρ : MState d) : 0 ≤ Sᵥₙ ρ :=
  Hₛ_nonneg _

/-- von Neumman entropy is at most log d. -/
theorem Sᵥₙ_le_log_d (ρ : MState d) : Sᵥₙ ρ ≤ Real.log (Finset.card Finset.univ (α := d)):=
  Hₛ_le_log_d _

/-- von Neumman entropy of pure states is zero. -/
@[simp]
theorem Sᵥₙ_of_pure_zero (ψ : Ket d) : Sᵥₙ (MState.pure ψ) = 0 := by
  rw [Sᵥₙ, (MState.spectrum_pure_eq_constant ψ).choose_spec, Hₛ_constant_eq_zero]

set_option backward.isDefEq.respectTransparency false in
theorem Sᵥₙ_eq_neg_trace_log (ρ : MState d) : Sᵥₙ ρ = -⟪ρ.M.log, ρ.M⟫ := by
  rw [HermitianMat.log, HermitianMat.inner_eq_re_trace, Matrix.trace_mul_comm,
    ρ.M.trace_mul_cfc]
  simp [Sᵥₙ, Hₛ, H₁, Real.negMulLog, MState.spectrum, ProbDistribution.mk',
    ProbDistribution.prob]

/-- Von Neumann entropy is the trace of the matrix function `x ↦ -x log x`. -/
theorem Sᵥₙ_eq_trace_cfc_negMulLog (ρ : MState d) :
    Sᵥₙ ρ = (ρ.M.cfc Real.negMulLog).trace := by
  rw [HermitianMat.trace_cfc_eq]
  simp [Sᵥₙ, Hₛ, H₁, MState.spectrum, ProbDistribution.mk', ProbDistribution.prob]

@[simp]
theorem Sᵥₙ_unit_zero [Unique d] (ρ : MState d) : Sᵥₙ ρ = 0 :=
  le_antisymm (by simpa using Sᵥₙ_le_log_d ρ) (Sᵥₙ_nonneg ρ)

/-- Von Neumann entropy is invariant under relabeling of the basis. -/
@[simp]
theorem Sᵥₙ_relabel (ρ : MState d₁) (e : d₂ ≃ d₁) :
    Sᵥₙ (ρ.relabel e) = Sᵥₙ ρ := by
  simp [Sᵥₙ_eq_neg_trace_log]

/-- Von Neumann entropy is unchanged under SWAP. TODO: All unitaries-/
@[simp]
theorem Sᵥₙ_of_SWAP_eq (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.SWAP = Sᵥₙ ρ :=
  Hₛ_eq_of_multiset_map_eq _ _ (ρ.multiset_spectrum_relabel_eq (Equiv.prodComm d₁ d₂).symm)

/-- Von Neumann entropy is unchanged under assoc. -/
@[simp]
theorem Sᵥₙ_of_assoc_eq (ρ : MState ((d₁ × d₂) × d₃)) : Sᵥₙ ρ.assoc = Sᵥₙ ρ :=
  Hₛ_eq_of_multiset_map_eq _ _ (ρ.multiset_spectrum_relabel_eq _)

/-- Von Neumann entropy is unchanged under assoc'. -/
@[simp]
theorem Sᵥₙ_of_assoc'_eq (ρ : MState (d₁ × (d₂ × d₃))) : Sᵥₙ ρ.assoc' = Sᵥₙ ρ := by
  rw [← Sᵥₙ_of_assoc_eq, ρ.assoc_assoc']

@[fun_prop]
theorem selfAdjointMap_Continuous {𝕜 : Type*} [RCLike 𝕜] :
    Continuous (IsMaximalSelfAdjoint.selfadjMap : 𝕜 →+ ℝ) := by
  rw [IsMaximalSelfAdjoint.RCLike_selfadjMap]
  fun_prop

@[fun_prop]
theorem HermitianMat.trace_Continuous {d 𝕜 : Type*} [Fintype d] [RCLike 𝕜]  :
    Continuous (HermitianMat.trace : HermitianMat d 𝕜 → ℝ) := by
  rw [funext HermitianMat.trace_eq_re_trace]
  fun_prop

@[fun_prop]
theorem Sᵥₙ_continuous : Continuous (Sᵥₙ (d := d)) := by
  rw [funext Sᵥₙ_eq_trace_cfc_negMulLog]
  fun_prop

section partial_trace_pure
--TODO Cleanup

/--
Convert a vector on a product space to a matrix.
-/
def vecToMat {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] (v : d₁ × d₂ → ℂ) : Matrix d₁ d₂ ℂ :=
  Matrix.of (fun i j => v (i, j))

/--
The right partial trace of a pure state is the product of the matrix representation
and its conjugate transpose.
-/
private lemma traceRight_eq_mul_conjTranspose (ψ : Ket (d₁ × d₂)) :
    (MState.pure ψ).traceRight.M.val = (vecToMat ψ.vec) * (vecToMat ψ.vec).conjTranspose := by
  aesop (add simp vecToMat)

/-
The left partial trace of a pure state is the product of the transpose of the
matrix representation and its conjugate.
-/
lemma traceLeft_eq_transpose_mul_conj (ψ : Ket (d₁ × d₂)) :
    (MState.pure ψ).traceLeft.M.val = (vecToMat ψ.vec).transpose * (vecToMat ψ.vec).map star := by
  aesop (add simp vecToMat)

/--
The left partial trace of `vecToMat` is the transpose of M^H * M.
-/
private lemma traceLeft_eq_transpose_conjTranspose_mul (ψ : Ket (d₁ × d₂)) :
    (MState.pure ψ).traceLeft.M.val =
    ((vecToMat ψ.vec).conjTranspose * (vecToMat ψ.vec)).transpose := by
  rw [traceLeft_eq_transpose_mul_conj, Matrix.transpose_mul]
  rfl

/--
Shannon entropy is determined by the multiset of non-zero probabilities.
-/
private lemma Hₛ_eq_of_nonzero_multiset_eq {α β : Type*} [Fintype α] [Fintype β]
  (d₁ : ProbDistribution α) (d₂ : ProbDistribution β)
  (h : (Finset.univ.val.map d₁.prob).filter (· ≠ 0) = (Finset.univ.val.map d₂.prob ).filter (· ≠ 0)) :
    Hₛ d₁ = Hₛ d₂ := by
  rw [Hₛ, Hₛ,
    ← Finset.sum_filter_of_ne (p := (d₁.prob · ≠ 0)) fun x _ hne h0 ↦ hne (by simp [h0]),
    ← Finset.sum_filter_of_ne (p := (d₂.prob · ≠ 0)) fun x _ hne h0 ↦ hne (by simp [h0])]
  convert congr_arg (fun m ↦ (m.map H₁).sum) h using 1 <;>
    simp [Finset.sum, Multiset.filter_map]

/--
If two polynomials differ by a factor of X^k, their non-zero roots are the same.
-/
private lemma nonzero_roots_eq_of_charpoly_eq_X_pow {R : Type*} [CommRing R] [IsDomain R]
  [DecidableEq R] (p q : Polynomial R) (k : ℕ) (h : p = Polynomial.X ^ k * q) :
    p.roots.filter (· ≠ 0) = q.roots.filter (· ≠ 0) := by
  by_cases hq : q = 0 <;> simp_all [ Polynomial.roots_mul, Polynomial.X_ne_zero ]

/--
The non-zero eigenvalues of AB and BA are the same.
-/
private lemma nonzero_eigenvalues_eq_of_mul_comm {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] (A : Matrix n m ℂ) (B : Matrix m n ℂ) :
    (A * B).charpoly.roots.filter (· ≠ 0) = (B * A).charpoly.roots.filter (· ≠ 0) := by
  rw [← nonzero_roots_eq_of_charpoly_eq_X_pow _ ((A * B).charpoly) (Fintype.card m) rfl,
    A.charpoly_mul_comm' B, nonzero_roots_eq_of_charpoly_eq_X_pow _ _ _ rfl]

/--
If two states have the same non-zero eigenvalues (spectrum probabilities), they have
the same von Neumann entropy.
-/
private lemma Sᵥₙ_eq_of_nonzero_eigenvalues_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂)
    (h : (Finset.univ.val.map ρ₁.spectrum.prob).filter (· ≠ 0) =
      (Finset.univ.val.map ρ₂.spectrum.prob).filter (· ≠ 0)) :
    Sᵥₙ ρ₁ = Sᵥₙ ρ₂ :=
  Hₛ_eq_of_nonzero_multiset_eq _ _ h

/--
Filtering non-zero elements commutes with mapping `RCLike.ofReal` for multisets.
-/
private lemma multiset_filter_map_ofReal_eq {R : Type*} [RCLike R] (M : Multiset ℝ) :
    (M.map (RCLike.ofReal : ℝ → R)).filter (· ≠ 0) = (M.filter (· ≠ 0)).map RCLike.ofReal := by
  simp [Multiset.filter_map]

/-
The non-zero roots of the characteristic polynomial are the non-zero eigenvalues mapped
to complex numbers.
-/
private lemma charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    A.charpoly.roots.filter (· ≠ 0) = ((Finset.univ.val.map hA.eigenvalues).filter (· ≠ 0)).map RCLike.ofReal := by
  rw [hA.roots_charpoly_eq_eigenvalues, ← Multiset.map_map, multiset_filter_map_ofReal_eq]

/--
Mapping `RCLike.ofReal` over a multiset is injective.
-/
private lemma multiset_map_ofReal_injective {R : Type*} [RCLike R] {M N : Multiset ℝ} :
    M.map (RCLike.ofReal : ℝ → R) = N.map RCLike.ofReal ↔ M = N :=
  (Multiset.map_injective RCLike.ofReal_injective).eq_iff

/--
If the non-zero roots of the characteristic polynomials of two states are equal,
their von Neumann entropies are equal.
-/
private lemma Sᵥₙ_eq_of_charpoly_roots_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂)
    (h : (ρ₁.M.1.charpoly.roots.filter (· ≠ 0)) = (ρ₂.M.1.charpoly.roots.filter (· ≠ 0))) :
    Sᵥₙ ρ₁ = Sᵥₙ ρ₂ := by
  replace h := multiset_map_ofReal_injective.mp <|
    (charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero _ ρ₁.M.H).symm.trans <|
      h.trans (charpoly_roots_filter_ne_zero_eq_eigenvalues_filter_ne_zero _ ρ₂.M.H)
  refine Sᵥₙ_eq_of_nonzero_eigenvalues_eq ρ₁ ρ₂ (Multiset.map_injective (f := (↑· : Prob → ℝ))
    (fun a b hab ↦ by aesop) ?_)
  simpa [Multiset.filter_map, MState.spectrum, ProbDistribution.mk', ProbDistribution.prob,
    Function.comp_def, Subtype.ext_iff] using h

end partial_trace_pure

/-- von Neumman entropies of the left- and right- partial trace of pure states are equal. -/
theorem Sᵥₙ_of_partial_eq (ψ : Ket (d₁ × d₂)) :
    Sᵥₙ (MState.pure ψ).traceLeft = Sᵥₙ (MState.pure ψ).traceRight := by
  apply Sᵥₙ_eq_of_charpoly_roots_eq
  rw [traceLeft_eq_transpose_conjTranspose_mul, traceRight_eq_mul_conjTranspose,
    ← Matrix.charpoly_transpose]
  exact nonzero_eigenvalues_eq_of_mul_comm _ _

/-- Quantum conditional entropy is symmetric for pure states. -/
@[simp]
theorem qConditionalEnt_of_pure_symm (ψ : Ket (d₁ × d₂)) :
    qConditionalEnt (MState.pure ψ).SWAP = qConditionalEnt (MState.pure ψ) := by
  simp [qConditionalEnt, Sᵥₙ_of_partial_eq]

/-- Quantum mutual information is symmetric. -/
@[simp]
theorem qMutualInfo_symm (ρ : MState (d₁ × d₂)) :
    qMutualInfo ρ.SWAP = qMutualInfo ρ := by
  simp [qMutualInfo, add_comm]

/-- For a pure state, the entropy of one subsystem equals the entropy of its complement,
even after relabeling. -/
@[simp]
theorem Sᵥₙ_pure_complement (ψ : Ket d₁) (e : d₂ × d₃ ≃ d₁) :
    Sᵥₙ ((MState.pure ψ).relabel e).traceLeft = Sᵥₙ ((MState.pure ψ).relabel e).traceRight := by
  obtain ⟨ψ', hψ'⟩ := MState.relabel_pure_exists ψ e
  simp only [hψ', Sᵥₙ_of_partial_eq]

end entropy
