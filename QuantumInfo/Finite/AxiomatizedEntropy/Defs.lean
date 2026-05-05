/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Dennj Osele
-/
module

public import QuantumInfo.ClassicalInfo.Entropy
public import QuantumInfo.ClassicalInfo.Hellinger
public import QuantumInfo.Finite.MState
public import QuantumInfo.Finite.CPTPMap
public import QuantumInfo.Finite.POVM
public import QuantumInfo.Finite.Entropy.Relative

@[expose] public section

/-! # Generalized quantum entropy and relative entropy

Here we define a broad notion of entropy axiomatically, `Entropy`, and the Prop
`Entropy f` means that the function `f : MState → ℝ` acts like a generalized kind of quantum
entropy. For instance, min-, max-, α-Renyi, and von Neumann entropies all fall
into this category. We prove various properties about the entropy for anything
supporting this type class. Any entropy automatically gets corresponding notions
of conditional entropy, mutual information, and so on.

Similarly, `RelEntropy f` means that `f : MState → HermitianMat → ENNReal` is a kind of
relative entropy. Every `RelEntropy` leads to a notion of entropy, as well, by
fixing one argument to the fully mixed state.

Of course relative entropies are "usually" used with a pair of (normalized) quantum
states, but it's still very common in literature to specifically let the second
argument be an arbitrary (PSD, Hermitian) matrix, so we do allow this. The behavior
when not a density matrix is left unspecified by the axioms.

In terms of the file structure, we start with `RelEntropy` as the more "general"
function, and then derive much of `Entropy` from it.

## References:

 - [Khinchin’s Fourth Axiom of Entropy Revisited](https://www.mdpi.com/2571-905X/6/3/49)
 - [α-z Relative Entropies](https://warwick.ac.uk/fac/sci/maths/research/events/2013-2014/statmech/su/Nilanjana-slides.pdf)
 - Watrous's notes, [Max-relative entropy and conditional min-entropy](https://cs.uwaterloo.ca/~watrous/QIT-notes/QIT-notes.02.pdf)
 - [Quantum Relative Entropy - An Axiomatic Approach](https://www.marcotom.info/files/entropy-masterclass2022.pdf)
by Marco Tomamichel
 - [StackExchange](https://quantumcomputing.stackexchange.com/a/12953/10115)

-/

noncomputable section
universe u

open ComplexOrder
open scoped NNReal
open scoped ENNReal
open scoped Kronecker
open scoped HermitianMat

variable (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → HermitianMat d ℂ → ℝ≥0∞)

/-- The axioms to be a well-behaved quantum relative entropy, as given by
[Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf).

This simpler class allows for _trivial_ relative entropies, such as `-log tr(ρ⁰σ)`.
Use the mixin `RelEntropy.Nontrivial` to only allow nontrivial relative entropies. -/
class RelEntropy : Prop where
  /-- The data processing inequality -/
  DPI {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ σ : MState d₁) (Λ : CPTPMap d₁ d₂) : f (Λ ρ) (Λ σ) ≤ f ρ σ
  /-- Entropy is additive under tensor products -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂), f (ρ₁ ⊗ᴹ ρ₂) (σ₁ ⊗ᴹ σ₂) = f ρ₁ σ₁ + f ρ₂ σ₂
  /-- Normalization of entropy to be `ln N` for a pure state vs. uniform on `N` many states. -/
  normalized {d : Type u} [fin : Fintype d] [DecidableEq d] [Nonempty d] (i : d) :
    f (.ofClassical (.constant i)) MState.uniform.M =
      some ⟨Real.log fin.card, Real.log_nonneg (mod_cast Fintype.card_pos)⟩

/-- Mixin on top of `RelEntropy` that rules out trivial relative entropies (those that vanish
on every pair of full-support states). See [Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf). -/
class RelEntropy.Nontrivial [RelEntropy f] where
  /-- Nontriviality condition for a relative entropy: some pair of full-support states has
  positive relative entropy. This is the negation of Tomamichel's definition of a trivial
  relative entropy, which vanishes on all full-support state pairs. -/
  nontrivial : ∃ (d : Type u) (_ : Fintype d) (_ : DecidableEq d) (ρ σ : MState d),
    ρ.M.support = ⊤ ∧ σ.M.support = ⊤ ∧ 0 < f ρ σ

namespace RelEntropy

variable {d : Type u} [Fintype d] [DecidableEq d]
variable {d₂ : Type u} [Fintype d₂] [DecidableEq d₂]

variable [RelEntropy f]

section possibly_trivial

/-
At some point we might want to offer a different constructor so that `normalized` only checks
it for domains of size 2, which is sufficient (see Tomamichel's proof). In that case, the
fact that it's still zero when `Unique d` has to be proven, and this (now used) chunk of a proof
can be used in part for that:

-- have h_uniq (ρ') := (Subsingleton.allEq ρ ρ').symm
-- have h_kron := of_kron (f := f) ρ ρ ρ ρ
-- let e : d ≃ (d × d) := (Equiv.prodUnique d d).symm
-- rw [← relabel_eq f e] at h_kron
-- rw [h_uniq ((ρ⊗ρ).relabel e)] at h_kron
-- rw [h_uniq σ]

At that point we need the fact that it's not `⊤`, and then it must be zero.

-/

/-- Relabelling a state with `CPTPMap.ofEquiv` leaves relative entropies unchanged. -/
@[simp]
theorem ofEquiv_eq (e : d ≃ d₂) (ρ σ : MState d) :
    f (CPTPMap.ofEquiv e ρ) (CPTPMap.ofEquiv e σ) = f ρ σ := by
  apply le_antisymm
  · apply DPI
  · convert DPI (f := f) ((CPTPMap.ofEquiv e) ρ) ((CPTPMap.ofEquiv e) σ) (CPTPMap.ofEquiv e.symm)
    all_goals
      symm
      exact congrFun (CPTPMap.equiv_inverse e.symm) _

/-- Relabelling a state with `MState.relabel` leaves relative entropies unchanged. -/
@[simp]
theorem relabel_eq (e : d₂ ≃ d) (ρ σ : MState d) :
    f (ρ.relabel e) (σ.relabel e) = f ρ σ := by
  exact ofEquiv_eq (f := f) e.symm ρ σ

--Tomamichel's "4. Positivity" theorem is implicit true in our description because we
--only allow ENNReals. The only part to prove is that "D(ρ‖σ) = 0 if ρ = σ".

/-- The relative entropy is zero between any two states on a 1-D Hilbert space. -/
private lemma wrt_self_eq_zero' [Unique d] (ρ σ : MState d) : f ρ σ = 0 := by
  convert normalized (f := f) (d := d) default
  · exact Subsingleton.allEq _ _
  · exact Subsingleton.allEq _ _
  · simp [Fintype.card_unique, Real.log_one]
    rfl

/-- The relative entropy `D(ρ‖ρ) = 0`. -/
@[simp]
theorem wrt_self_eq_zero (ρ : MState d) : f ρ ρ.M = 0 := by
  rw [← nonpos_iff_eq_zero, ← wrt_self_eq_zero' f (d := PUnit) default default]
  convert DPI (f := f) _ _ (CPTPMap.replacement ρ)
  all_goals rw [CPTPMap.replacement_apply]

end possibly_trivial

section bounds

open Prob in
/-- A support-test lower bound for relative entropies.

This is not the standard quantum relative min-entropy on state inputs: for density-matrix
second arguments it collapses to zero, as `min_state_eq_zero` shows. The name is kept because
it is the min-side bound paired with `max` in this axiomatized API. -/
def min (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  —log ⟨ρ.exp_val (HermitianMat.projLE 0 σ),
    ρ.exp_val_prob ⟨HermitianMat.projLE_nonneg 0 σ, HermitianMat.projLE_le_one 0 σ⟩⟩

@[aesop (rule_sets := [finiteness]) simp]
theorem min_eq_top_iff (ρ : MState d) (σ : HermitianMat d ℂ) :
    (min ρ σ) = ⊤ ↔ ρ.M.support ≤ (HermitianMat.projLE 0 σ).ker := by
  rw [min, Prob.negLog_eq_top_iff]
  constructor
  · intro h
    have h0 : ρ.exp_val (HermitianMat.projLE 0 σ) = 0 := by
      simpa using congrArg (fun p : Prob => (p : ℝ)) h
    exact (ρ.exp_val_eq_zero_iff (HermitianMat.projLE_nonneg 0 σ)).mp h0
  · intro h
    exact Subtype.ext ((ρ.exp_val_eq_zero_iff (HermitianMat.projLE_nonneg 0 σ)).mpr h)

protected theorem toReal_min (ρ : MState d) (σ : HermitianMat d ℂ) :
    (min ρ σ).toReal = -Real.log (ρ.exp_val (HermitianMat.projLE 0 σ)) := by
  simp [min,
    Prob.negLog_pos_Real (p := ⟨ρ.exp_val (HermitianMat.projLE 0 σ),
      ρ.exp_val_prob ⟨HermitianMat.projLE_nonneg 0 σ, HermitianMat.projLE_le_one 0 σ⟩⟩)]


/-- On state inputs, the current support-based `min` quantity is always zero. -/
@[simp]
theorem min_state_eq_zero (ρ σ : MState d) : min ρ σ.M = 0 := by
  have hproj : HermitianMat.projLE 0 σ.M = 1 := by
    rw [HermitianMat.projLE_zero_cfc]
    calc σ.M.cfc (fun x ↦ if 0 ≤ x then 1 else 0) = σ.M.cfc (fun _ ↦ (1 : ℝ)) :=
          HermitianMat.cfc_congr_of_nonneg σ.nonneg fun _ hx => by simpa using hx
      _ = 1 := by simp [HermitianMat.cfc_const (A := σ.M) (r := (1 : ℝ))]
  simp [min, show (⟨ρ.exp_val (HermitianMat.projLE 0 σ.M),
    ρ.exp_val_prob ⟨HermitianMat.projLE_nonneg 0 σ.M, HermitianMat.projLE_le_one 0 σ.M⟩⟩ : Prob) = 1
    from Subtype.ext (by change ρ.exp_val _ = 1; rw [hproj, MState.exp_val_one])]

/-- The current support-based `min` quantity does not satisfy the normalization axiom of `RelEntropy`. -/
theorem not_RelEntropy_min : ¬ RelEntropy min := by
  intro hmin
  have := congrArg ENNReal.toReal (hmin.normalized (d := ULift (Fin 2)) (i := ⟨0⟩))
  simp at this; linarith [Real.log_pos one_lt_two]

theorem not_Nontrivial_min [RelEntropy min] : ¬Nontrivial min := by
  rintro ⟨h⟩
  obtain ⟨d, _, _, ρ, σ, -, -, hpos⟩ := h
  simp at hpos

omit [RelEntropy f] in
/-- The relative min-entropy is a lower bound on all relative entropies. -/
theorem min_le (ρ σ : MState d) : min ρ σ.M ≤ f ρ σ.M := by
  simp

open Classical in
/-- Quantum relative max-entropy. -/
def max (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
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

/-- A full-support state dominates every other state up to an integer scalar. -/
private theorem exists_le_nat_smul_of_fullSupport (ρ σ : MState d)
    (hσ : σ.M.support = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ρ.M ≤ ((N + 1 : ℝ) • σ.M) := by
  letI : σ.M.NonSingular := HermitianMat.nonSingular_iff_support_top.mpr hσ
  have hexp : ∃ x : ℝ, ρ.M ≤ Real.exp x • σ.M := by
    by_contra h
    exact (RelEntropy.max_not_top ρ σ.M σ.nonneg).mpr
      (by simp [HermitianMat.nonSingular_ker_bot]) (by simp [max, h])
  obtain ⟨x, hx⟩ := hexp
  refine ⟨Nat.ceil (Real.exp x), Nat.ceil_pos.mpr (Real.exp_pos x), ?_⟩
  exact hx.trans <| smul_le_smul_of_nonneg_right ((Nat.le_ceil _).trans (by norm_num)) σ.nonneg

/-- The output of Tomamichel's preparation channel on the first binary point. -/
private def binaryPrepOne (γ ω : MState d) (s t : ℝ) (hden : 0 < 1 - s - t)
    (h : t • γ.M ≤ (1 - s) • ω.M) : MState d where
  M := (1 - s - t)⁻¹ • ((1 - s) • ω.M - t • γ.M)
  nonneg := smul_nonneg (inv_nonneg.mpr hden.le) (sub_nonneg.mpr h)
  tr := by
    simpa [HermitianMat.trace_smul, HermitianMat.trace_sub, γ.tr, ω.tr] using
      inv_mul_cancel₀ hden.ne'

/-- The output of Tomamichel's preparation channel on the second binary point. -/
private def binaryPrepZero (γ ω : MState d) (s t : ℝ) (hden : 0 < 1 - s - t)
    (h : s • ω.M ≤ (1 - t) • γ.M) : MState d where
  M := (1 - s - t)⁻¹ • ((1 - t) • γ.M - s • ω.M)
  nonneg := smul_nonneg (inv_nonneg.mpr hden.le) (sub_nonneg.mpr h)
  tr := by
    simp [HermitianMat.trace_smul, HermitianMat.trace_sub, γ.tr, ω.tr]
    field_simp [hden.ne']
    ring_nf

/-- A binary coin lifted to the working universe. -/
private def uliftCoin (p : Prob) : ProbDistribution (ULift.{u} (Fin 2)) :=
  (ProbDistribution.congr Equiv.ulift.symm) (.coin p)

private def cqPrepareChoiH {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    HermitianMat (d × κ) ℂ :=
  ∑ i, HermitianMat.kronecker (τ i).M (MState.ofClassical (.constant i)).M

private def cqPrepareChoi {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    Matrix (d × κ) (d × κ) ℂ :=
  (cqPrepareChoiH (d := d) τ).mat

private def cqPrepareMap {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    MatrixMap κ d ℂ where
  toFun X := fun b₁ b₂ => ∑ i, X i i * (τ i).m b₁ b₂
  map_add' X Y := by
    ext b₁ b₂
    simp [Matrix.add_apply, Finset.sum_add_distrib, add_mul]
  map_smul' c X := by
    ext b₁ b₂
    simp [Matrix.smul_apply, Finset.mul_sum, mul_assoc]

private theorem cqPrepareMap_choi {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    (cqPrepareMap (d := d) τ).choi_matrix = cqPrepareChoi (d := d) τ := by
  ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
  simp only [MatrixMap.choi_matrix, cqPrepareMap, Matrix.single,
    cqPrepareChoi, cqPrepareChoiH, HermitianMat.mat_finset_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  show (if a₁ = x ∧ a₂ = x then 1 else 0) * (τ x).m b₁ b₂ =
    (τ x).m b₁ b₂ * (HermitianMat.diagonal ℂ (fun x₁ => ((ProbDistribution.constant x) x₁ : ℝ))).mat a₁ a₂
  rw [HermitianMat.diagonal_mat]
  aesop (add simp [Matrix.diagonal, ProbDistribution.constant_eq, Ne.symm])

private theorem cqPrepareChoi_psd {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    (cqPrepareChoi (d := d) τ).PosSemidef := by
  change ((cqPrepareChoiH (d := d) τ).mat).PosSemidef
  have hnonneg : (0 : HermitianMat (d × κ) ℂ) ≤ cqPrepareChoiH (d := d) τ := by
    unfold cqPrepareChoiH
    exact Finset.sum_nonneg fun i _ =>
      HermitianMat.kronecker_nonneg (τ i).nonneg (MState.ofClassical (.constant i)).nonneg
  exact HermitianMat.zero_le_iff.mp hnonneg

private theorem cqPrepareChoi_traceLeft {κ : Type u} [Fintype κ] [DecidableEq κ]
    (τ : κ → MState d) :
    (cqPrepareChoi (d := d) τ).traceLeft = 1 := by
  rw [← cqPrepareMap_choi (d := d) τ, ← MatrixMap.IsTracePreserving_iff_trace_choi]
  intro X
  change ∑ x, ∑ i, X i i * (τ i).m x x = X.trace
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, show ∑ x, (τ i).m x x = 1 by
    simpa [Matrix.trace] using (MState.tr' (ρ := τ i))]
  simp [Matrix.diag_apply]

private def cqPrepareCPTP {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    CPTPMap κ d :=
  CPTPMap.CPTP_of_choi_PSD_Tr
    (M := cqPrepareChoi (d := d) τ)
    (cqPrepareChoi_psd (d := d) τ)
    (cqPrepareChoi_traceLeft (d := d) τ)

private theorem cqPrepare_apply_ofClassical {κ : Type u} [Fintype κ] [DecidableEq κ]
    (τ : κ → MState d) (dist : ProbDistribution κ) :
    MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ) (MState.ofClassical dist).m
      = ∑ i, (dist i : ℝ) • (τ i).m := by
  rw [← cqPrepareMap_choi (d := d) τ, MatrixMap.choi_map_inv]
  ext b₁ b₂
  change ∑ i, (Matrix.diagonal fun x => ((dist x : Prob) : ℂ)) i i * (τ i).m b₁ b₂ =
    (∑ i, (dist i : ℝ) • (τ i).m) b₁ b₂
  rw [Matrix.sum_apply]
  simp [Matrix.smul_apply]

private theorem cqPrepare_apply_uliftCoin (τ : ULift (Fin 2) → MState d) (p : Prob) :
    MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ) (MState.ofClassical (uliftCoin p)).m =
      (p : ℝ) • (τ (ULift.up (0 : Fin 2))).m +
        ((1 - p : Prob) : ℝ) • (τ (ULift.up (1 : Fin 2))).m := by
  rw [cqPrepare_apply_ofClassical (d := d) τ (uliftCoin p)]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  have hsum :
      (∑ x : ULift (Fin 2), ↑↑((uliftCoin p) x) * (τ x).m i j) =
        ∑ y : Fin 2, ↑↑((ProbDistribution.coin p) y) * (τ (ULift.up y)).m i j := by
    simpa [uliftCoin, ProbDistribution.congr_apply] using
      (Equiv.sum_comp (Equiv.ulift : ULift (Fin 2) ≃ Fin 2)
        (fun y : Fin 2 => ↑↑((ProbDistribution.coin p) y) * (τ (ULift.up y)).m i j))
  rw [hsum]
  simp [Fin.sum_univ_two]


private def binaryClassicalPostprocess (a b : Prob) :
    CPTPMap (ULift (Fin 2)) (ULift (Fin 2)) :=
  let τ : ULift (Fin 2) → MState (ULift (Fin 2)) := fun i =>
    if i = ULift.up (0 : Fin 2) then MState.ofClassical (uliftCoin a)
    else MState.ofClassical (uliftCoin b)
  CPTPMap.CPTP_of_choi_PSD_Tr
    (M := cqPrepareChoi (d := ULift (Fin 2)) τ)
    (cqPrepareChoi_psd (d := ULift (Fin 2)) τ)
    (cqPrepareChoi_traceLeft (d := ULift (Fin 2)) τ)

private theorem binaryClassicalPostprocess_apply (a b p : Prob) :
    binaryClassicalPostprocess a b (MState.ofClassical (uliftCoin p)) =
      MState.ofClassical (uliftCoin (Prob.mix p a b)) := by
  apply MState.ext_m
  change MatrixMap.of_choi_matrix
      (cqPrepareChoi (d := ULift (Fin 2))
        (fun i : ULift (Fin 2) =>
          if i = ULift.up (0 : Fin 2) then MState.ofClassical (uliftCoin a)
          else MState.ofClassical (uliftCoin b)))
      (MState.ofClassical (uliftCoin p)).m =
    (MState.ofClassical (uliftCoin (Prob.mix p a b))).m
  rw [cqPrepare_apply_uliftCoin]
  ext i j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  all_goals
    simp [MState.m, MState.ofClassical, Matrix.add_apply, Prob.coe_one_minus, uliftCoin,
      ProbDistribution.congr_apply]
    rw [← HermitianMat.mat_apply, HermitianMat.diagonal_mat]
    simp [Matrix.diagonal, Prob.mix, Mixable.mix, Mixable.mix_ab, Prob.coe_one_minus]
  all_goals ring_nf

private theorem uliftCoin_support_top (p : Prob) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (MState.ofClassical (uliftCoin p)).M.support = ⊤ := by
  rw [← HermitianMat.nonSingular_iff_support_top]
  apply HermitianMat.nonSingular_of_posDef
  rw [MState.coe_ofClassical]
  apply Matrix.PosDef.diagonal
  intro i
  rcases i with ⟨i⟩
  fin_cases i
  · simpa [Complex.real_lt_real, uliftCoin, ProbDistribution.congr_apply] using hp0
  · simp [uliftCoin, ProbDistribution.congr_apply, Prob.coe_one_minus]
    exact_mod_cast hp1

private def classicalIndicatorEffect {κ : Type u} [DecidableEq κ] (A : Set κ) :
    HermitianMat κ ℂ := by classical exact HermitianMat.diagonal ℂ fun x => if x ∈ A then 1 else 0

private theorem ofClassical_exp_val_indicator
    {κ : Type u} [Fintype κ] [DecidableEq κ] (dist : ProbDistribution κ) (A : Set κ)
    [DecidablePred (fun x => x ∈ A)] :
    (MState.ofClassical dist).exp_val (classicalIndicatorEffect A) =
      ∑ x, if x ∈ A then (dist x : ℝ) else 0 := by
  rw [classicalIndicatorEffect, MState.exp_val, MState.coe_ofClassical,
    HermitianMat.inner_eq_re_trace]
  simp [Matrix.trace, HermitianMat.diagonal]
  exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp

private theorem exists_effect_exp_val_ne_of_ne (ρ σ : MState d) (hne : ρ ≠ σ) :
    ∃ T : HermitianMat d ℂ, (0 ≤ T ∧ T ≤ 1) ∧ ρ.exp_val T ≠ σ.exp_val T := by
  let A : HermitianMat d ℂ := ρ.M - σ.M
  have hA_not_nonneg : ¬ 0 ≤ A := by
    intro hA_nonneg
    exact hne (MState.ext (eq_of_sub_eq_zero (HermitianMat.ext <|
      (Matrix.PosSemidef.trace_eq_zero_iff (HermitianMat.zero_le_iff.mp hA_nonneg)).1 <|
        (HermitianMat.trace_eq_zero_iff (A := A)).1
          (by simp [A, HermitianMat.trace_sub, ρ.tr, σ.tr]))))
  let B : HermitianMat d ℂ := A⁻
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using HermitianMat.negPart_nonneg A
  have hinner_neg : inner ℝ A B < 0 := by
    simpa [B] using (HermitianMat.inner_negPart_neg_iff (A := A)).2 hA_not_nonneg
  have hB_trace_pos : 0 < B.trace := by
    refine lt_of_le_of_ne (HermitianMat.trace_nonneg hB_nonneg) ?_
    intro htrace
    have hB_zero : B = 0 := HermitianMat.ext <|
      (Matrix.PosSemidef.trace_eq_zero_iff (HermitianMat.zero_le_iff.mp hB_nonneg)).1 <|
        (HermitianMat.trace_eq_zero_iff (A := B)).1 htrace.symm
    rw [hB_zero] at hinner_neg
    simp at hinner_neg
  let T : HermitianMat d ℂ := B.trace⁻¹ • B
  have hT_nonneg : 0 ≤ T := by
    simpa [T] using smul_nonneg (inv_nonneg.mpr hB_trace_pos.le) hB_nonneg
  have hT_le_one : T ≤ 1 := by
    dsimp [T]
    simpa [smul_smul, inv_mul_cancel₀ hB_trace_pos.ne'] using
      smul_le_smul_of_nonneg_left (HermitianMat.le_trace_smul_one hB_nonneg)
        (inv_nonneg.mpr hB_trace_pos.le)
  refine ⟨T, ⟨hT_nonneg, hT_le_one⟩, fun hsame => ?_⟩
  have hzero : inner ℝ A T = 0 := by
    simpa [A, MState.exp_val, inner_sub_left] using sub_eq_zero.mpr hsame
  have hneg : inner ℝ A T < 0 := by
    simpa [T, inner_smul_right] using
      mul_neg_of_pos_of_neg (inv_pos.mpr hB_trace_pos) hinner_neg
  linarith

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
    cqPrepareCPTP (d := d) (fun i : ULift (Fin (M + 1)) =>
      if i = ⟨0⟩ then ρ else tauOfLE (d := d) M hM_pos ρ σ h)
      (MState.uniform : MState (ULift (Fin (M + 1)))) = σ := by
  let x0 : ULift (Fin (M + 1)) := ⟨0⟩
  let τr := tauOfLE (d := d) M hM_pos ρ σ h
  let τ : ULift (Fin (M + 1)) → MState d := fun i => if i = x0 then ρ else τr
  change cqPrepareCPTP (d := d) τ (MState.uniform : MState (ULift (Fin (M + 1)))) = σ
  apply MState.ext_m
  change MatrixMap.of_choi_matrix
      (cqPrepareChoi (d := d) τ)
      (MState.ofClassical ProbDistribution.uniform).m = σ.m
  rw [cqPrepare_apply_ofClassical (d := d) τ ProbDistribution.uniform]
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

private theorem integer_bound_aux (N : ℕ) (ρ σ : MState d)
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
      let Λ : CPTPMap κ d := cqPrepareCPTP (d := d) τ
      have hconst : Λ (MState.ofClassical (.constant x0)) = ρ := by
        apply MState.ext_m
        change MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ)
            (MState.ofClassical (.constant x0)).m = ρ.m
        rw [cqPrepare_apply_ofClassical (d := d) τ (.constant x0)]
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

private def dyadicStatePow (ρ : MState d) : ∀ n, MState (DyadicPow d n)
  | 0 => ρ
  | n + 1 => dyadicStatePow ρ n ⊗ᴹ dyadicStatePow ρ n

private theorem dyadicStatePow_ofClassical (dist : ProbDistribution d) :
    ∀ n, dyadicStatePow (MState.ofClassical dist) n =
      MState.ofClassical (dyadicProbPow dist n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [dyadicStatePow, ih]
      change _ = MState.ofClassical (ProbDistribution.prod _ _)
      ext i j
      simp [MState.prod, MState.ofClassical, ProbDistribution.prod,
        HermitianMat.kronecker_diagonal]

private theorem hellingerOverlap_uliftCoin (p q : Prob) :
    hellingerOverlap (uliftCoin p) (uliftCoin q) =
      Real.sqrt ((p : ℝ) * (q : ℝ)) +
        Real.sqrt ((1 - (p : ℝ)) * (1 - (q : ℝ))) := by
  change (∑ x : ULift (Fin 2),
      Real.sqrt (((ProbDistribution.coin p) x.down : ℝ) *
        ((ProbDistribution.coin q) x.down : ℝ))) = _
  simpa [Fin.sum_univ_two] using
    (Equiv.sum_comp (Equiv.ulift : ULift (Fin 2) ≃ Fin 2)
      fun y : Fin 2 => Real.sqrt (((ProbDistribution.coin p) y : ℝ) *
        ((ProbDistribution.coin q) y : ℝ)))

private theorem exists_likelihood_indicator_effect
    {κ : Type u} [Fintype κ] [DecidableEq κ] (P Q : ProbDistribution κ) (s r : Prob)
    (hoverlap_s : hellingerOverlap P Q ≤ (s : ℝ))
    (hoverlap_r : hellingerOverlap P Q ≤ 1 - (r : ℝ)) :
    ∃ T : HermitianMat κ ℂ, (0 ≤ T ∧ T ≤ 1) ∧
      ∃ α β : Prob,
        (MState.ofClassical P).exp_val T = α ∧
        (MState.ofClassical Q).exp_val T = β ∧
        (α : ℝ) ≤ s ∧ (r : ℝ) ≤ β := by
  classical
  let A : Set κ := {x | (P x : ℝ) ≤ Q x}
  let T : HermitianMat κ ℂ := classicalIndicatorEffect A
  have hT : 0 ≤ T ∧ T ≤ 1 := by
    refine ⟨?_, ?_⟩
    · rw [HermitianMat.zero_le_iff]
      simp [T, classicalIndicatorEffect, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]
      exact fun i => by by_cases hi : i ∈ A <;> simp [hi]
    · rw [← sub_nonneg]
      rw [show T = HermitianMat.diagonal ℂ fun x => if x ∈ A then (1 : ℝ) else 0 from rfl,
        ← HermitianMat.diagonal_one (𝕜 := ℂ),
        ← HermitianMat.diagonal_sub, HermitianMat.zero_le_iff, HermitianMat.diagonal_mat,
        Matrix.posSemidef_diagonal_iff]
      exact fun i => by by_cases hi : i ∈ A <;> simp [hi]
  refine ⟨T, hT,
    ⟨(MState.ofClassical P).exp_val T, (MState.ofClassical P).exp_val_prob hT⟩,
    ⟨(MState.ofClassical Q).exp_val T, (MState.ofClassical Q).exp_val_prob hT⟩,
    rfl, rfl, ?_, ?_⟩
  · change (MState.ofClassical P).exp_val T ≤ (s : ℝ)
    rw [ofClassical_exp_val_indicator]
    exact (show ∑ x, (if (P x : ℝ) ≤ Q x then (P x : ℝ) else 0) ≤
        hellingerOverlap P Q by
      rw [hellingerOverlap]
      refine Finset.sum_le_sum ?_
      intro x _
      by_cases hx : (P x : ℝ) ≤ Q x
      · simpa [hx] using Real.le_sqrt (P x).2.1 (mul_nonneg (P x).2.1 (Q x).2.1) |>.2
          (by simpa [pow_two] using mul_le_mul_of_nonneg_left hx (P x).2.1)
      · simpa [hx] using Real.sqrt_nonneg ((P x : ℝ) * (Q x : ℝ))).trans hoverlap_s
  · change (r : ℝ) ≤ (MState.ofClassical Q).exp_val T
    rw [ofClassical_exp_val_indicator]
    change (r : ℝ) ≤ ∑ x, (if (P x : ℝ) ≤ Q x then (Q x : ℝ) else 0)
    have hcompl : ∑ x, (if (P x : ℝ) ≤ Q x then 0 else (Q x : ℝ)) ≤
        hellingerOverlap P Q := by
      rw [hellingerOverlap]
      refine Finset.sum_le_sum ?_
      intro x _
      by_cases hx : (P x : ℝ) ≤ Q x
      · simpa [hx] using Real.sqrt_nonneg ((P x : ℝ) * (Q x : ℝ))
      · rw [mul_comm]
        simpa [hx] using Real.le_sqrt (Q x).2.1 (mul_nonneg (Q x).2.1 (P x).2.1) |>.2
          (by simpa [pow_two] using
            mul_le_mul_of_nonneg_left (le_of_not_ge hx) (Q x).2.1)
    have htotal' :
        (∑ x, (if (P x : ℝ) ≤ Q x then 0 else (Q x : ℝ))) +
          (∑ x, (if (P x : ℝ) ≤ Q x then (Q x : ℝ) else 0)) =
        1 := by
      rw [← Finset.sum_add_distrib]
      convert Q.normalized using 1
      exact Finset.sum_congr rfl fun x _ => by by_cases hx : (P x : ℝ) ≤ Q x <;> simp [hx]
    linarith

private theorem exists_dyadic_binary_effect_le_ge
    (p q s r : Prob) (hpq : (p : ℝ) < q)
    (hs_pos : 0 < (s : ℝ)) (hr_lt_one : (r : ℝ) < 1) :
    ∃ (n : ℕ) (T : HermitianMat (DyadicPow (ULift.{u} (Fin 2)) n) ℂ),
      (0 ≤ T ∧ T ≤ 1) ∧ ∃ α β : Prob,
        (dyadicStatePow (MState.ofClassical (uliftCoin p)) n).exp_val T = α ∧
        (dyadicStatePow (MState.ofClassical (uliftCoin q)) n).exp_val T = β ∧
        (α : ℝ) ≤ s ∧ (r : ℝ) ≤ β := by
  let ε : ℝ := (s : ℝ) ⊓ (1 - (r : ℝ))
  have ha1 : hellingerOverlap (uliftCoin p) (uliftCoin q) < 1 := by
    rw [hellingerOverlap_uliftCoin]
    simpa [hellingerOverlap_coin] using hellingerOverlap_coin_lt_one p q hpq
  obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one
    (show 0 < ε by simpa [ε] using lt_inf_iff.mpr ⟨hs_pos, sub_pos.mpr hr_lt_one⟩) ha1
  have hn : (hellingerOverlap (uliftCoin p) (uliftCoin q)) ^ (2 ^ n : ℕ) < ε := lt_of_le_of_lt
    (pow_le_pow_of_le_one (by rw [hellingerOverlap_uliftCoin]; positivity) ha1.le
      (Nat.lt_two_pow_self (n := n)).le) hn'
  have hoverlap_lt :
      hellingerOverlap (dyadicProbPow (uliftCoin p) n) (dyadicProbPow (uliftCoin q) n) < ε := by
    rw [hellingerOverlap_dyadicProbPow]
    exact hn
  obtain ⟨T, hT, α, β, hpT, hqT, hαs, hrβ⟩ :=
    exists_likelihood_indicator_effect
      (dyadicProbPow (uliftCoin p) n) (dyadicProbPow (uliftCoin q) n) s r
      (hoverlap_lt.le.trans inf_le_left) (hoverlap_lt.le.trans inf_le_right)
  exact ⟨n, T, hT, α, β, by simpa [dyadicStatePow_ofClassical] using hpT,
    by simpa [dyadicStatePow_ofClassical] using hqT, hαs, hrβ⟩

private def dyadicCPTPMapPow {e : Type u} [Fintype e] [DecidableEq e]
    (Λ : CPTPMap d e) : ∀ n, CPTPMap (DyadicPow d n) (DyadicPow e n)
  | 0 => Λ
  | n + 1 => dyadicCPTPMapPow Λ n ⊗ᶜᵖ dyadicCPTPMapPow Λ n

/-- Universe-lifted two-outcome POVM associated to an effect `0 ≤ T ≤ 1`. -/
private def binaryPOVMOfEffectULift (T : HermitianMat d ℂ) (hT : 0 ≤ T ∧ T ≤ 1) :
    POVM (ULift (Fin 2)) d where
  mats i := if i = ULift.up (0 : Fin 2) then T else 1 - T
  nonneg i := by
    split
    · exact hT.1
    · exact HermitianMat.zero_le_iff.mpr hT.2
  normalized := by
    have hsum :
        (∑ i : ULift (Fin 2), if i = ULift.up (0 : Fin 2) then T else 1 - T) =
          ∑ i : Fin 2, if ULift.up i = ULift.up (0 : Fin 2) then T else 1 - T := by
      refine Fintype.sum_equiv Equiv.ulift
        (fun i : ULift (Fin 2) => if i = ULift.up (0 : Fin 2) then T else 1 - T)
        (fun i : Fin 2 => if ULift.up i = ULift.up (0 : Fin 2) then T else 1 - T) ?_
      rintro ⟨x⟩
      rfl
    rw [hsum]
    simp [Fin.sum_univ_two]

/-- Measuring a lifted binary effect and discarding the post-measurement state gives a lifted coin. -/
private theorem binaryPOVMOfEffectULift_measureDiscard_apply
    (T : HermitianMat d ℂ) (hT : 0 ≤ T ∧ T ≤ 1) (ρ : MState d) :
    (binaryPOVMOfEffectULift T hT).measureDiscard ρ =
      MState.ofClassical (uliftCoin ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩) := by
  rw [POVM.measureDiscard_apply]
  congr 1
  let p : Prob := ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩
  ext i
  rcases i with ⟨i⟩
  fin_cases i
  · let z : ULift.{u} (Fin 2) := ULift.up (0 : Fin 2)
    change inner ℝ T ρ.M = ((uliftCoin p) z : ℝ)
    simp [z, p, uliftCoin, ProbDistribution.congr_apply, MState.exp_val, HermitianMat.inner_comm]
  · let o : ULift.{u} (Fin 2) := ULift.up (1 : Fin 2)
    change inner ℝ (1 - T) ρ.M = ((uliftCoin p) o : ℝ)
    simp [o, p, uliftCoin, ProbDistribution.congr_apply, Prob.coe_one_minus,
      MState.exp_val, HermitianMat.inner_comm, inner_sub_right, HermitianMat.inner_one, ρ.tr]

private theorem dyadicStatePow_relEntropy (ρ σ : MState d) :
    ∀ n, f (dyadicStatePow ρ n) (dyadicStatePow σ n).M = ((2 ^ n : ℕ) : ENNReal) * f ρ σ := by
  intro n
  induction n with
  | zero => simp [dyadicStatePow]; rfl
  | succ n ih =>
      show f (dyadicStatePow ρ n ⊗ᴹ dyadicStatePow ρ n)
            ↑(dyadicStatePow σ n ⊗ᴹ dyadicStatePow σ n) = _
      rw [RelEntropy.of_kron (f := f), ih]
      rw [← mul_add, ← two_mul, pow_succ, Nat.cast_mul]
      ring

private theorem exists_binary_measurement_of_ne (ρ σ : MState d) (hne : ρ ≠ σ) :
    ∃ p q : Prob, (p : ℝ) < (q : ℝ) ∧
      ∃ Λ : CPTPMap d (ULift.{u} (Fin 2)),
        Λ ρ = MState.ofClassical (uliftCoin p) ∧
        Λ σ = MState.ofClassical (uliftCoin q) := by
  obtain ⟨T, hT, hT_ne⟩ := exists_effect_exp_val_ne_of_ne ρ σ hne
  let p : Prob := ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩
  let q : Prob := ⟨σ.exp_val T, σ.exp_val_prob hT⟩
  by_cases hpq : (p : ℝ) < q
  · exact ⟨p, q, hpq, (binaryPOVMOfEffectULift T hT).measureDiscard,
      by rw [binaryPOVMOfEffectULift_measureDiscard_apply],
      by rw [binaryPOVMOfEffectULift_measureDiscard_apply]⟩
  · let T' : HermitianMat d ℂ := 1 - T
    have hT' : 0 ≤ T' ∧ T' ≤ 1 := by
      refine ⟨by dsimp [T']; exact HermitianMat.zero_le_iff.mpr hT.2, ?_⟩
      dsimp [T']
      rw [sub_le_iff_le_add]
      simpa using hT.1
    have hpq' : ((1 - p : Prob) : ℝ) < (1 - q : Prob) := by
      rw [Prob.coe_one_minus, Prob.coe_one_minus]
      linarith [lt_of_le_of_ne (le_of_not_gt hpq) (fun heq => hT_ne heq.symm)]
    refine ⟨1 - p, 1 - q, hpq', (binaryPOVMOfEffectULift T' hT').measureDiscard, ?_, ?_⟩ <;>
      rw [binaryPOVMOfEffectULift_measureDiscard_apply] <;>
      congr 2 <;>
      apply Subtype.ext <;>
      simp [T', p, q, MState.exp_val_sub, MState.exp_val_one, Prob.coe_one_minus]

private theorem exists_binary_postprocess {α β s r : Prob}
    (hαs : (α : ℝ) ≤ s) (hsr : (s : ℝ) < r) (hrβ : (r : ℝ) ≤ β) :
    ∃ a b : Prob, Prob.mix α a b = s ∧ Prob.mix β a b = r := by
  let A : ℝ := α
  let B : ℝ := β
  let S : ℝ := s
  let R : ℝ := r
  have hAB : A < B := by dsimp [A, B, S, R] at *; linarith
  let k : ℝ := (R - S) / (B - A)
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (sub_nonneg.mpr (by dsimp [S, R]; exact hsr.le))
      (sub_nonneg.mpr hAB.le)
  have hk_le_one : k ≤ 1 := by
    dsimp [k]
    rw [div_le_one (sub_pos.mpr hAB)]
    dsimp [A, B, S, R] at *
    linarith
  let bR : ℝ := S - A * k
  let aR : ℝ := bR + k
  have hbR_nonneg : 0 ≤ bR := by
    dsimp [bR, A, S] at *
    linarith [mul_le_mul_of_nonneg_left hk_le_one α.2.1]
  have hbR_le_one : bR ≤ 1 := by
    dsimp [bR, S]
    nlinarith [s.2.2, α.2.1, hk_nonneg]
  have haR_nonneg : 0 ≤ aR := by dsimp [aR]; positivity
  have haR_le_one : aR ≤ 1 := by
    have hden_pos : 0 < B - A := sub_pos.mpr hAB
    have hmain :
        S * (B - A) + (1 - A) * (R - S) ≤ 1 * (B - A) := by
      nlinarith [
        mul_le_mul_of_nonneg_right (show R ≤ B by dsimp [R, B] at hrβ ⊢; exact hrβ)
          (show 0 ≤ 1 - A by dsimp [A]; linarith [α.2.2]),
        mul_le_mul_of_nonpos_right (show A ≤ S by dsimp [A, S] at hαs ⊢; exact hαs)
          (show B - 1 ≤ 0 by dsimp [B]; linarith [β.2.2])]
    rw [show aR = (S * (B - A) + (1 - A) * (R - S)) / (B - A) by
      dsimp [aR, bR, k]
      field_simp [hden_pos.ne']
      ring, div_le_one hden_pos]
    simpa using hmain
  let a : Prob := ⟨aR, haR_nonneg, haR_le_one⟩
  let b : Prob := ⟨bR, hbR_nonneg, hbR_le_one⟩
  refine ⟨a, b, ?_, ?_⟩
  all_goals
    ext
    simp [Prob.mix, Mixable.mix, Mixable.mix_ab, Prob.coe_one_minus, a, b, aR, bR, k, A, B, S, R]
  ·
    ring
  ·
    field_simp [show (↑β : ℝ) - ↑α ≠ 0 by dsimp [A, B] at hAB; linarith]
    ring

section nontrivial
variable [RelEntropy.Nontrivial f]

/-- From Tomamichel nontriviality, extract a strictly positive binary classical pair with
full-support states. This is the finite binary witness used in the proof of `faithful`. -/
private theorem exists_positive_binary_pair :
    ∃ p q : Prob, 0 < (p : ℝ) ∧ (p : ℝ) < q ∧ (q : ℝ) < 1 ∧
      (MState.ofClassical (uliftCoin.{u} p)).M.support = ⊤ ∧
      (MState.ofClassical (uliftCoin.{u} q)).M.support = ⊤ ∧
      0 < f (MState.ofClassical (uliftCoin.{u} p))
        (MState.ofClassical (uliftCoin.{u} q)).M := by
  obtain ⟨s, t, hs0, -, ht0, -, hs_order, hsSupport, htSupport, hpos⟩ :
      ∃ s t : Prob,
        0 < (s : ℝ) ∧ (s : ℝ) < 1 / 2 ∧
        0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 ∧
        (s : ℝ) < ((1 - t : Prob) : ℝ) ∧
        (MState.ofClassical (uliftCoin s)).M.support = ⊤ ∧
        (MState.ofClassical (uliftCoin (1 - t))).M.support = ⊤ ∧
        0 < f (MState.ofClassical (uliftCoin s))
          (MState.ofClassical (uliftCoin (1 - t))).M := by
    obtain ⟨d, instFintype, instDecidableEq, γ, ω, hγ, hω, hpos⟩ :=
      RelEntropy.Nontrivial.nontrivial (f := f)
    letI : Fintype d := instFintype
    letI : DecidableEq d := instDecidableEq
    obtain ⟨s, t, hs0, hslt, ht0, htlt, hleft, hright⟩ :
        ∃ s t : Prob, 0 < (s : ℝ) ∧ (s : ℝ) < 1 / 2 ∧
          0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 ∧
          (t : ℝ) • γ.M ≤ (1 - (s : ℝ)) • ω.M ∧
          (s : ℝ) • ω.M ≤ (1 - (t : ℝ)) • γ.M := by
      obtain ⟨Nγω, hNγω_pos, hγω⟩ := exists_le_nat_smul_of_fullSupport γ ω hω
      obtain ⟨Nωγ, _, hωγ⟩ := exists_le_nat_smul_of_fullSupport ω γ hγ
      let K : ℕ := Nat.max Nγω Nωγ
      let a : ℝ := 1 / (K + 2 : ℝ)
      have hden_pos : (0 : ℝ) < K + 2 := by positivity
      have ha_pos : 0 < a := by dsimp [a]; positivity
      have ha_lt_half : a < 1 / 2 := by
        dsimp [a]
        rw [div_lt_iff₀ hden_pos]
        nlinarith [show (1 : ℝ) ≤ K by
          exact_mod_cast le_trans hNγω_pos (le_max_left Nγω Nωγ)]
      have hscale {N : ℕ} (hNK : N ≤ K) : a * (N + 1 : ℝ) ≤ 1 - a := by
        dsimp [a]
        rw [div_mul_eq_mul_div, one_sub_div hden_pos.ne',
          div_le_div_iff_of_pos_right hden_pos]
        nlinarith [show (N + 1 : ℝ) ≤ K + 1 by exact_mod_cast Nat.succ_le_succ hNK]
      let p : Prob := ⟨a, ha_pos.le, by linarith [ha_lt_half]⟩
      refine ⟨p, p, by simpa [p] using ha_pos, by simpa [p] using ha_lt_half,
        by simpa [p] using ha_pos, by simpa [p] using ha_lt_half, ?_, ?_⟩
      · simpa [p] using calc
          a • γ.M ≤ a • ((Nγω + 1 : ℝ) • ω.M) :=
            smul_le_smul_of_nonneg_left hγω ha_pos.le
          _ = (a * (Nγω + 1 : ℝ)) • ω.M := by rw [smul_smul]
          _ ≤ (1 - a) • ω.M := smul_le_smul_of_nonneg_right
            (hscale (le_max_left Nγω Nωγ)) ω.nonneg
      · simpa [p] using calc
          a • ω.M ≤ a • ((Nωγ + 1 : ℝ) • γ.M) :=
            smul_le_smul_of_nonneg_left hωγ ha_pos.le
          _ = (a * (Nωγ + 1 : ℝ)) • γ.M := by rw [smul_smul]
          _ ≤ (1 - a) • γ.M := smul_le_smul_of_nonneg_right
            (hscale (le_max_right Nγω Nωγ)) γ.nonneg
    have hden : 0 < 1 - (s : ℝ) - (t : ℝ) := by linarith
    let τ : ULift.{u} (Fin 2) → MState d := fun i =>
      if i = ULift.up (0 : Fin 2) then
        binaryPrepOne γ ω (s : ℝ) (t : ℝ) hden hleft
      else
        binaryPrepZero γ ω (s : ℝ) (t : ℝ) hden hright
    let Λ : CPTPMap (ULift.{u} (Fin 2)) d :=
      CPTPMap.CPTP_of_choi_PSD_Tr
        (M := cqPrepareChoi (d := d) τ)
        (cqPrepareChoi_psd (d := d) τ)
        (cqPrepareChoi_traceLeft (d := d) τ)
    have hdenC : (1 - ((s : ℝ) : ℂ) - ((t : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hden.ne'
    have hγprep : Λ (MState.ofClassical (uliftCoin s)) = γ := by
      apply MState.ext_m
      change MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ)
        (MState.ofClassical (uliftCoin s)).m = γ.m
      rw [cqPrepare_apply_uliftCoin, Prob.coe_one_minus]
      ext i j
      simp [τ, binaryPrepOne, binaryPrepZero, MState.m, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, -MState.mat_M]
      field_simp [hdenC]
      ring
    have hωprep : Λ (MState.ofClassical (uliftCoin (1 - t))) = ω := by
      apply MState.ext_m
      change MatrixMap.of_choi_matrix (cqPrepareChoi (d := d) τ)
        (MState.ofClassical (uliftCoin (1 - t))).m = ω.m
      rw [cqPrepare_apply_uliftCoin, Prob.coe_one_minus, Prob.coe_one_minus]
      ext i j
      simp [τ, binaryPrepOne, binaryPrepZero, MState.m, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, -MState.mat_M]
      field_simp [hdenC]
      ring
    refine ⟨s, t, hs0, hslt, ht0, htlt, by rw [Prob.coe_one_minus]; linarith,
      uliftCoin_support_top s hs0 (by linarith),
      uliftCoin_support_top (1 - t) (by rw [Prob.coe_one_minus]; linarith)
        (by rw [Prob.coe_one_minus]; linarith), ?_⟩
    exact lt_of_lt_of_le hpos <| by
      simpa [hγprep, hωprep] using DPI (f := f) (MState.ofClassical (uliftCoin s))
        (MState.ofClassical (uliftCoin (1 - t))) Λ
  exact ⟨s, 1 - t, hs0, hs_order, by rw [Prob.coe_one_minus]; linarith,
    hsSupport, htSupport, hpos⟩

/-- A nontrivial relative entropy is **faithful**: it can distinguish when two states are equal.

The proof (Tomamichel §5) goes by building a binary measurement that separates `ρ` from `σ`,
using DPI to reduce to a classical `Fin 2` distribution, then amplifying with `of_kron` until the
`Nontrivial` axiom forces a strictly positive value. The tensor-power separation step is formalized
via the finite classical likelihood test in `exists_dyadic_binary_effect_le_ge`. -/
theorem faithful (ρ σ : MState d) : f ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro hzero
    by_contra hne
    obtain ⟨p, q, hpq, Λ, hρ, hσ⟩ := exists_binary_measurement_of_ne ρ σ hne
    have hzero_binary : ∀ n,
        f (dyadicStatePow (MState.ofClassical (uliftCoin p)) n)
          (dyadicStatePow (MState.ofClassical (uliftCoin q)) n).M = 0 := by
      intro n
      induction n with
      | zero =>
          simpa [dyadicStatePow] using
            le_antisymm (by simpa [hρ, hσ, hzero] using RelEntropy.DPI (f := f) ρ σ Λ) bot_le
      | succ n ih =>
          simpa [dyadicStatePow, ih] using
            RelEntropy.of_kron (f := f)
              (dyadicStatePow (MState.ofClassical (uliftCoin p)) n)
              (dyadicStatePow (MState.ofClassical (uliftCoin q)) n)
              (dyadicStatePow (MState.ofClassical (uliftCoin p)) n)
              (dyadicStatePow (MState.ofClassical (uliftCoin q)) n)
    obtain ⟨s, r, hs_pos, hsr, hr_lt_one, _, _, hpos⟩ :=
      exists_positive_binary_pair (f := f)
    obtain ⟨n, T, hT, α, β, hpT, hqT, hαs, hrβ⟩ :=
      exists_dyadic_binary_effect_le_ge p q s r hpq hs_pos hr_lt_one
    suffices 0 < f (dyadicStatePow (MState.ofClassical (uliftCoin p)) n)
        (dyadicStatePow (MState.ofClassical (uliftCoin q)) n).M by
      simp [hzero_binary n] at this
    obtain ⟨a, b, hsmix, hrmix⟩ := exists_binary_postprocess hαs hsr hrβ
    let Μ : CPTPMap (DyadicPow (ULift.{u} (Fin 2)) n) (ULift (Fin 2)) :=
      (binaryPOVMOfEffectULift T hT).measureDiscard
    let Λ' : CPTPMap (DyadicPow (ULift.{u} (Fin 2)) n) (ULift (Fin 2)) :=
      (binaryClassicalPostprocess a b) ∘ₘ Μ
    have hOut (x z y : Prob)
        (hz : (dyadicStatePow (MState.ofClassical (uliftCoin x)) n).exp_val T = z)
        (hy : Prob.mix z a b = y) :
        Λ' (dyadicStatePow (MState.ofClassical (uliftCoin x)) n) =
          MState.ofClassical (uliftCoin y) := by
      have hΜ : Μ (dyadicStatePow (MState.ofClassical (uliftCoin x)) n) =
          MState.ofClassical (uliftCoin z) := by
        rw [binaryPOVMOfEffectULift_measureDiscard_apply]
        exact congrArg (fun x => MState.ofClassical (uliftCoin x)) (Subtype.ext hz)
      simpa [Λ', CPTPMap.compose_eq, hΜ, binaryClassicalPostprocess_apply] using
        congrArg (fun x => MState.ofClassical (uliftCoin x)) hy
    exact lt_of_lt_of_le hpos <| by
      simpa [hOut p α s hpT hsmix, hOut q β r hqT hrmix] using DPI (f := f)
        (dyadicStatePow (MState.ofClassical (uliftCoin p)) n)
        (dyadicStatePow (MState.ofClassical (uliftCoin q)) n) Λ'
  · rintro rfl
    simp

/-- In every system with at least two classical points, a nontrivial relative entropy has a
strictly positive value on some pair of full-support states. -/
theorem exists_fullSupport_positive_of_two_le_card
    (d : Type u) [Fintype d] [DecidableEq d] (hd : 2 ≤ Fintype.card d) :
    ∃ (ρ σ : MState d), ρ.M.support = ⊤ ∧ σ.M.support = ⊤ ∧ 0 < f ρ σ := by
  haveI : Nonempty d := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num) hd)
  let i : d := Classical.arbitrary d
  let p : Prob := ⟨1 / 2, by norm_num⟩
  let ρ : MState d := p [MState.ofClassical (.constant i) ↔ MState.uniform]
  refine ⟨ρ, MState.uniform, ?_, ?_, ?_⟩
  · haveI : ρ.M.NonSingular := HermitianMat.nonSingular_of_posDef <| by
      dsimp [ρ]
      exact MState.PosDef_mix_of_ne_one (hσ₂ := MState.uniform_posDef) p
        (by dsimp [p]; norm_num [Prob.ext_iff])
    exact HermitianMat.nonSingular_support_top
  · haveI : (MState.uniform : MState d).M.NonSingular :=
      HermitianMat.nonSingular_of_posDef MState.uniform_posDef
    exact HermitianMat.nonSingular_support_top
  · refine bot_lt_iff_ne_bot.mpr ((faithful (f := f) ρ MState.uniform).not.mpr ?_)
    intro hρσ
    have hmat := congrArg (fun τ : MState d => τ.M.mat) hρσ
    simp [ρ, p, Mixable.mix, Mixable.mix_ab, MState.instMixable,
      MState.uniform, MState.ofClassical, ProbDistribution.constant_eq,
      ProbDistribution.uniform_def, HermitianMat.diagonal, Mixable.to_U] at hmat
    have hdiag_re := congrArg Complex.re (congrFun (congrFun hmat i) i)
    simp [Matrix.add_apply] at hdiag_re
    norm_num at hdiag_re
    nlinarith [inv_lt_one_of_one_lt₀
      (by exact_mod_cast (lt_of_lt_of_le one_lt_two hd) : (1 : ℝ) < Fintype.card d)]

end nontrivial


/-- If `ρ ≤ exp x • σ`, then every axiomatized relative entropy is bounded by `x`. -/
theorem le_of_le_exp (ρ σ : MState d) {x : ℝ}
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
  have hgap : Real.log 3 < (((2 ^ n : ℕ) : ℝ)) * δ := by
    exact (div_lt_iff₀ hδ).mp <| lt_of_lt_of_le
      (show Real.log 3 / δ < (n : ℝ) by
        dsimp [n]
        exact lt_of_le_of_lt (Nat.le_ceil (Real.log 3 / δ))
          (by exact_mod_cast Nat.lt_succ_self (Nat.ceil (Real.log 3 / δ))))
      (by exact_mod_cast ((Nat.lt_two_pow_self : n < 2 ^ n).le) : (n : ℝ) ≤ (2 ^ n : ℕ))
  let y : ℝ := (((2 ^ n : ℕ) : ℝ)) * x
  have hy_nonneg : 0 ≤ y := by dsimp [y]; positivity
  have hpow_le : ∀ m, (dyadicStatePow ρ m).M ≤
      Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M := by
    intro m
    induction m with
    | zero =>
        simpa [dyadicStatePow] using h
    | succ m ih =>
        have hσ_nonneg :
            0 ≤ Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M :=
          smul_nonneg (by positivity) (dyadicStatePow σ m).nonneg
        have hpow :
            ((((2 ^ (m + 1) : ℕ) : ℝ)) * x) =
              ((((2 ^ m : ℕ) : ℝ)) * x) + ((((2 ^ m : ℕ) : ℝ)) * x) := by
          rw [pow_succ, Nat.cast_mul]
          ring
        have hunfold : (dyadicStatePow ρ (m + 1)).M
            = (dyadicStatePow ρ m).M ⊗ₖ (dyadicStatePow ρ m).M := rfl
        have hrhs : Real.exp (((((2 ^ m : ℕ) : ℝ)) * x) + ((((2 ^ m : ℕ) : ℝ)) * x)) •
              (dyadicStatePow σ (m + 1)).M
            = (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M) ⊗ₖ
              (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M) := by
          have hsk :
              (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M) ⊗ₖ
                  (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) • (dyadicStatePow σ m).M) =
                (Real.exp ((((2 ^ m : ℕ) : ℝ)) * x) * Real.exp ((((2 ^ m : ℕ) : ℝ)) * x)) •
                  ((dyadicStatePow σ m).M ⊗ₖ (dyadicStatePow σ m).M) := by
            ext1
            simp [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, mul_comm]
          simpa [dyadicStatePow, MState.prod, Real.exp_add] using hsk.symm
        rw [hunfold, hpow, hrhs]
        exact HermitianMat.kronecker_self_mono (dyadicStatePow ρ m).nonneg hσ_nonneg ih
  have hpow_bound' :
      (((2 ^ n : ℕ) : ENNReal) * f ρ σ.M) ≤
        ENNReal.ofReal (Real.log (Nat.ceil (Real.exp y) + 1)) := by
    simpa [dyadicStatePow_relEntropy (f := f) ρ σ n] using
      integer_bound_aux (f := f) (N := Nat.ceil (Real.exp y))
        (dyadicStatePow ρ n) (dyadicStatePow σ n) (by
          exact (hpow_le n).trans <| smul_le_smul_of_nonneg_right
            (by dsimp [y]; exact (Nat.le_ceil _).trans (by norm_num))
            (dyadicStatePow σ n).nonneg)
  have hpow_bound_real :
      (((2 ^ n : ℕ) : ℝ)) * (f ρ σ.M).toReal ≤
        Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) := by
    calc
      (((2 ^ n : ℕ) : ℝ)) * (f ρ σ.M).toReal
          = ((((2 ^ n : ℕ) : ENNReal) * f ρ σ.M)).toReal := by
              rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      _ ≤ (ENNReal.ofReal (Real.log (Nat.ceil (Real.exp y) + 1 : ℝ))).toReal :=
        (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hfin) ENNReal.ofReal_ne_top).2 hpow_bound'
      _ = Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) := by
              rw [ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num))]
  have hlog_upper : Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) ≤ y + Real.log 3 := by
    calc
      Real.log (Nat.ceil (Real.exp y) + 1 : ℝ) ≤ Real.log (3 * Real.exp y) :=
        Real.log_le_log (by positivity) (by
          nlinarith [(Nat.ceil_lt_add_one (Real.exp_nonneg y)).le,
            (show (1 : ℝ) ≤ Real.exp y by simpa [Real.one_le_exp_iff] using hy_nonneg)])
      _ = y + Real.log 3 := by
        rw [Real.log_mul (by positivity : (3 : ℝ) ≠ 0) (Real.exp_pos y).ne', Real.log_exp]
        ring
  have hlower :
      y + Real.log 3 < (((2 ^ n : ℕ) : ℝ)) * (f ρ σ.M).toReal := by
    dsimp [y, δ] at hgap
    nlinarith
  linarith

/-- The relative max-entropy is a lower bound on all relative entropies. -/
theorem le_max (ρ σ : MState d) : f ρ σ.M ≤ max ρ σ.M := by
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

end bounds

end RelEntropy

/-- The axioms for a well-behaved quantum entropy: it vanishes on pure states and is additive
under tensor products. Captures the common features of the von Neumann, min-, max-, and α-Renyi
entropies. -/
class Entropy (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → ℝ≥0) where
  /-- The entropy of a pure state is zero -/
  of_const {d : Type u} [Fintype d] [DecidableEq d] (ψ : Ket d) : f (.pure ψ) = 0
  /-- Entropy is additive under tensor products -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ : MState d₁) (σ : MState d₂), f (ρ ⊗ᴹ σ) = f ρ + f σ
  -- /-- Entropy is convex. TODO def? Or do we even need this? -/
  -- convex : True := by trivial
