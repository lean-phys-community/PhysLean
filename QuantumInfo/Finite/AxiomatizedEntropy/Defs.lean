/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ClassicalInfo.Entropy
public import QuantumInfo.Finite.MState
public import QuantumInfo.Finite.CPTPMap

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

@[expose] public section

noncomputable section
universe u

open scoped NNReal
open scoped ENNReal

variable (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → HermitianMat d ℂ → ℝ≥0∞)

/-- The axioms to be a well-behaved quantum relative entropy, as given by
[Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf).

This simpler class allows for _trivial_ relative entropies, such as `-log tr(ρ⁰σ)`.
Use mixing `RelEntropy.Nontrivial` to only allow nontrivial relative entropies. -/
class RelEntropy : Prop where
  /-- The data processing inequality -/
  DPI {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ σ : MState d₁) (Λ : CPTPMap d₁ d₂) : f (Λ ρ) (Λ σ) ≤ f ρ σ
  /-- Entropy is additive under tensor products -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂), f (ρ₁ ⊗ ρ₂) (σ₁ ⊗ σ₂) = f ρ₁ σ₁ + f ρ₂ σ₂
  /-- Normalization of entropy to be `ln N` for a pure state vs. uniform on `N` many states. -/
  normalized {d : Type u} [fin : Fintype d] [DecidableEq d] [Nonempty d] (i : d) :
    f (.ofClassical (.constant i)) MState.uniform.M =
      some ⟨Real.log fin.card, Real.log_nonneg (mod_cast Fintype.card_pos)⟩

/-- The axioms to be a well-behaved quantum relative entropy, as given by
[Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf). -/
class RelEntropy.Nontrivial [RelEntropy f] where
  /-- Nontriviality condition for a relative entropy. -/
  nontrivial (d) [Fintype d] [DecidableEq d] : ∃ (ρ σ : MState d),
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

/-- Relabelling a state with `CPTPMap.of_equiv` leaves relative entropies unchanged. -/
@[simp]
theorem of_equiv_eq (e : d ≃ d₂) (ρ σ : MState d) :
    f (CPTPMap.of_equiv e ρ) (CPTPMap.of_equiv e σ) = f ρ σ := by
  apply le_antisymm
  · apply DPI
  · convert DPI (f := f) ((CPTPMap.of_equiv e) ρ) ((CPTPMap.of_equiv e) σ) (CPTPMap.of_equiv e.symm)
    · symm
      exact congrFun (CPTPMap.equiv_inverse e.symm) ρ
    · symm
      exact congrFun (CPTPMap.equiv_inverse e.symm) σ

/-- Relabelling a state with `MState.relabel` leaves relative entropies unchanged. -/
@[simp]
theorem relabel_eq (e : d₂ ≃ d) (ρ σ : MState d) :
    f (ρ.relabel e) (σ.relabel e) = f ρ σ := by
  apply of_equiv_eq

--Tomamichel's "4. Positivity" theorem is implicit true in our description because we
--only allow ENNReals. The only part to prove is that "D(ρ‖σ) = 0 if ρ = σ".

/-- The relative entropy is zero between any two states on a 1-D Hilbert space. -/
private lemma wrt_self_eq_zero' [Unique d] (ρ σ : MState d) : f ρ σ = 0 := by
  convert normalized (f := f) (d := d) default
  · apply Subsingleton.allEq
  · apply Subsingleton.allEq
  · simp

/-- The relative entropy `D(ρ‖ρ) = 0`. -/
@[simp]
theorem wrt_self_eq_zero (ρ : MState d) : f ρ ρ.M = 0 := by
  rw [← nonpos_iff_eq_zero, ← wrt_self_eq_zero' f (d := PUnit) default default]
  convert DPI (f := f) _ _ (CPTPMap.const_state ρ)
  · rw [CPTPMap.const_state_apply]
  · rw [CPTPMap.const_state_apply]

end possibly_trivial

section nontrivial
variable [Nontrivial f]

/-- A nontrivial relative entropy is **faithful**, it can distinguish when two states are equal. -/
theorem faithful (ρ σ : MState d) : f ρ σ = 0 ↔ ρ = σ := by
  sorry

end nontrivial

section bounds

open Prob in
/-- Quantum relative min-entropy. -/
def min (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  —log ⟨_, ρ.exp_val_prob ⟨proj_le_nonneg 0 σ, proj_le_le_one _ _⟩⟩

@[aesop (rule_sets := [finiteness]) simp]
theorem min_eq_top_iff (ρ : MState d) (σ : HermitianMat d ℂ) :
    (min ρ σ) = ⊤ ↔ ρ.M.support ≤ σ.ker := by
  open scoped HermitianMat in
  have h₂ : {0 ≤ₚ σ}.ker = σ.ker := by
    sorry --missing simp lemma
  simp [min, Prob.negLog_eq_top_iff, MState.exp_val_eq_zero_iff, Subtype.ext_iff, proj_le_nonneg, h₂]

open scoped HermitianMat in
protected theorem toReal_min (ρ : MState d) (σ : HermitianMat d ℂ) :
    (min ρ σ).toReal = -Real.log (ρ.exp_val {0 ≤ₚ σ}) :=
  Prob.negLog_pos_Real

/-- Min-relative entropy is a valid entropy function, albeit trivial (and not faithful). -/
instance : RelEntropy min where
  DPI := sorry
  of_kron := sorry
  normalized := sorry

theorem not_Nontrivial_min : ¬Nontrivial min := by
  rintro ⟨h⟩
  obtain ⟨ρ, σ, h₁, h₂, h₃⟩ := h (ULift (Fin 2))
  replace h₂ : proj_le 0 σ = (1 : HermitianMat (ULift (Fin 2)) ℂ) := by
    sorry--TODO
  simp [min, Subtype.ext_iff, MState.exp_val_eq_one_iff, proj_le_le_one, h₁, h₂] at h₃

/-- The relative min-entropy is a lower bound on all relative entropies. -/
theorem min_le (ρ σ : MState d) : min ρ σ ≤ f ρ σ := by
  sorry --Tomamichel, https://www.marcotom.info/files/entropy-masterclass2022.pdf, (1.28)

open Classical in
/-- Quantum relative max-entropy. -/
def max (ρ : MState d) (σ : HermitianMat d ℂ) : ENNReal :=
  if ∃ (x : ℝ), ρ.M ≤ Real.exp x • σ then
    some (sInf { x : NNReal | ρ.M ≤ Real.exp x • σ })
  else
    ⊤

@[aesop (rule_sets := [finiteness]) simp]
protected theorem max_not_top (ρ : MState d) (σ : HermitianMat d ℂ) :
    (max ρ σ) ≠ ⊤ ↔ σ.ker ≤ ρ.M.ker := by
  open ComplexOrder in
  constructor
  · intro h
    contrapose! h
    simp only [max, ENNReal.some_eq_coe, ite_eq_right_iff, ENNReal.coe_ne_top, imp_false,
      not_exists]
    intro x
    contrapose! h
    intro v hv
    rw [HermitianMat.ker, LinearMap.mem_ker] at hv ⊢
    replace hv : σ.toMat.mulVec v = 0 := sorry --why is this not defeq??
    replace h := h.right v
    rw [Matrix.sub_mulVec] at h
    simp [hv, Matrix.smul_mulVec_assoc] at h
    have := ρ.pos.right v
    -- have := le_antisymm (ρ.pos.right v) (by )
    sorry
  · intro
    rw [max, if_pos]
    · nofun
    sorry --log ("min nonzero eigenvalue of σ" / "max eigenvalue of ρ") should work

protected theorem toReal_max (ρ : MState d) (σ : HermitianMat d ℂ) :
    (max ρ σ).toReal = sInf { x : ℝ | ρ.M ≤ Real.exp x • σ } := by
  rw [max]
  split_ifs with h
  · have : { x : ℝ | ρ.M ≤ Real.exp x • σ }.Nonempty := by
      convert h
    simp
    sorry
  · push_neg at h
    simp [h]

/-- The relative max-entropy is a lower bound on all relative entropies. -/
theorem le_max (ρ σ : MState d) : f ρ σ ≤ max ρ σ := by
  sorry --Tomamichel, https://www.marcotom.info/files/entropy-masterclass2022.pdf, (1.28)

end bounds

end RelEntropy

class Entropy (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → ℝ≥0) where
  /-- The entropy of a pure state is zero -/
  of_const {d : Type u} [Fintype d] [DecidableEq d] (ψ : Ket d) : f (.pure ψ) = 0
  /-- Entropy is additive under tensor products -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ : MState d₁) (σ : MState d₂), f (ρ ⊗ σ) = f ρ + f σ
  -- /-- Entropy is convex. TODO def? Or do we even need this? -/
  -- convex : True := by trivial
