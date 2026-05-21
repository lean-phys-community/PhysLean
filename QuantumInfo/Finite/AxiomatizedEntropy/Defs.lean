/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Dennj Osele
-/
module

public import QuantumInfo.ClassicalInfo.Entropy
public import QuantumInfo.Finite.MState
public import QuantumInfo.Finite.CPTPMap.CPTP

@[expose] public section

/-! # Generalized quantum entropy and relative entropy

Here we define a broad notion of entropy axiomatically, `Entropy`, and the Prop
`Entropy f` means that the function `f : MState → ℝ` acts like a generalized kind of quantum
entropy. For instance, min-, max-, α-Renyi, and von Neumann entropies all fall
into this category.

Similarly, `RelEntropy f` means that `f : MState → HermitianMat → ENNReal` is a kind of
relative entropy. Every `RelEntropy` leads to a notion of entropy, as well, by
fixing one argument to the fully mixed state.

Of course relative entropies are "usually" used with a pair of normalized quantum states, but
it is still common in the literature to let the second argument be an arbitrary PSD Hermitian
matrix, so we allow this. The behavior when not a density matrix is left unspecified by the
axioms.

## References

* [Khinchin’s Fourth Axiom of Entropy Revisited](https://www.mdpi.com/2571-905X/6/3/49)
* [α-z Relative Entropies](https://warwick.ac.uk/fac/sci/maths/research/events/2013-2014/statmech/su/Nilanjana-slides.pdf)
* Watrous's notes, [Max-relative entropy and conditional min-entropy](https://cs.uwaterloo.ca/~watrous/QIT-notes/QIT-notes.02.pdf)
* [Quantum Relative Entropy - An Axiomatic Approach](https://www.marcotom.info/files/entropy-masterclass2022.pdf)
  by Marco Tomamichel
* [StackExchange](https://quantumcomputing.stackexchange.com/a/12953/10115)
-/

noncomputable section
universe u

open scoped NNReal
open scoped ENNReal

variable (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → HermitianMat d ℂ → ℝ≥0∞)

/-- The axioms to be a well-behaved quantum relative entropy, as given by
[Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf).

This simpler class allows for _trivial_ relative entropies, such as `-log tr(ρ⁰σ)`.
Use the mixin `RelEntropy.Nontrivial` to only allow nontrivial relative entropies. -/
class RelEntropy : Prop where
  /-- The data processing inequality. -/
  DPI {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ σ : MState d₁) (Λ : CPTPMap d₁ d₂) : f (Λ ρ) (Λ σ) ≤ f ρ σ
  /-- Entropy is additive under tensor products. -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂),
      f (ρ₁ ⊗ᴹ ρ₂) (σ₁ ⊗ᴹ σ₂) = f ρ₁ σ₁ + f ρ₂ σ₂
  /-- Normalization of entropy to be `ln N` for a pure state vs. uniform on `N` many states. -/
  normalized {d : Type u} [fin : Fintype d] [DecidableEq d] [Nonempty d] (i : d) :
    f (.ofClassical (.constant i)) MState.uniform.M =
      some ⟨Real.log fin.card, Real.log_nonneg (mod_cast Fintype.card_pos)⟩

/-- Mixin on top of `RelEntropy` that rules out trivial relative entropies, those that vanish
on every pair of full-support states. See
[Tomamichel](https://www.marcotom.info/files/entropy-masterclass2022.pdf). -/
class RelEntropy.Nontrivial [RelEntropy f] where
  /-- Nontriviality condition for a relative entropy: every finite system has some pair of
  full-support states with positive relative entropy. -/
  nontrivial (d : Type u) [Fintype d] [DecidableEq d] :
    ∃ ρ σ : MState d, ρ.M.support = ⊤ ∧ σ.M.support = ⊤ ∧ 0 < f ρ σ

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

Let `D` be a generalized divergence satisfying DPI and additivity. Then `D` is automatically
normalized to zero on the 1D space.

Proof sketch: By additivity, `D(unit‖unit) = D(unit⊗unit‖unit⊗unit) = D(unit‖unit) + D(unit‖unit)`,
so `D(unit‖unit) = 0` unless it is `⊤`. DPI from a two-point normalized pair rules out `⊤`.
The current axioms include the 1D normalization directly, so the proof below uses it.
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

end RelEntropy

/-- The axioms for a well-behaved quantum entropy: it vanishes on pure states and is additive
under tensor products. Captures the common features of the von Neumann, min-, max-, and α-Renyi
entropies. -/
class Entropy (f : ∀ {d : Type u} [Fintype d] [DecidableEq d], MState d → ℝ≥0) where
  /-- The entropy of a pure state is zero. -/
  of_const {d : Type u} [Fintype d] [DecidableEq d] (ψ : Ket d) : f (.pure ψ) = 0
  /-- Entropy is additive under tensor products. -/
  of_kron {d₁ d₂ : Type u} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂] :
    ∀ (ρ : MState d₁) (σ : MState d₂), f (ρ ⊗ᴹ σ) = f ρ + f σ
  -- /-- Entropy is convex. TODO def? Or do we even need this? -/
  -- convex : True := by trivial
