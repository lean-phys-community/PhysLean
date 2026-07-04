/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.WickContraction.Basic
/-!

# Involution associated with a contraction

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}
namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open Physlib.List
open FieldStatistic

/-- The involution of `Fin n` associated with a Wick contraction `c : WickContraction n` as follows.
  If `i : Fin n` is contracted in `c` then it is taken to its dual, otherwise
  it is taken to itself. -/
def toInvolution : {f : Fin n → Fin n // Function.Involutive f} :=
  ⟨fun i => if h : (c.getDual? i).isSome then (c.getDual? i).get h else i, by
    intro i
    by_cases h : (c.getDual? i).isSome
    · simp [h]
    · simp [h]⟩

/-- The Wick contraction formed by an involution `f` of `Fin n` by taking as the contracted
  sets of the contraction the orbits of `f` of cardinality `2`. -/
def fromInvolution (f : {f : Fin n → Fin n // Function.Involutive f}) : WickContraction n :=
  ⟨Finset.univ.filter (fun a => a.card = 2 ∧ ∃ i, {i, f.1 i} = a), by
  intro a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp, forall_exists_index]
  intro h1 _ _
  exact h1, by
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨i, hai⟩ := ha.2
  subst hai
  obtain ⟨j, hbj⟩ := hb.2
  subst hbj
  by_cases h : i = j
  · subst h
    simp
  · by_cases hi : i = f.1 j
    · subst hi
      simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton, not_or,
        Finset.disjoint_singleton_right, true_or, not_true_eq_false, and_false, or_false]
      rw [f.2]
      rw [@Finset.pair_comm]
    · apply Or.inr
      simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton, not_or,
        Finset.disjoint_singleton_right]
      apply And.intro
      · apply And.intro
        · exact fun a => h a.symm
        · by_contra hn
          subst hn
          rw [f.2 i] at hi
          simp at hi
      · apply And.intro
        · exact fun a => hi a.symm
        · rw [Function.Injective.eq_iff]
          exact fun a => h (id (Eq.symm a))
          exact Function.Involutive.injective f.2⟩

@[simp]
lemma fromInvolution_getDual?_isSome (f : {f : Fin n → Fin n // Function.Involutive f})
    (i : Fin n) : ((fromInvolution f).getDual? i).isSome ↔ f.1 i ≠ i := by
  rw [getDual?_isSome_iff]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha⟩ := h
    have ha2 := a.2
    simp only [fromInvolution, Finset.mem_filter, Finset.mem_univ, true_and] at ha2
    obtain ⟨j, h⟩ := ha2.2
    rw [← h] at ha
    have hj : f.1 j ≠ j := by
      intro hn
      rw [hn] at h
      simp [← h] at ha2
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hj
    · rw [f.2]
      exact hj.symm
  · intro hi
    use ⟨{i, f.1 i}, by
      simp only [fromInvolution, Finset.mem_filter, Finset.mem_univ, exists_apply_eq_apply,
        and_true, true_and]
      exact Finset.card_pair hi.symm⟩
    simp

lemma fromInvolution_getDual?_eq_some (f : {f : Fin n → Fin n // Function.Involutive f}) (i : Fin n)
    (h : ((fromInvolution f).getDual? i).isSome) :
    ((fromInvolution f).getDual? i) = some (f.1 i) := by
  rw [getDual?_eq_some_iff_mem]
  simp only [fromInvolution, Finset.mem_filter, Finset.mem_univ, exists_apply_eq_apply, and_true,
    true_and]
  exact Finset.card_pair (Ne.symm ((fromInvolution_getDual?_isSome f i).mp h))

@[simp]
lemma fromInvolution_getDual?_get (f : {f : Fin n → Fin n // Function.Involutive f}) (i : Fin n)
    (h : ((fromInvolution f).getDual? i).isSome) :
    ((fromInvolution f).getDual? i).get h = (f.1 i) :=
  Option.get_of_mem h (fromInvolution_getDual?_eq_some f i h)

lemma toInvolution_fromInvolution : fromInvolution c.toInvolution = c := by
  apply Subtype.ext
  simp only [fromInvolution, toInvolution]
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply Iff.intro
  · intro h
    obtain ⟨i, hi⟩ := h.2
    split at hi
    · subst hi
      simp
    · subst hi
      simp [Finset.insert_eq_of_mem] at h
  · intro ha
    refine ⟨c.2.1 a ha, c.fstFieldOfContract ⟨a, ha⟩, ?_⟩
    simp only [fstFieldOfContract_getDual?, Option.isSome_some, ↓reduceDIte, Option.get_some]
    exact (finset_eq_fstFieldOfContract_sndFieldOfContract c ⟨a, ha⟩).symm

lemma fromInvolution_toInvolution (f : {f : Fin n → Fin n // Function.Involutive f}) :
    (fromInvolution f).toInvolution = f := by
  apply Subtype.ext
  funext i
  simp only [toInvolution]
  split
  · simp
  · rename_i h
    simp only [fromInvolution_getDual?_isSome, ne_eq, Decidable.not_not] at h
    exact h.symm

/-- The equivalence between Wick contractions for `n` and involutions of `Fin n`.
  The involution of `Fin n` associated with a Wick contraction `c : WickContraction n` as follows.
  If `i : Fin n` is contracted in `c` then it is taken to its dual, otherwise
  it is taken to itself. -/
def equivInvolution : WickContraction n ≃ {f : Fin n → Fin n // Function.Involutive f} where
  toFun := toInvolution
  invFun := fromInvolution
  left_inv := toInvolution_fromInvolution
  right_inv := fromInvolution_toInvolution

end WickContraction
