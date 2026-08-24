/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.SuperSymmetry.SU5.ChargeSpectrum.AllowsTerm
/-!

# Charge spectrum which minimally allows terms

## i. Overview

We can say that a charge spectrum `x : ChargeSpectrum 𝓩` minimally allows a potential term
`T : PotentialTerm` if it allows the term `T` and no strict subset of `x` allows `T`.

That is to say, you need all of the charges in `x` to allow the term `T`.

We show that any charge spectrum which allows `T` has a subset which minimally allows `T`.

We show that every charge spectrum which minimally allows `T` is of the form
`allowsTermForm a b c T` for some `a b c : 𝓩`, and the reverse is true for
`T` not equal to `W1` or `W2`.

## ii. Key results

- `MinimallyAllowsTerm` : Predicate on charge spectra which is true if the charge spectrum
  minimally allows a potential term.
- `allowsTerm_iff_subset_minimallyAllowsTerm` : A charge spectrum which allows a term
  has a subset which minimally allows the term, and vice versa.
- `eq_allowsTermForm_of_minimallyAllowsTerm` : Any charge spectrum which minimally allows a term
  is of the form `allowsTermForm a b c T` for some `a b c : 𝓩`.

## iii. Table of contents

- A. Charge spectra which minimally allow potential terms
  - A.1. Decidability of `MinimallyAllowsTerm`
  - A.2. A charge spectrum which minimally allows a term allows the term
  - A.3. Spectrum with a subset which minimally allows a term, allows the term
  - A.4. Minimally allows term iff only member of powerset allowing term
  - A.5. Minimally allows term iff powerset allowing term has cardinal one
  - A.6. A charge spectrum which allows a term has a subset which minimally allows the term
  - A.7. A charge spectrum allows a term iff it has a subset which minimally allows the term
  - A.8. Cardinality of spectrum which minimally allows term is at most degree of term
- B. Relation between `MinimallyAllowsTerm` and `allowsTermForm`
  - B.1. A charge spectrum which minimally allows a term is of the form `allowsTermForm a b c T`
  - B.2. `allowsTermForm a b c T` minimally allows `T` if `T` is not `W1` or `W2`

## iv. References

There are no known references for this material.
-/

@[expose] public section

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [AddCommGroup 𝓩] [DecidableEq 𝓩]
open SuperSymmetry.SU5

/-!

## A. Charge spectra which minimally allow potential terms

We define the predicate `MinimallyAllowsTerm` on charge spectra
which is true if the charge spectrum allows a given potential term and no strict subset of
it allows the term.

We prove properties of charge spectra which minimally allow potential terms.

-/
/-- A charge spectrum `x : ChargeSpectrum 𝓩` is said to minimally allow
  the potential term `T` if it allows `T` and no strict subset of it allows `T`. -/
def MinimallyAllowsTerm (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Prop :=
  ∀ y ∈ x.powerset, y = x ↔ y.AllowsTerm T

/-!

### A.1. Decidability of `MinimallyAllowsTerm`

We show that `MinimallyAllowsTerm` is decidable.
-/

instance (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Decidable (x.MinimallyAllowsTerm T) :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ y.AllowsTerm T))

/-!

### A.2. A charge spectrum which minimally allows a term allows the term

Somewhat trivially a charge spectrum which minimally allows the term does indeed allow the term.

-/

variable {T : PotentialTerm} {x : ChargeSpectrum 𝓩}

lemma allowsTerm_of_minimallyAllowsTerm (h : x.MinimallyAllowsTerm T) : x.AllowsTerm T := by
  simp only [MinimallyAllowsTerm] at h
  simpa using h x (self_mem_powerset x)

/-!

### A.3. Spectrum with a subset which minimally allows a term, allows the term

If a charge spectrum `x` has a subset which minimally allows a term `T`, then `x` allows `T`.

-/

lemma allowsTerm_of_has_minimallyAllowsTerm_subset
    (hx : ∃ y ∈ powerset x, y.MinimallyAllowsTerm T) : x.AllowsTerm T := by
  obtain ⟨y, hy⟩ := hx
  simp only [mem_powerset_iff_subset] at hy
  apply allowsTerm_mono hy.1
  exact allowsTerm_of_minimallyAllowsTerm hy.2

/-!

### A.4. Minimally allows term iff only member of powerset allowing term

A charge spectrum `x` minimally allows a term `T` if and only if the only member of its
own powerset which allows `T` is itself.

-/

lemma minimallyAllowsTerm_iff_powerset_filter_eq :
    x.MinimallyAllowsTerm T ↔ x.powerset.filter (fun y => y.AllowsTerm T) = {x} := by
  constructor
  · intro h
    ext y
    simp only [Finset.mem_filter, mem_powerset_iff_subset, Finset.mem_singleton]
    simp [MinimallyAllowsTerm] at h
    constructor
    · exact fun ⟨h1, h2⟩ => (h y h1).mpr h2
    · intro h1
      subst h1
      simp
      exact (h y (by simp)).mp rfl
  · intro h
    simp [MinimallyAllowsTerm]
    intro y hy
    rw [Finset.eq_singleton_iff_unique_mem] at h
    simp at h
    constructor
    · intro h1
      subst h1
      exact h.1
    · intro h1
      apply h.2
      · exact hy
      · exact h1

/-!

### A.5. Minimally allows term iff powerset allowing term has cardinal one

A charge spectrum `x` minimally allows a term `T` if and only the
the number of members of its powerset which allow `T` is one.

-/

lemma minimallyAllowsTerm_iff_powerset_countP_eq_one :
    x.MinimallyAllowsTerm T ↔ x.powerset.val.countP (fun y => y.AllowsTerm T) = 1 := by
  rw [minimallyAllowsTerm_iff_powerset_filter_eq]
  constructor
  · intro h
    trans (Finset.filter (fun y => y.AllowsTerm T) x.powerset).card
    · change _ = (Multiset.filter (fun y => y.AllowsTerm T) x.powerset.val).card
      exact Multiset.countP_eq_card_filter (fun y => y.AllowsTerm T) x.powerset.val
    · rw [h]
      simp
  · intro h
    have h1 : (Multiset.filter (fun y => y.AllowsTerm T) x.powerset.val).card = 1 := by
      rw [← h]
      exact Eq.symm (Multiset.countP_eq_card_filter (fun y => y.AllowsTerm T) x.powerset.val)
    rw [Multiset.card_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have haMem : a ∈ Multiset.filter (fun y => y.AllowsTerm T) x.powerset.val := by
      simp [ha]
    simp at haMem
    have hxMem : x ∈ Multiset.filter (fun y => y.AllowsTerm T) x.powerset.val := by
      simpa using allowsTerm_mono haMem.1 haMem.2
    rw [ha] at hxMem
    simp at hxMem
    subst hxMem
    exact Finset.val_inj.mp ha

/-!

### A.6. A charge spectrum which allows a term has a subset which minimally allows the term

If a charge spectrum `x` allows a term `T`, then it has a subset which minimally allows `T`.

-/

lemma subset_minimallyAllowsTerm_of_allowsTerm
    (hx : x.AllowsTerm T) : ∃ y ∈ powerset x, y.MinimallyAllowsTerm T := by
  have hPresent : (x.powerset.filter (fun y => y.AllowsTerm T)) ≠ ∅ := by
    rw [← @Finset.nonempty_iff_ne_empty]
    use x
    simp [hx]
  obtain ⟨y, h1, h2⟩ := min_exists (x.powerset.filter (fun y => y.AllowsTerm T)) hPresent
  use y
  simp at h1
  simp_all
  rw [minimallyAllowsTerm_iff_powerset_filter_eq]
  rw [← h2]
  ext z
  simp only [Finset.mem_filter, mem_powerset_iff_subset, Finset.mem_inter, and_congr_right_iff,
    iff_and_self]
  intro hzy hzpres
  exact subset_trans hzy h1.1

/-!

### A.7. A charge spectrum allows a term iff it has a subset which minimally allows the term

We combine results above to show that a charge spectrum allows a term if and only if it has a subset
which minimally allows the term.

-/

lemma allowsTerm_iff_subset_minimallyAllowsTerm :
    x.AllowsTerm T ↔ ∃ y ∈ powerset x, y.MinimallyAllowsTerm T :=
  ⟨fun h => subset_minimallyAllowsTerm_of_allowsTerm h, fun h =>
    allowsTerm_of_has_minimallyAllowsTerm_subset h⟩

/-!

### A.8. Cardinality of spectrum which minimally allows term is at most degree of term

We show that the cardinality of a charge spectrum which minimally allows a term `T` is at most the
degree of `T`.

-/

lemma card_le_degree_of_minimallyAllowsTerm (h : x.MinimallyAllowsTerm T) :
    x.card ≤ T.degree := by
  obtain ⟨y, y_mem_power, y_card,y_present⟩ :=
    subset_card_le_degree_allowsTerm_of_allowsTerm (allowsTerm_of_minimallyAllowsTerm h)
  have hy : y ∈ x.powerset.filter (fun y => y.AllowsTerm T) := by
    simp_all
  rw [minimallyAllowsTerm_iff_powerset_filter_eq] at h
  rw [h] at hy
  simp at hy
  subst hy
  exact y_card

/-!

## B. Relation between `MinimallyAllowsTerm` and `allowsTermForm`

We now relate the predicate `MinimallyAllowsTerm` to charge spectra of the form
`allowsTermForm a b c T`.

-/

/-!

### B.1. A charge spectrum which minimally allows a term is of the form `allowsTermForm a b c T`

We show that any charge spectrum which minimally allows a term `T` is of the form
`allowsTermForm a b c T` for some `a b c : 𝓩`.

-/

lemma eq_allowsTermForm_of_minimallyAllowsTerm (h1 : x.MinimallyAllowsTerm T) :
    ∃ a b c, x = allowsTermForm a b c T := by
  obtain ⟨a, b, c, h2, h3⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm
    (allowsTerm_of_minimallyAllowsTerm h1)
  use a, b, c
  have hy : allowsTermForm a b c T ∈ x.powerset.filter (fun y => y.AllowsTerm T) := by
    simp_all
  rw [minimallyAllowsTerm_iff_powerset_filter_eq] at h1
  rw [h1] at hy
  simp at hy
  exact hy.symm

/-!

### B.2. `allowsTermForm a b c T` minimally allows `T` if `T` is not `W1` or `W2`

We show that charge spectra of the form `allowsTermForm a b c T` minimally allow `T` provided that
`T` is not one of `W1` or `W2`.

-/
open PotentialTerm in
lemma allowsTermForm_minimallyAllowsTerm {a b c : 𝓩} {T : PotentialTerm}
    (hT : T ≠ W1 ∧ T ≠ W2) :
    MinimallyAllowsTerm (allowsTermForm a b c T) T := by
  simp [MinimallyAllowsTerm]
  intro y hy
  constructor
  · intro h
    subst h
    exact allowsTermForm_allowsTerm
  · intro h
    obtain ⟨a', b', c', hsub, hAllowsTerm⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm h
    have hEq : allowsTermForm a' b' c' T = allowsTermForm a b c T :=
      allowsTermForm_eq_of_subset (subset_trans hsub hy) hT
    apply subset_antisymm hy
    rw [← hEq]
    exact hsub

end ChargeSpectrum

end SU5
end SuperSymmetry
