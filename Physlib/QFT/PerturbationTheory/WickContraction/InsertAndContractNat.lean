/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.WickContraction.Erase
/-!

# Inserting an element into a contraction

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open Physlib.List
open Physlib.Fin

/-!

## Inserting an element into a contraction

-/

/-- Given a Wick contraction `c` for `n`, a position `i : Fin n.succ` and
  an optional uncontracted element `j : Option (c.uncontracted)` of `c`.
  The Wick contraction for `n.succ` formed by 'inserting' `i` into `Fin n`
  and contracting it optionally with `j`. -/
def insertAndContractNat (c : WickContraction n) (i : Fin n.succ) (j : Option (c.uncontracted)) :
    WickContraction n.succ := by
  let f := Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1
  let f' := match j with | none => f | some j => Insert.insert {i, i.succAbove j} f
  refine ⟨f', ?_, ?_⟩
  · simp only [Nat.succ_eq_add_one, f']
    match j with
    | none =>
      simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, f]
      intro a ha
      rw [Finset.mapEmbedding_apply]
      simp only [Finset.card_map]
      exact c.2.1 a ha
    | some j =>
      simp only [Finset.mem_insert, forall_eq_or_imp]
      apply And.intro
      · rw [@Finset.card_eq_two]
        use i
        use (i.succAbove j)
        simp only [ne_eq, and_true]
        exact Fin.ne_succAbove i j
      · simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, f]
        intro a ha
        rw [Finset.mapEmbedding_apply]
        simp only [Finset.card_map]
        exact c.2.1 a ha
  · intro a ha b hb
    simp only [Nat.succ_eq_add_one, f'] at ha hb
    match j with
    | none =>
      simp_all only [f, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        Nat.succ_eq_add_one]
      obtain ⟨a', ha', ha''⟩ := ha
      obtain ⟨b', hb', hb''⟩ := hb
      subst ha''
      subst hb''
      simp only [EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.disjoint_map]
      exact c.2.2 a' ha' b' hb'
    | some j =>
      simp_all only [Finset.mem_insert, Nat.succ_eq_add_one]
      match ha, hb with
      | Or.inl ha, Or.inl hb =>
        rw [ha, hb]
        simp
      | Or.inl ha, Or.inr hb =>
        apply Or.inr
        subst ha
        simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
        simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding, f] at hb
        obtain ⟨a', hb', hb''⟩ := hb
        subst hb''
        rw [Finset.mapEmbedding_apply]
        apply And.intro
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          exact fun x _ => Fin.succAbove_ne i x
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          have hj := j.2
          rw [mem_uncontracted_iff_not_contracted] at hj
          intro a ha hja
          rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hja
          subst hja
          exact False.elim (hj a' hb' ha)
      | Or.inr ha, Or.inl hb =>
        apply Or.inr
        subst hb
        simp only [Finset.disjoint_insert_right, Nat.succ_eq_add_one,
          Finset.disjoint_singleton_right]
        simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding, f] at ha
        obtain ⟨a', ha', ha''⟩ := ha
        subst ha''
        rw [Finset.mapEmbedding_apply]
        apply And.intro
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          exact fun x _ => Fin.succAbove_ne i x
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          have hj := j.2
          rw [mem_uncontracted_iff_not_contracted] at hj
          intro a ha hja
          rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hja
          subst hja
          exact False.elim (hj a' ha' ha)
      | Or.inr ha, Or.inr hb =>
        simp_all only [f,
          or_true, Finset.mem_map, RelEmbedding.coe_toEmbedding]
        obtain ⟨a', ha', ha''⟩ := ha
        obtain ⟨b', hb', hb''⟩ := hb
        subst ha''
        subst hb''
        simp only [EmbeddingLike.apply_eq_iff_eq]
        rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.disjoint_map]
        exact c.2.2 a' ha' b' hb'

lemma insertAndContractNat_of_isSome (c : WickContraction n) (i : Fin n.succ)
    (j : Option c.uncontracted) (hj : j.isSome) :
    (insertAndContractNat c i j).1 = Insert.insert {i, i.succAbove (j.get hj)}
    (Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1) := by
  obtain ⟨j, rfl⟩ := Option.isSome_iff_exists.mp hj
  simp [insertAndContractNat]

@[simp]
lemma self_mem_uncontracted_of_insertAndContractNat_none (c : WickContraction n) (i : Fin n.succ) :
    i ∈ (insertAndContractNat c i none).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  simp only [Nat.succ_eq_add_one, insertAndContractNat, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at hp
  obtain ⟨a, ha, ha'⟩ := hp
  have hc := c.2.1 a ha
  rw [@Finset.card_eq_two] at hc
  obtain ⟨x, y, hxy, ha⟩ := hc
  subst ha
  subst ha'
  rw [Finset.mapEmbedding_apply]
  simp only [Nat.succ_eq_add_one, Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  apply And.intro
  · exact Fin.ne_succAbove i x
  · exact Fin.ne_succAbove i y

@[simp]
lemma self_not_mem_uncontracted_of_insertAndContractNat_some (c : WickContraction n)
    (i : Fin n.succ) (j : c.uncontracted) :
    i ∉ (insertAndContractNat c i (some j)).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  simp [insertAndContractNat]

lemma insertAndContractNat_succAbove_mem_uncontracted_iff (c : WickContraction n) (i : Fin n.succ)
    (j : Fin n) :
    (i.succAbove j) ∈ (insertAndContractNat c i none).uncontracted ↔ j ∈ c.uncontracted := by
  simp [mem_uncontracted_iff_not_contracted, insertAndContractNat, Finset.mapEmbedding_apply]

@[simp]
lemma mem_uncontracted_insertAndContractNat_none_iff (c : WickContraction n) (i : Fin n.succ)
    (k : Fin n.succ) : k ∈ (insertAndContractNat c i none).uncontracted ↔
    k = i ∨ ∃ j, k = i.succAbove j ∧ j ∈ c.uncontracted := by
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨z, rfl⟩
  · simp
  · simp [insertAndContractNat_succAbove_mem_uncontracted_iff, Fin.succAbove_ne]

lemma insertAndContractNat_none_uncontracted (c : WickContraction n) (i : Fin n.succ) :
    (insertAndContractNat c i none).uncontracted =
    Insert.insert i (c.uncontracted.map i.succAboveEmb) := by
  ext a
  simp [mem_uncontracted_insertAndContractNat_none_iff, and_comm, eq_comm]

@[simp]
lemma mem_uncontracted_insertAndContractNat_some_iff (c : WickContraction n) (i : Fin n.succ)
    (k : Fin n.succ) (j : c.uncontracted) :
    k ∈ (insertAndContractNat c i (some j)).uncontracted ↔
    ∃ z, k = i.succAbove z ∧ z ∈ c.uncontracted ∧ z ≠ j := by
  by_cases hki : k = i
  · subst hki
    simp only [Nat.succ_eq_add_one, self_not_mem_uncontracted_of_insertAndContractNat_some, ne_eq,
      false_iff, not_exists, not_and, Decidable.not_not]
    exact fun x hx => False.elim (Fin.ne_succAbove k x hx)
  · simp only [Nat.succ_eq_add_one, ← Fin.exists_succAbove_eq_iff] at hki
    obtain ⟨z, hk⟩ := hki
    subst hk
    by_cases hjz : j = z
    · subst hjz
      rw [mem_uncontracted_iff_not_contracted]
      simp only [Nat.succ_eq_add_one, insertAndContractNat, Finset.mem_insert,
        Finset.mem_map, RelEmbedding.coe_toEmbedding, forall_eq_or_imp, Finset.mem_singleton,
        or_true, not_true_eq_false, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        false_and, ne_eq, false_iff, not_exists, not_and, Decidable.not_not]
      intro x
      rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)]
      exact fun a _a => a.symm
    · apply Iff.intro
      · intro h
        use z
        simp only [Nat.succ_eq_add_one, ne_eq, true_and]
        refine And.intro ?_ (fun a => hjz a.symm)
        rw [mem_uncontracted_iff_not_contracted]
        intro p hp
        rw [mem_uncontracted_iff_not_contracted] at h
        simp only [Nat.succ_eq_add_one, insertAndContractNat,
          Finset.mem_insert, Finset.mem_map, RelEmbedding.coe_toEmbedding, forall_eq_or_imp,
          Finset.mem_singleton, not_or, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
        have hc := h.2 p hp
        rw [Finset.mapEmbedding_apply] at hc
        exact (Finset.mem_map' (i.succAboveEmb)).mpr.mt hc
      · intro h
        obtain ⟨z', hz'1, hz'⟩ := h
        rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hz'1
        subst hz'1
        rw [mem_uncontracted_iff_not_contracted]
        simp only [Nat.succ_eq_add_one, insertAndContractNat,
          Finset.mem_insert, Finset.mem_map, RelEmbedding.coe_toEmbedding, forall_eq_or_imp,
          Finset.mem_singleton, not_or, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        apply And.intro
        · rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)]
          exact And.intro (Fin.succAbove_ne i z) (fun a => hjz a.symm)
        · rw [mem_uncontracted_iff_not_contracted] at hz'
          exact fun a ha hc => hz'.1 a ha ((Finset.mem_map' (i.succAboveEmb)).mp hc)

lemma insertAndContractNat_some_uncontracted (c : WickContraction n) (i : Fin n.succ)
    (j : c.uncontracted) :
    (insertAndContractNat c i (some j)).uncontracted =
    (c.uncontracted.erase j).map i.succAboveEmb := by
  ext a
  simp only [Nat.succ_eq_add_one, mem_uncontracted_insertAndContractNat_some_iff, ne_eq,
    Finset.map_erase, Fin.succAboveEmb_apply, Finset.mem_erase, Finset.mem_map]
  grind [Fin.succAbove_right_inj]

/-!

## Insert and getDual?

-/

set_option backward.isDefEq.respectTransparency false in
lemma insertAndContractNat_none_getDual?_isNone (c : WickContraction n) (i : Fin n.succ) :
    ((insertAndContractNat c i none).getDual? i).isNone := by
  simp [Option.isNone_iff_eq_none, getDual?_eq_none_iff_mem_uncontracted]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma insertAndContractNat_none_getDual?_eq_none (c : WickContraction n) (i : Fin n.succ) :
    (insertAndContractNat c i none).getDual? i = none := by
  simp [getDual?_eq_none_iff_mem_uncontracted]

@[simp]
lemma insertAndContractNat_succAbove_getDual?_eq_none_iff (c : WickContraction n) (i : Fin n.succ)
    (j : Fin n) :
    (insertAndContractNat c i none).getDual? (i.succAbove j) = none ↔ c.getDual? j = none := by
  simpa [uncontracted] using insertAndContractNat_succAbove_mem_uncontracted_iff c i j

@[simp]
lemma insertAndContractNat_succAbove_getDual?_isSome_iff (c : WickContraction n) (i : Fin n.succ)
    (j : Fin n) :
    ((insertAndContractNat c i none).getDual? (i.succAbove j)).isSome ↔ (c.getDual? j).isSome := by
  simp [Option.isSome_iff_ne_none]

@[simp]
lemma insertAndContractNat_succAbove_getDual?_get (c : WickContraction n) (i : Fin n.succ)
    (j : Fin n) (h : ((insertAndContractNat c i none).getDual? (i.succAbove j)).isSome) :
    ((insertAndContractNat c i none).getDual? (i.succAbove j)).get h =
    i.succAbove ((c.getDual? j).get (by simpa using h)) := by
  refine Option.get_of_mem h ((getDual?_eq_some_iff_mem _ _ _).mpr ?_)
  simp only [Nat.succ_eq_add_one, insertAndContractNat, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  exact ⟨_, self_getDual?_get_mem c j (by simpa using h),
    by simp [Finset.mapEmbedding_apply]⟩

@[simp]
lemma insertAndContractNat_some_getDual?_eq (c : WickContraction n) (i : Fin n.succ)
    (j : c.uncontracted) :
    (insertAndContractNat c i (some j)).getDual? i = some (i.succAbove j) := by
  rw [getDual?_eq_some_iff_mem]
  simp [insertAndContractNat]

lemma insertAndContractNat_some_getDual?_ne_none (c : WickContraction n) (i : Fin n.succ)
    (j : c.uncontracted) (k : Fin n) (hkj : k ≠ j.1) :
    (insertAndContractNat c i (some j)).getDual? (i.succAbove k) = none ↔ c.getDual? k = none := by
  simp [getDual?_eq_none_iff_mem_uncontracted, hkj]

lemma insertAndContractNat_some_getDual?_ne_isSome (c : WickContraction n) (i : Fin n.succ)
    (j : c.uncontracted) (k : Fin n) (hkj : k ≠ j.1) :
    ((insertAndContractNat c i (some j)).getDual? (i.succAbove k)).isSome ↔
    (c.getDual? k).isSome := by
  simp [Option.isSome_iff_ne_none, insertAndContractNat_some_getDual?_ne_none c i j k hkj]

lemma insertAndContractNat_some_getDual?_ne_isSome_get (c : WickContraction n) (i : Fin n.succ)
    (j : c.uncontracted) (k : Fin n) (hkj : k ≠ j.1)
    (h : ((insertAndContractNat c i (some j)).getDual? (i.succAbove k)).isSome) :
    ((insertAndContractNat c i (some j)).getDual? (i.succAbove k)).get h =
    i.succAbove ((c.getDual? k).get
      (by simpa [hkj, insertAndContractNat_some_getDual?_ne_isSome] using h)) := by
  refine Option.get_of_mem h ((getDual?_eq_some_iff_mem _ _ _).mpr ?_)
  simp only [Nat.succ_eq_add_one, insertAndContractNat, Finset.mem_insert,
    Finset.mem_map, RelEmbedding.coe_toEmbedding]
  exact Or.inr ⟨_, self_getDual?_get_mem c k
    (by simpa [hkj, insertAndContractNat_some_getDual?_ne_isSome] using h),
    by simp [Finset.mapEmbedding_apply]⟩

@[simp]
lemma insertAndContractNat_some_getDual?_of_neq (c : WickContraction n) (i : Fin n.succ)
    (j : c.uncontracted) (k : Fin n) (hkj : k ≠ j.1) :
    (insertAndContractNat c i (some j)).getDual? (i.succAbove k) =
    Option.map i.succAbove (c.getDual? k) := by
  rcases hc : c.getDual? k with _ | d
  · simp [hc, insertAndContractNat_some_getDual?_ne_none c i j k hkj]
  · rw [Option.map_some, getDual?_eq_some_iff_mem]
    simp only [Nat.succ_eq_add_one, insertAndContractNat, Finset.mem_insert,
      Finset.mem_map, RelEmbedding.coe_toEmbedding]
    exact Or.inr ⟨{k, d}, (c.getDual?_eq_some_iff_mem k d).mp hc,
      by simp [Finset.mapEmbedding_apply]⟩

/-!

## Interaction with erase.

-/

@[simp]
lemma insertAndContractNat_erase (c : WickContraction n) (i : Fin n.succ)
    (j : Option c.uncontracted) : erase (insertAndContractNat c i j) i = c := by
  refine Subtype.ext (Finset.ext fun a => ?_)
  simp only [erase, Nat.succ_eq_add_one, insertAndContractNat, Finset.mem_filter, Finset.mem_univ,
    true_and]
  match j with
  | none =>
    simp [Finset.mapEmbedding_apply, Finset.map_inj]
  | some j =>
    have hn : Finset.map i.succAboveEmb a ≠ {i, i.succAbove j} := fun h => by
      have hi : i ∈ Finset.map i.succAboveEmb a := h ▸ Finset.mem_insert_self i _
      simp [Fin.succAbove_ne] at hi
    simp [Finset.mapEmbedding_apply, Finset.map_inj, hn]

set_option backward.isDefEq.respectTransparency false in
lemma insertAndContractNat_getDualErase (c : WickContraction n) (i : Fin n.succ)
    (j : Option c.uncontracted) : (insertAndContractNat c i j).getDualErase i =
    uncontractedCongr (c := c) (c' := (c.insertAndContractNat i j).erase i) (by simp) j := by
  match n with
  | 0 =>
    fin_cases j
    simp [getDualErase]
  | Nat.succ n =>
  match j with
  | none =>
    simp [getDualErase]
  | some j =>
    simp only [Nat.succ_eq_add_one, getDualErase, insertAndContractNat_some_getDual?_eq,
      Option.isSome_some, ↓reduceDIte, Option.get_some, predAboveI_succAbove,
      uncontractedCongr_some, Option.some.injEq]
    rfl

@[simp]
lemma erase_insert (c : WickContraction n.succ) (i : Fin n.succ) :
    insertAndContractNat (erase c i) i (getDualErase c i) = c := by
  match n with
  | 0 =>
    apply Subtype.ext
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, insertAndContractNat, getDualErase]
    ext a
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨a', ha', rfl⟩
      exact (Finset.mem_filter.mp ha').2
    · intro ha
      obtain ⟨a', ha', rfl⟩ := c.mem_not_eq_erase_of_isNone (a := a) i (by simp) ha
      exact ⟨a', ha', rfl⟩
  | Nat.succ n =>
  apply Subtype.ext
  by_cases hi : (c.getDual? i).isSome
  · rw [insertAndContractNat_of_isSome]
    simp only [Nat.succ_eq_add_one, getDualErase, hi, ↓reduceDIte, Option.get_some]
    rw [succsAbove_predAboveI]
    · ext a
      simp only [Finset.mem_insert, Finset.mem_map, RelEmbedding.coe_toEmbedding]
      constructor
      · rintro (rfl | ⟨a', ha', rfl⟩)
        · simp
        · exact (Finset.mem_filter.mp ha').2
      · intro ha
        by_cases hia : a = {i, (c.getDual? i).get hi}
        · exact Or.inl hia
        · obtain ⟨a', ha', rfl⟩ := c.mem_not_eq_erase_of_isSome (a := a) i hi ha hia
          exact Or.inr ⟨a', ha', rfl⟩
    · simp
    · exact (getDualErase_isSome_iff_getDual?_isSome c i).mpr hi
  · simp only [Nat.succ_eq_add_one, insertAndContractNat, getDualErase, hi, Bool.false_eq_true,
    ↓reduceDIte]
    ext a
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨a', ha', rfl⟩
      exact (Finset.mem_filter.mp ha').2
    · intro ha
      obtain ⟨a', ha', rfl⟩ := c.mem_not_eq_erase_of_isNone (a := a) i (by simpa using hi) ha
      exact ⟨a', ha', rfl⟩

/-- Lifts a contraction in `c` to a contraction in `(c.insert i j)`. -/
def insertLift {c : WickContraction n} (i : Fin n.succ) (j : Option (c.uncontracted))
    (a : c.1) : (c.insertAndContractNat i j).1 := ⟨a.1.map (Fin.succAboveEmb i), by
  simp only [Nat.succ_eq_add_one, insertAndContractNat]
  match j with
  | none =>
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    use a
    simp only [a.2, true_and]
    rfl
  | some j =>
    simp only [Finset.mem_insert, Finset.mem_map, RelEmbedding.coe_toEmbedding]
    apply Or.inr
    use a
    simp only [a.2, true_and]
    rfl⟩

lemma insertLift_injective {c : WickContraction n} (i : Fin n.succ) (j : Option (c.uncontracted)) :
    Function.Injective (insertLift i j) := fun _ _ hab =>
  Subtype.ext (Finset.map_injective _ (Subtype.ext_iff.mp hab))

lemma insertLift_none_surjective {c : WickContraction n} (i : Fin n.succ) :
    Function.Surjective (c.insertLift i none) := by
  intro a
  obtain ⟨a', ha', ha''⟩ := Finset.mem_map.mp a.2
  exact ⟨⟨a', ha'⟩, Subtype.ext ha''⟩

lemma insertLift_none_bijective {c : WickContraction n} (i : Fin n.succ) :
    Function.Bijective (c.insertLift i none) :=
  ⟨insertLift_injective i none, insertLift_none_surjective i⟩

@[simp]
lemma insertAndContractNat_fstFieldOfContract (c : WickContraction n) (i : Fin n.succ)
    (j : Option (c.uncontracted)) (a : c.1) :
    (c.insertAndContractNat i j).fstFieldOfContract (insertLift i j a) =
      i.succAbove (c.fstFieldOfContract a) :=
  (c.insertAndContractNat i j).eq_fstFieldOfContract_of_mem (insertLift i j a)
    (i.succAbove (c.fstFieldOfContract a)) (i.succAbove (c.sndFieldOfContract a))
    (Finset.mem_map_of_mem _ (fstFieldOfContract_mem c a))
    (Finset.mem_map_of_mem _ (sndFieldOfContract_mem c a))
    (Fin.succAbove_lt_succAbove_iff.mpr (fstFieldOfContract_lt_sndFieldOfContract c a))

@[simp]
lemma insertAndContractNat_sndFieldOfContract (c : WickContraction n) (i : Fin n.succ)
    (j : Option (c.uncontracted)) (a : c.1) :
    (c.insertAndContractNat i j).sndFieldOfContract (insertLift i j a) =
    i.succAbove (c.sndFieldOfContract a) :=
  (c.insertAndContractNat i j).eq_sndFieldOfContract_of_mem (insertLift i j a)
    (i.succAbove (c.fstFieldOfContract a)) (i.succAbove (c.sndFieldOfContract a))
    (Finset.mem_map_of_mem _ (fstFieldOfContract_mem c a))
    (Finset.mem_map_of_mem _ (sndFieldOfContract_mem c a))
    (Fin.succAbove_lt_succAbove_iff.mpr (fstFieldOfContract_lt_sndFieldOfContract c a))

/-- Given a contracted pair for a Wick contraction `WickContraction n`, the
  corresponding contracted pair of a wick contraction `(c.insert i (some j))` formed
  by inserting an element `i` into the contraction. -/
def insertLiftSome {c : WickContraction n} (i : Fin n.succ) (j : c.uncontracted)
    (a : Unit ⊕ c.1) : (c.insertAndContractNat i (some j)).1 :=
  match a with
  | Sum.inl () => ⟨{i, i.succAbove j}, by
    simp [insertAndContractNat]⟩
  | Sum.inr a => c.insertLift i j a

lemma insertLiftSome_injective {c : WickContraction n} (i : Fin n.succ) (j : c.uncontracted) :
    Function.Injective (insertLiftSome i j) := by
  intro a b hab
  match a, b with
  | Sum.inl (), Sum.inl () => rfl
  | Sum.inl (), Sum.inr a | Sum.inr a, Sum.inl () =>
    simp only [Nat.succ_eq_add_one, insertLiftSome, insertLift, Subtype.mk.injEq] at hab
    have hi : i ∈ Finset.map (Fin.succAboveEmb i) a.1 := hab ▸ Finset.mem_insert_self i _
    simp [Fin.succAbove_ne] at hi
  | Sum.inr a, Sum.inr b =>
    exact congrArg Sum.inr (insertLift_injective i (some j) hab)

lemma insertLiftSome_surjective {c : WickContraction n} (i : Fin n.succ) (j : c.uncontracted) :
    Function.Surjective (insertLiftSome i j) := by
  intro a
  rcases Finset.mem_insert.mp a.2 with ha | ha
  · exact ⟨Sum.inl (), Subtype.ext ha.symm⟩
  · obtain ⟨a', ha', ha''⟩ := Finset.mem_map.mp ha
    exact ⟨Sum.inr ⟨a', ha'⟩, Subtype.ext ha''⟩

lemma insertLiftSome_bijective {c : WickContraction n} (i : Fin n.succ) (j : c.uncontracted) :
    Function.Bijective (insertLiftSome i j) :=
  ⟨insertLiftSome_injective i j, insertLiftSome_surjective i j⟩

/-!

# insertAndContractNat c i none and injection

-/

set_option backward.isDefEq.respectTransparency false in
lemma insertAndContractNat_injective (i : Fin n.succ) :
    Function.Injective (fun c => insertAndContractNat c i none) := fun _ _ hc =>
  Subtype.ext (by simpa [insertAndContractNat] using Subtype.ext_iff.mp hc)

lemma insertAndContractNat_surjective_on_nodual (i : Fin n.succ)
    (c : WickContraction n.succ) (hc : c.getDual? i = none) :
    ∃ c', insertAndContractNat c' i none = c := by
  have h0 : c.getDualErase i = none := Option.not_isSome_iff_eq_none.mp (by simp [hc])
  exact ⟨c.erase i, h0 ▸ erase_insert c i⟩

lemma insertAndContractNat_bijective (i : Fin n.succ) :
    Function.Bijective (fun c => (⟨insertAndContractNat c i none, by simp⟩ :
      {c : WickContraction n.succ // c.getDual? i = none})) := by
  refine ⟨fun a b hab => insertAndContractNat_injective i (by simpa using hab), fun c => ?_⟩
  exact (insertAndContractNat_surjective_on_nodual i c c.2).imp fun _ => Subtype.ext

end WickContraction
