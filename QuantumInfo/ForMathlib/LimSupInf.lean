/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Int.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Util.CompileInductive
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Instances.Nat

@[expose] public section

open scoped NNReal
open scoped ENNReal
open Topology

/-!
Several 'bespoke' facts about limsup and liminf on ENNReal / NNReal needed in SteinsLemma
-/

/-
There exists a strictly increasing sequence of indices $n_k$ such that $f(1/(k+1), n_k) \le y + 1/(k+1)$.
-/
lemma exists_strictMono_seq_le (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞) (hf : ∀ x > 0, Filter.atTop.liminf (f x) ≤ y) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k : ℕ, f ((k : ℝ≥0) + 1)⁻¹ (n k) ≤ (y : ℝ≥0∞) + ((k : ℝ≥0) + 1)⁻¹ := by
  -- Since the liminf is ≤ y, for any ε > 0 and index n, there frequently exists an m > n satisfying the bound.
  have h_freq (k n : ℕ) : ∃ m > n, f ((k + 1 : ℝ≥0)⁻¹) m ≤ y + (k + 1 : ℝ≥0)⁻¹ := by
    specialize hf ((k + 1 : ℝ≥0)⁻¹) (by positivity)
    rw [Filter.liminf_eq] at hf
    simp only [Filter.eventually_atTop, sSup_le_iff, Set.mem_setOf_eq, forall_exists_index] at hf
    contrapose! hf
    refine ⟨_, n + 1, fun m hm ↦ (hf m hm).le, ENNReal.lt_add_right (by norm_num) (by norm_num)⟩
  refine ⟨fun k ↦ k.recOn (Classical.choose (h_freq 0 0))
    (fun i ih ↦ Nat.find (h_freq (i + 1) ih)), ?_, ?_⟩
  · exact strictMono_nat_of_lt_succ fun k ↦ (Nat.find_spec (h_freq (k + 1) _)).1
  · rintro (_ | k)
    · exact (Classical.choose_spec (h_freq 0 _)).2
    · exact (Nat.find_spec (h_freq (k + 1) _)).2
/-
There exists a strictly increasing sequence M such that for all k, and all n ≥ M k, f (1/(k+1)) n is close to y.
-/
lemma exists_seq_bound (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞) (hf : ∀ x > 0, Filter.atTop.limsup (f x) ≤ y) :
    ∃ M : ℕ → ℕ, StrictMono M ∧ ∀ k, ∀ n ≥ M k, f ((k + 1 : ℝ≥0)⁻¹) n ≤ y + (k + 1 : ℝ≥0∞)⁻¹ := by
  have h_M (k : ℕ) : ∃ M_k, ∀ n ≥ M_k, f (k + 1)⁻¹ n ≤ y + (k + 1 : ℝ≥0∞)⁻¹ :=
    Filter.eventually_atTop.mp <| (Filter.eventually_lt_of_limsup_lt <|
      (hf (k + 1)⁻¹ (by positivity)).trans_lt <|
      ENNReal.lt_add_right (by norm_num) (by norm_num)).mono fun n hn ↦ hn.le
  choose M hM using h_M
  refine ⟨Nat.rec (M 0) fun k ih ↦ M (k + 1) ⊔ (ih + 1),
    strictMono_nat_of_lt_succ fun _ ↦ lt_sup_of_lt_right (lt_add_one _),
    fun k n hn ↦ hM k n (le_trans ?_ hn)⟩
  cases k
  · exact le_rfl
  · exact le_max_left _ _

/- (∀ x, x > 0 → liminf (n ↦ f x n) ≤ y) →
  ∃ g : ℕ → ℝ, (∀ x, g x > 0) ∧ (liminf g = 0) ∧ (liminf (n ↦ f (g n) n) ≤ y) -/
lemma exists_liminf_zero_of_forall_liminf_le (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  (hf : ∀ x > 0, Filter.atTop.liminf (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ Filter.atTop.Tendsto g (𝓝 0) ∧
      Filter.atTop.liminf (fun n ↦ f (g n) n) ≤ y := by
  classical
  obtain ⟨n, hn_mono, hn_le⟩ := exists_strictMono_seq_le y f hf
  -- Define $g(m) = 1/(k(m)+1)$ where $k(m)$ is the index such that $n_{k(m)} \leq m < n_{k(m)+1}$.
  set g : ℕ → ℝ≥0 := fun m => (Nat.findGreatest (fun k => m ≥ n k) m + 1 : ℝ≥0)⁻¹ with hg_def
  have hg_le (k : ℕ) : f (g (n k)) (n k) ≤ (y : ℝ≥0∞) + ((k : ℝ≥0) + 1)⁻¹ := by
    have hfind : Nat.findGreatest (fun j => n k ≥ n j) (n k) = k :=
      Nat.findGreatest_eq_iff.mpr
        ⟨hn_mono.id_le k, fun _ => le_rfl, fun j hj _ => (hn_mono hj).not_ge⟩
    simpa only [hg_def, hfind] using hn_le k
  refine ⟨g, fun m => by positivity, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun m => Nat.findGreatest (fun k => m ≥ n k) m)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr fun x =>
        ⟨n x, fun a ha => Nat.le_findGreatest ((hn_mono.id_le x).trans ha) ha⟩
    have h2 : Filter.Tendsto (fun k : ℕ => ((k : ℝ≥0) + 1)⁻¹) Filter.atTop (𝓝 0) := by
      rw [← ENNReal.tendsto_coe]
      simpa [Function.comp_def] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
    exact h2.comp h1
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k₀, hk₀⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine Filter.liminf_le_of_frequently_le' (Filter.frequently_atTop.mpr fun a => ?_)
    refine ⟨n (a ⊔ k₀), le_sup_left.trans (hn_mono.id_le _), (hg_le _).trans ?_⟩
    gcongr
    refine le_trans ?_ hk₀.le
    rw [ENNReal.coe_inv (by positivity)]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ_of_le le_sup_right)

/- Version of `exists_liminf_zero_of_forall_liminf_le` that lets you also require `g`
to have an upper bound. -/
lemma exists_liminf_zero_of_forall_liminf_le_with_UB (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  {z : ℝ≥0} (hz : 0 < z)
  (hf : ∀ x, x > 0 → Filter.atTop.liminf (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (∀ x, g x < z) ∧ (Filter.atTop.Tendsto g (𝓝 0)) ∧
      (Filter.atTop.liminf (fun n ↦ f (g n) n) ≤ y) := by
  obtain ⟨g, hg₀, hg₁, hg₂⟩ := exists_liminf_zero_of_forall_liminf_le y (fun x n => f x n) hf;
  refine ⟨fun n => min (g n) (z / 2), by bound, by bound, ?_, ?_⟩
  · simpa using hg₁.min tendsto_const_nhds
  · beta_reduce
    rwa [Filter.liminf_congr ((hg₁.eventually (gt_mem_nhds <| half_pos hz)).mono
      fun n h => by rw [min_eq_left h.le])]

/- (∀ x, x > 0 → liminf (n ↦ f x n) ≤ y) →
  ∃ g : ℕ → ℝ, (∀ x, g x > 0) ∧ (liminf g = 0) ∧ (liminf (n ↦ f (g n) n) ≤ y) -/
lemma exists_limsup_zero_of_forall_limsup_le (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  (hf : ∀ x, x > 0 → Filter.atTop.limsup (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (Filter.atTop.Tendsto g (𝓝 0)) ∧
      (Filter.atTop.limsup (fun n ↦ f (g n) n) ≤ y) := by
  obtain ⟨M, hM₁, hM₂⟩ := exists_seq_bound y f hf
  refine ⟨fun n => 1 / (Nat.findGreatest (fun k => M k ≤ n) n + 1),
    fun n => by positivity, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => Nat.findGreatest (fun k => M k ≤ n) n)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr fun k =>
        ⟨M k, fun a ha => Nat.le_findGreatest ((hM₁.id_le k).trans ha) ha⟩
    have h2 : Filter.Tendsto (fun k : ℕ => ((k : ℝ≥0) + 1)⁻¹) Filter.atTop (𝓝 0) := by
      rw [← ENNReal.tendsto_coe]
      simpa [Function.comp_def] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [one_div, Function.comp_def] using h2.comp h1
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨K, hK⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [Filter.eventually_ge_atTop (M K)] with n hn
    have hKf : K ≤ Nat.findGreatest (fun k => M k ≤ n) n :=
      Nat.le_findGreatest ((hM₁.id_le K).trans hn) hn
    rw [one_div]
    refine (hM₂ _ n (Nat.findGreatest_spec (P := fun k => M k ≤ n)
      ((hM₁.id_le K).trans hn) hn)).trans ?_
    gcongr
    refine le_trans ?_ hK.le
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ_of_le hKf)

/-
If x_k tends to L and g(n) = x_k for n in [T_k, T_{k+1}) where T is strictly increasing, then g(n) tends to L.
-/
lemma tendsto_of_block_sequence {α : Type*} [TopologicalSpace α] {x : ℕ → α} {T : ℕ → ℕ}
    (hT : StrictMono T) {L : α} (hx : Filter.atTop.Tendsto x (𝓝 L)) (g : ℕ → α) (hg : ∀ k, ∀ n ∈ Set.Ico (T k) (T (k + 1)), g n = x k) :
      Filter.atTop.Tendsto g (𝓝 L) := by
  rw [Filter.tendsto_atTop'] at hx ⊢
  intro s hs
  rcases hx s hs with ⟨a, ha⟩
  refine ⟨T a, fun n hn => ?_⟩
  have h1 : T (Nat.findGreatest (T · ≤ n) n) ≤ n :=
    Nat.findGreatest_spec (P := (T · ≤ n)) ((hT.id_le a).trans hn) hn
  have h2 : n < T (Nat.findGreatest (T · ≤ n) n + 1) :=
    lt_of_not_ge fun hc =>
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) ((hT.id_le _).trans hc) hc
  rw [hg _ n ⟨h1, h2⟩]
  exact ha _ (Nat.le_findGreatest ((hT.id_le a).trans hn) hn)

/-
Given a lower bound sequence M and a property P that can always be satisfied eventually, there exists a strictly increasing sequence T bounded by M such that each interval [T_k, T_{k+1}) contains a witness for P.
-/
lemma exists_increasing_sequence_with_property (M : ℕ → ℕ) (P : ℕ → ℕ → Prop) (hP : ∀ k L, ∃ n ≥ L, P k n) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ k, T k ≥ M k) ∧ (∀ k, ∃ n ∈ Set.Ico (T k) (T (k + 1)), P k n) := by
  choose! w hw₁ hw₂ using hP
  refine ⟨fun k => Nat.rec (M 0) (fun k ih => max (M (k + 1)) (w k ih + 1)) k,
    strictMono_nat_of_lt_succ fun k => ?_, fun k => ?_, fun k => ?_⟩
  · exact lt_of_le_of_lt (hw₁ k _) (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
  · cases k
    · exact le_rfl
    · exact le_max_left _ _
  · exact ⟨w k _, ⟨hw₁ k _, lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)⟩, hw₂ k _⟩

/-
If g is a block sequence constructed from x and T, and each block contains a witness where f is bounded by y + 1/(k+1), then liminf f(g) <= y.
-/
lemma liminf_le_of_block_sequence_witnesses {α : Type*} (y : ℝ≥0) (f : α → ℕ → ℝ≥0∞)
    (T : ℕ → ℕ) (hT : StrictMono T) (x : ℕ → α) (g : ℕ → α)
    (hg : ∀ k, ∀ n ∈ Set.Ico (T k) (T (k + 1)), g n = x k)
    (hwit : ∀ k, ∃ n ∈ Set.Ico (T k) (T (k + 1)), f (x k) n ≤ (y : ℝ≥0∞) + (k + 1 : ℝ≥0)⁻¹) :
    Filter.atTop.liminf (fun n ↦ f (g n) n) ≤ y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨k₀, hk₀⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  refine Filter.liminf_le_of_frequently_le' (Filter.frequently_atTop.mpr fun a => ?_)
  obtain ⟨m, hm, hle⟩ := hwit (a ⊔ k₀)
  refine ⟨m, le_trans (le_sup_left.trans (hT.id_le _)) hm.1, ?_⟩
  rw [hg _ m hm]
  refine hle.trans ?_
  gcongr
  refine le_trans ?_ hk₀.le
  rw [ENNReal.coe_inv (by positivity)]
  exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ_of_le le_sup_right)

/-
If g is a block sequence constructed from x and T, and f is bounded by y + 1/(k+1) on each block, then limsup f(g) <= y.
-/
lemma limsup_le_of_block_sequence_bound {α : Type*} (y : ℝ≥0) (f : α → ℕ → ℝ≥0∞)
  (T : ℕ → ℕ) (hT : StrictMono T) (x : ℕ → α) (g : ℕ → α)
  (hg : ∀ k, ∀ n ∈ Set.Ico (T k) (T (k + 1)), g n = x k)
  (hbound : ∀ k, ∀ n ∈ Set.Ico (T k) (T (k + 1)), f (x k) n ≤ (y : ℝ≥0∞) + (k + 1 : ℝ≥0)⁻¹) :
  Filter.atTop.limsup (fun n ↦ f (g n) n) ≤ y := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨K, hK⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [Filter.eventually_ge_atTop (T K)] with b hb
    have hKf : K ≤ Nat.findGreatest (T · ≤ b) b :=
      Nat.le_findGreatest ((hT.id_le K).trans hb) hb
    have h1 : T (Nat.findGreatest (T · ≤ b) b) ≤ b :=
      Nat.findGreatest_spec (P := (T · ≤ b)) ((hT.id_le K).trans hb) hb
    have h2 : b < T (Nat.findGreatest (T · ≤ b) b + 1) :=
      lt_of_not_ge fun hc =>
        Nat.findGreatest_is_greatest (Nat.lt_succ_self _) ((hT.id_le _).trans hc) hc
    rw [hg _ b ⟨h1, h2⟩]
    refine (hbound _ b ⟨h1, h2⟩).trans ?_
    gcongr
    refine le_trans ?_ hK.le
    rw [ENNReal.coe_inv (by positivity)]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ_of_le hKf)

/- Version of `exists_liminf_zero_of_forall_liminf_le_with_UB` that lets you stipulate it for
two different functions simultaneously, one with liminf and one with limsup. -/
lemma exists_liminf_zero_of_forall_liminf_limsup_le_with_UB (y₁ y₂ : ℝ≥0) (f₁ f₂ : ℝ≥0 → ℕ → ℝ≥0∞)
    {z : ℝ≥0} (hz : 0 < z)
    (hf₁ : ∀ x > 0, Filter.atTop.liminf (f₁ x) ≤ y₁)
    (hf₂ : ∀ x > 0, Filter.atTop.limsup (f₂ x) ≤ y₂) :
      ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (∀ x, g x < z) ∧
        Filter.atTop.Tendsto g (𝓝 0) ∧
        Filter.atTop.liminf (fun n ↦ f₁ (g n) n) ≤ y₁ ∧
      Filter.atTop.limsup (fun n ↦ f₂ (g n) n) ≤ y₂ := by
  -- Fix some sequences of positive real numbers $x_k$ and $N_0(k)$.
  obtain ⟨x, hx₀, hx₁, hx₂⟩ : ∃ x : ℕ → ℝ≥0, (∀ k, 0 < x k) ∧ (∀ k, x k ≤ z / 2) ∧
      Filter.Tendsto x Filter.atTop (𝓝 0) := by
    refine ⟨fun k => min (z / 2) ((k : ℝ≥0) + 1)⁻¹,
      fun k => lt_min (by positivity) (by positivity), fun k => min_le_left _ _, ?_⟩
    have h2 : Filter.Tendsto (fun k : ℕ => ((k : ℝ≥0) + 1)⁻¹) Filter.atTop (𝓝 0) := by
      rw [← ENNReal.tendsto_coe]
      simpa [Function.comp_def] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun k => by positivity) (fun k => min_le_right _ _)
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ → ℕ, ∀ k, ∀ n ≥ N0 k, f₂ (x k) n ≤ y₂ + (k + 1 : ℝ≥0)⁻¹ := by
    have h (k : ℕ) : ∃ N, ∀ n ≥ N, f₂ (x k) n ≤ y₂ + (k + 1 : ℝ≥0)⁻¹ :=
      Filter.eventually_atTop.mp <| (Filter.eventually_lt_of_limsup_lt <|
        (hf₂ _ (hx₀ k)).trans_lt <|
        ENNReal.lt_add_right (by simp) (by simp)).mono fun n hn => hn.le
    exact ⟨fun k => (h k).choose, fun k => (h k).choose_spec⟩
  -- Define the sequence $T_k$ such that $T_k \geq N_0(k)$ and each interval $[T_k, T_{k+1})$
  -- contains some $n_k$ with $P(k, n_k)$.
  obtain ⟨T, hT_mono, hT_bound, hT_wit⟩ :=
    exists_increasing_sequence_with_property N0
      (fun k n => f₁ (x k) n ≤ y₁ + (k + 1 : ℝ≥0)⁻¹) fun k L => by
        have h : ∃ᶠ n in Filter.atTop, f₁ (x k) n < y₁ + (k + 1 : ℝ≥0)⁻¹ :=
          Filter.frequently_lt_of_liminf_lt (by isBoundedDefault)
            ((hf₁ _ (hx₀ k)).trans_lt (ENNReal.lt_add_right (by simp) (by simp)))
        obtain ⟨m, h₁, h₂⟩ := (h.and_eventually (Filter.eventually_ge_atTop L)).exists
        exact ⟨m, h₂, h₁.le⟩
  refine ⟨fun n => x (Nat.find (show ∃ k, n < T (k + 1) from ⟨n, hT_mono.id_le _⟩)),
    fun n => hx₀ _, fun n => (hx₁ _).trans_lt (half_lt_self hz), ?_, ?_, ?_⟩
  · refine hx₂.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨T b, fun a ha => ?_⟩)
    rw [← not_lt, Nat.find_lt_iff]
    push Not
    exact fun m hm => le_trans (hT_mono.monotone hm) ha
  · refine liminf_le_of_block_sequence_witnesses y₁ f₁ T hT_mono x _ ?_ hT_wit
    intro k m hm
    congr
    rw [Nat.find_eq_iff]
    exact ⟨hm.2, fun j hj => not_lt.mpr ((hT_mono.monotone hj).trans hm.1)⟩
  · refine limsup_le_of_block_sequence_bound y₂ f₂ T hT_mono x _ ?_
      fun k m hm => hN0 k m ((hT_bound k).trans hm.1)
    intro k m hm
    congr
    rw [Nat.find_eq_iff]
    exact ⟨hm.2, fun j hj => not_lt.mpr ((hT_mono.monotone hj).trans hm.1)⟩


--PULLOUT.
--PR? This is "not specific to our repo", but might be a bit too specialized to be in Mathlib. Not sure.
--Definitely would need to clean up the proof first
theorem extracted_limsup_inequality (z : ℝ≥0∞) (hz : z ≠ ⊤) (y x : ℕ → ℝ≥0∞) (h_lem5 : ∀ (n : ℕ), x n ≤ y n + z)
    : Filter.atTop.limsup (fun n ↦ x n / n) ≤ Filter.atTop.limsup (fun n ↦ y n / n) := by
  --Thanks Aristotle!
  simp only [Filter.limsup_eq, Filter.eventually_atTop, le_sInf_iff, Set.mem_setOf_eq,
    forall_exists_index]
  -- Taking the limit superior of both sides of the inequality x n / n ≤ y_n / n + z / n, we
  -- get limsup x n / n ≤ limsup (y n / n + z / n).
  intro b n h_bn
  have h_le : ∀ m ≥ n, x m / (m : ℝ≥0∞) ≤ b + z / (m : ℝ≥0∞) := by
    intro m hm
    grw [← h_bn m hm, ← ENNReal.add_div, h_lem5 m]
  -- Since z is finite, we have lim z / n = 0.
  have h_z_div_n_zero : Filter.atTop.Tendsto (fun n : ℕ ↦ z / (n : ℝ≥0∞)) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_div ENNReal.tendsto_nat_nhds_top (Or.inr hz)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rcases Filter.eventually_atTop.mp (h_z_div_n_zero.eventually <| gt_mem_nhds hε) with ⟨m, hm⟩
  refine sInf_le ⟨n + m, fun k hk => ?_⟩
  grw [h_le k (by omega), (hm k (by omega)).le]

--PULLOUT and PR
open Filter in
/-- Like `Filter.tendsto_add_atTop_iff_nat`, but with nat subtraction. -/
theorem _root_.Filter.tendsto_sub_atTop_iff_nat {α : Type*} {f : ℕ → α} {l : Filter α} (k : ℕ) :
    Tendsto (fun (n : ℕ) ↦ f (n - k)) atTop l ↔ Tendsto f atTop l :=
  show Tendsto (f ∘ fun n ↦ n - k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff, map_sub_atTop_eq_nat]

--PULLOUT and PR
open ENNReal Filter in
/-- Sort of dual to `ENNReal.tendsto_const_sub_nhds_zero_iff`. Takes a substantially different form though, since
we don't actually have equality of the limits, or even the fact that the other one converges, which is why we
need to use `limsup`. -/
theorem _root_.ENNReal.tendsto_sub_const_nhds_zero_iff {α : Type*} {l : Filter α} {f : α → ℝ≥0∞} {a : ℝ≥0∞}
    : Tendsto (f · - a) l (𝓝 0) ↔ limsup f l ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [tendsto_const_nhds]
  rw [ENNReal.tendsto_nhds_zero, limsup_le_iff']
  simp only [tsub_le_iff_left]
  refine ⟨fun h y hy => ?_, fun h ε hε => h (a + ε) (lt_add_right ha hε.ne')⟩
  have h' := h (y - a) (tsub_pos_of_lt hy)
  rwa [add_comm, tsub_add_cancel_of_le hy.le] at h'
