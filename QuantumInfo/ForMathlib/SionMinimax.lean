/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Data.Fintype.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

@[simp]
theorem Set.image2_flip {α β γ : Type*} {f : α → β → γ} (s : Set α) (t : Set β) :
    image2 (flip f) t s = image2 f s t :=
  (image2_swap f s t).symm

section ciSup

variable {ι α : Type*} [ConditionallyCompleteLattice α] {f g : ι → α} {a : α}

/-- The **max-min theorem**. A version of `iSup_iInf_le_iInf_iSup` for conditionally complete lattices. -/
theorem ciSup_ciInf_le_ciInf_ciSup {ι': Type*} [Nonempty ι]
  (f : ι → ι' → α) (Ha : ∀ j, BddAbove (Set.range (f · j))) (Hb : ∀ i, BddBelow (Set.range (f i))) :
    ⨆ i, ⨅ j, f i j ≤ ⨅ j, ⨆ i, f i j :=
  ciSup_le fun i ↦ ciInf_mono (Hb i) fun j ↦ le_ciSup (Ha j) i

theorem BddAbove.range_max (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) :
    BddAbove (Set.range (max f g)) :=
  bbdAbove_range_sup hf hg

theorem BddBelow.range_min (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g)) :
    BddBelow (Set.range (min f g)) :=
  BddAbove.range_max (α := αᵒᵈ) hf hg

theorem ciInf_eq_min_cInf_inter_diff (S T : Set ι)
  [Nonempty (S ∩ T : Set ι)] [Nonempty (S \ T : Set ι)] (hf : BddBelow (f '' S)) :
    ⨅ i : S, f i = (⨅ i : (S ∩ T : Set ι), f i) ⊓ ⨅ i : (S \ T : Set ι), f i := by
  rw [iInf, iInf, iInf, ← Set.image_eq_range, ← Set.image_eq_range, ← Set.image_eq_range,
    show f '' S = f '' (S ∩ T) ∪ f '' (S \ T) by rw [← Set.image_union, Set.inter_union_sdiff]]
  exact csInf_union (hf.mono (Set.image_mono Set.inter_subset_left))
    ((Set.nonempty_coe_sort.mp ‹_›).image f)
    (hf.mono (Set.image_mono Set.sdiff_subset)) ((Set.nonempty_coe_sort.mp ‹_›).image f)

variable [Nonempty ι]

theorem lt_ciInf_iff (hf : BddBelow (Set.range f)) :
    a < iInf f ↔ ∃ b, a < b ∧ ∀ (i : ι), b ≤ f i :=
  ⟨(⟨iInf f, ·, (ciInf_le hf ·)⟩), fun ⟨_, hb₁, hb₂⟩ ↦ lt_of_lt_of_le hb₁ (le_ciInf hb₂)⟩

theorem sup_ciSup (hf : BddAbove (Set.range f)) : a ⊔ ⨆ x, f x = ⨆ x, a ⊔ f x := by
  rw [ciSup_sup_eq (by simp) hf, ciSup_const]

theorem inf_ciInf (hf : BddBelow (Set.range f)) : a ⊓ ⨅ x, f x = ⨅ x, a ⊓ f x :=
  sup_ciSup (α := αᵒᵈ) hf

theorem ciInf_sup_ciInf_le (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g)) :
    (⨅ i, f i) ⊔ ⨅ i, g i ≤ ⨅ i, f i ⊔ g i :=
  le_ciInf (fun i ↦ sup_le_sup (ciInf_le hf i) (ciInf_le hg i))

theorem le_ciSup_inf_ciSup (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) :
    ⨆ (i : ι), f i ⊓ g i ≤ (⨆ (i : ι), f i) ⊓ ⨆ (i : ι), g i :=
  ciInf_sup_ciInf_le (α := αᵒᵈ) hf hg

end ciSup

theorem QuasiconvexOn.subset
  {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [LE β] [SMul 𝕜 E]
  {s : Set E} {f : E → β} (h : QuasiconvexOn 𝕜 s f) {t : Set E} (hts : t ⊆ s) (ht : Convex 𝕜 t) :
    QuasiconvexOn 𝕜 t f := by
  intro b
  convert ht.inter (h b) using 1
  simp +contextual [Set.ext_iff, @hts _]

theorem QuasiconvexOn.mem_segment_le_max
  {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SemilatticeSup β] [SMul 𝕜 E]
  {s : Set E} {f : E → β} (h : QuasiconvexOn 𝕜 s f)
  {x y z : E} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ segment 𝕜 x y):
    f z ≤ f x ⊔ f y :=
  ((h (f x ⊔ f y)).segment_subset (by simpa) (by simpa) hz).right

theorem QuasiconcaveOn.min_le_mem_segment
  {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SemilatticeInf β] [SMul 𝕜 E]
  {s : Set E} {f : E → β} (h : QuasiconcaveOn 𝕜 s f)
  {x y z : E} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ segment 𝕜 x y):
    f x ⊓ f y ≤ f z :=
  ((h (f x ⊓ f y)).segment_subset (by simpa) (by simpa) hz).right

theorem LowerSemicontinuousOn.bddBelow {α : Type*} [TopologicalSpace α] {S : Set α} {g : α → ℝ}
    (hg : LowerSemicontinuousOn g S) (hS : IsCompact S) : BddBelow (g '' S) :=
  hg.bddBelow_of_isCompact hS

theorem LowerSemicontinuousOn.max {α : Type*} [TopologicalSpace α] {S : Set α} {f g : α → ℝ}
    (hf : LowerSemicontinuousOn f S) (hg : LowerSemicontinuousOn g S) :
    LowerSemicontinuousOn (fun x ↦ max (f x) (g x)) S :=
  hf.sup hg

variable {α : Type*} [TopologicalSpace α] {β : Type*} [Preorder β] {f g : α → β} {x : α}
  {s t : Set α} {y z : β} {γ : Type*} [LinearOrder γ]

theorem lowerSemicontinuousOn_iff_isClosed_preimage {f : α → γ} [IsClosed s] :
    LowerSemicontinuousOn f s ↔ ∀ y, IsClosed (s ∩ f ⁻¹' Set.Iic y) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  exact forall_congr' fun y ↦
    ⟨fun ⟨v, hv, hveq⟩ ↦ hveq ▸ IsClosed.inter ‹_› hv,
      fun h ↦ ⟨_, h, by rw [← Set.inter_assoc, Set.inter_self]⟩⟩

theorem segment.isConnected {E : Type u_1} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] (a b : E) :
    IsConnected (segment ℝ a b) :=
  (convex_segment a b).isConnected ⟨a, left_mem_segment ℝ a b⟩

theorem BddAbove.range_inf_of_image2 {M N α : Type*} {f : M → N → α} [ConditionallyCompleteLinearOrder α]
  {S : Set M} {T : Set N} (h_bddA : BddAbove (Set.image2 f S T)) (h_bddB : BddBelow (Set.image2 f S T)) :
    BddAbove (Set.range fun y : T ↦ ⨅ x : S, f x y) := by
  rcases isEmpty_or_nonempty T with hT | hT
  · aesop
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp [Set.range, iInf]
  obtain ⟨z, hz⟩ := h_bddA
  obtain ⟨w, hw⟩ := h_bddB
  refine ⟨z, Set.forall_mem_range.2 fun y ↦
    (ciInf_le ⟨w, Set.forall_mem_range.2 (hw <| Set.mem_image2_of_mem ·.2 y.2)⟩ ⟨x, hx⟩).trans
      (hz (Set.mem_image2_of_mem hx y.2))⟩

theorem BddBelow.range_sup_of_image2 {M N α : Type*} {f : M → N → α} [ConditionallyCompleteLinearOrder α]
  {S : Set M} {T : Set N} (h_bddA : BddAbove (Set.image2 f S T)) (h_bddB : BddBelow (Set.image2 f S T)) :
      BddBelow (Set.range fun y : T ↦ ⨆ x : S, f x y) :=
  BddAbove.range_inf_of_image2 (α := αᵒᵈ) h_bddB h_bddA

theorem ciInf_le_ciInf_of_subset {α β : Type*} [ConditionallyCompleteLattice α]
  {f : β → α} {s t : Set β} (hs : s.Nonempty) (hf : BddBelow (f '' t)) (hst : s ⊆ t) :
    ⨅ x : t, f x ≤ ⨅ x : s, f x := by
  rw [iInf, iInf, ← Set.image_eq_range, ← Set.image_eq_range]
  exact csInf_le_csInf hf (hs.image f) (Set.image_mono hst)

theorem LowerSemicontinuousOn.dite_top {α β : Type*} [TopologicalSpace α] [Preorder β] [OrderTop β]
  {s : Set α} (p : α → Prop) [DecidablePred p] {f : (a : α) → p a → β}
  (hf : LowerSemicontinuousOn (fun x : Subtype p ↦ f x.val x.prop) {x | x.val ∈ s})
  (h_relatively_closed : ∃ U : Set α, IsClosed U ∧ s ∩ U = s ∩ setOf p) :
    LowerSemicontinuousOn (fun x ↦ dite (p x) (f x) (fun _ ↦ ⊤)) s := by
  rcases h_relatively_closed with ⟨u, ⟨hu, hsu⟩⟩
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff] at hsu
  intro x hx y hy
  dsimp at hy
  split_ifs at hy with h
  · specialize hf ⟨x, h⟩ hx y hy
    rw [ eventually_nhdsWithin_iff ] at hf ⊢
    rw [ nhds_subtype_eq_comap, Filter.eventually_comap ] at hf;
    filter_upwards [hf]
    simp only [Subtype.forall]
    grind [lt_top_of_lt]
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hu.isOpen_compl.mem_nhds (show x ∉ u by grind))]
    intros
    simp_all only [Set.mem_compl_iff, ↓reduceDIte]

theorem LowerSemicontinuousOn.comp_continuousOn {α β γ : Type*}
  [TopologicalSpace α] [TopologicalSpace β] [Preorder γ] {f : α → β} {s : Set α} {g : β → γ} {t : Set β}
  (hg : LowerSemicontinuousOn g t) (hf : ContinuousOn f s) (h : Set.MapsTo f s t) :
    LowerSemicontinuousOn (g ∘ f) s := by
  intro x hx y hy
  filter_upwards [(hf x hx).eventually (eventually_nhdsWithin_iff.mp (hg (f x) (h hx) y hy)),
    self_mem_nhdsWithin] with z hz hzs using hz (h hzs)

theorem UpperSemicontinuousOn.comp_continuousOn {α β γ : Type*}
  [TopologicalSpace α] [TopologicalSpace β] [Preorder γ] {f : α → β} {s : Set α} {g : β → γ} {t : Set β}
  (hg : UpperSemicontinuousOn g t) (hf : ContinuousOn f s) (h : Set.MapsTo f s t) :
    UpperSemicontinuousOn (g ∘ f) s :=
  LowerSemicontinuousOn.comp_continuousOn (γ := γᵒᵈ) hg hf h

theorem LowerSemicontinuousOn.ite_top {α β : Type*} [TopologicalSpace α] [Preorder β] [OrderTop β]
  {s : Set α} (p : α → Prop) [DecidablePred p] {f : (a : α) → β} (hf : LowerSemicontinuousOn f (s ∩ setOf p))
  (h_relatively_closed : ∃ U : Set α, IsClosed U ∧ s ∩ U = s ∩ setOf p) :
    LowerSemicontinuousOn (fun x ↦ ite (p x) (f x) ⊤) s :=
  dite_top p (hf.comp_continuousOn (by fun_prop) (by intro; simp)) h_relatively_closed

theorem LeftOrdContinuous.comp_lowerSemicontinuousOn_strong_assumptions {α γ δ : Type*}
  [TopologicalSpace α] [LinearOrder γ] [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
  [TopologicalSpace γ] [OrderTopology γ] [DenselyOrdered γ] [DenselyOrdered δ]
  {s : Set α} {g : γ → δ} {f : α → γ} (hg : LeftOrdContinuous g) (hf : LowerSemicontinuousOn f s) (hg2 : Monotone g) :
    LowerSemicontinuousOn (g ∘ f) s := by
  intro x hx y hy
  obtain ⟨_, ⟨z, hz, rfl⟩, hyz, -⟩ := (hg isLUB_Iio).exists_between hy
  filter_upwards [hf x hx z hz] with w hw using hyz.trans_le (hg2 hw.le)

theorem UpperSemicontinuousOn.frequently_lt_of_tendsto {α β γ : Type*} [TopologicalSpace β] [Preorder γ]
  {f : β → γ} {T : Set β} (hf : UpperSemicontinuousOn f T) {c : γ} {zs : α → β} {z : β}
  {l : Filter α} [l.NeBot] (hzs : l.Tendsto zs (nhds z)) (hx₂ : f z < c) (hzI : ∀ a, zs a ∈ T) (hzT : z ∈ T) :
    ∀ᶠ a in l, f (zs a) < c := by
  filter_upwards [hzs.eventually (eventually_nhdsWithin_iff.mp (hf z hzT c hx₂))] with n hn
    using hn (hzI n)

theorem Finset.ciInf_insert {α β : Type*} [DecidableEq α] [ConditionallyCompleteLattice β]
  (t : Finset α) (ht : t.Nonempty) (x : α) (f : α → β) :
    ⨅ (a : (insert x t : _)), f a = f x ⊓ ⨅ (a : t), f a := by
  have _ := Finset.nonempty_coe_sort.mpr ht
  have _ := Finset.nonempty_coe_sort.mpr (t.insert_nonempty x)
  refine eq_of_forall_le_iff fun c ↦ ?_
  simp only [le_inf_iff, le_ciInf_iff (Set.finite_range _).bddBelow, Subtype.forall,
    Finset.mem_insert, forall_eq_or_imp]

theorem Finset.ciSup_insert {α β : Type*} [DecidableEq α] [ConditionallyCompleteLattice β]
  (t : Finset α) (ht : t.Nonempty) (x : α) (f : α → β) :
    ⨆ (a : (insert x t : _)), f a = f x ⊔ ⨆ (a : t), f a :=
  t.ciInf_insert (β := βᵒᵈ) ht x f

section sion_minimax
/-!
Following https://projecteuclid.org/journals/kodai-mathematical-journal/volume-11/issue-1/Elementary-proof-for-Sions-minimax-theorem/10.2996/kmj/1138038812.full, with some corrections. There are two errors in Lemma 2 and the main theorem: an incorrect step that
`(∀ x, a < f x) → (a < ⨅ x, f x)`. This is repaired by taking an extra `exists_between` to get `a < b < ⨅ ...`, concluding that
`(∀ x, b < f x) → (b ≤ ⨅ x, f x)` and so `(a < ⨅ x, f x)`.
-/

variable  {M : Type*} [NormedAddCommGroup M]
  {N : Type*}
  {f : M → N → ℝ} {S : Set M} {T : Set N}
  (hfc₂ : ∀ y, y ∈ T → LowerSemicontinuousOn (f · y) S)
  (hS₁ : IsCompact S) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)

include hfc₂ hS₁ hS₃ in
private theorem sion_exists_min_lowerSemi (a : ℝ) (hc : ∀ y₀ : T, ⨅ (x : S), f (↑x) y₀ ≤ a) (z : N) (hzT : z ∈ T) :
    ∃ x ∈ S, f x z ≤ a := by
  let _ := hS₃.to_subtype
  obtain ⟨x₀, hx₀S, hmin⟩ := (hfc₂ z hzT).exists_isMinOn hS₃ hS₁
  exact ⟨x₀, hx₀S, (le_ciInf fun x ↦ hmin x.2).trans (hc ⟨z, hzT⟩)⟩

variable [Module ℝ M] [ContinuousSMul ℝ M]
variable [AddCommGroup N] [TopologicalSpace N] [SequentialSpace N] [T2Space N] [ContinuousAdd N] [Module ℝ N] [ContinuousSMul ℝ N]
variable
  (hfc₁ : ∀ x, x ∈ S → UpperSemicontinuousOn (f x) T)
  (hfq₂ : ∀ y, y ∈ T → QuasiconvexOn ℝ S (f · y))
  (hfq₁ : ∀ x, x ∈ S → QuasiconcaveOn ℝ T (f x))
  (hT₂ : Convex ℝ T) (hS₂ : Convex ℝ S)

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hT₂ hS₃ in
private lemma sion_exists_min_2 (y₁ y₂ : N) (hy₁ : y₁ ∈ T) (hy₂ : y₂ ∈ T)
    (a : ℝ) (ha : a < ⨅ x : S, (max (f x y₁) (f x y₂)))
    : ∃ y₀ : T, a < ⨅ x : S, f x y₀ := by
  by_contra! hc
  have _ := hS₁.isClosed
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_between ha
  let C : N → Set M := fun z ↦ { x ∈ S | f x z ≤ a }
  let C' : N → Set M := fun z ↦ { x ∈ S | f x z ≤ β }
  let A := C' y₁
  let B := C' y₂
  have hC_subset_C' (z) : C z ⊆ C' z :=
    fun x hx ↦ ⟨hx.1, hx.2.trans hβ₁.le⟩
  have hC_nonempty (z) (hz : z ∈ segment ℝ y₁ y₂) : (C z).Nonempty :=
    sion_exists_min_lowerSemi hfc₂ hS₁ hS₃ a hc z (hT₂.segment_subset hy₁ hy₂ hz)
  have hC'_nonempty (z) (hz : z ∈ segment ℝ y₁ y₂) : (C' z).Nonempty :=
    (hC_nonempty z hz).mono (hC_subset_C' z)
  have hC'_closed (z) (hz : z ∈ segment ℝ y₁ y₂) : IsClosed (C' z) :=
    lowerSemicontinuousOn_iff_isClosed_preimage.mp (hfc₂ z (hT₂.segment_subset hy₁ hy₂ hz)) β
  have hA_closed : IsClosed A := hC'_closed y₁ (left_mem_segment ℝ y₁ y₂)
  have hB_closed : IsClosed B := hC'_closed y₂ (right_mem_segment ℝ y₁ y₂)
  have hAB : A ∩ B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨hxS, h₁⟩, -, h₂⟩
    exact (hβ₂.trans_le (ciInf_le ((((hfc₂ y₁ hy₁).max (hfc₂ y₂ hy₂)).bddBelow hS₁).mono
      (by rw [Set.image_eq_range])) ⟨x, hxS⟩)).not_ge (max_le h₁ h₂)
  have hfxz (x) (hx : x ∈ S) (z) (hz : z ∈ segment ℝ y₁ y₂) : min (f x y₁) (f x y₂) ≤ f x z :=
    (hfq₁ x hx).min_le_mem_segment hy₁ hy₂ hz
  have hC'zAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C' z ⊆ A ∪ B := by
    intro; grind [inf_le_iff, le_trans]
  have hC'zAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C' z ⊆ A ∨ C' z ⊆ B := by
    have hC' := ((hfq₂ z (hT₂.segment_subset hy₁ hy₂ hz) β).isConnected
      (hC'_nonempty z hz)).isPreconnected
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hC'
    exact hC' A B hA_closed hB_closed (hC'zAB z hz) (by simp [hAB])
  have hCzAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C z ⊆ A ∨ C z ⊆ B :=
    (hC'zAB z hz).imp (hC_subset_C' z).trans (hC_subset_C' z).trans
  have h_not_CzAB (z) (hz : z ∈ segment ℝ y₁ y₂) : ¬(C z ⊆ A ∧ C z ⊆ B) :=
    fun ⟨h₁, h₂⟩ ↦ (hC_nonempty z hz).elim fun x hx ↦
      Set.eq_empty_iff_forall_notMem.mp hAB x ⟨h₁ hx, h₂ hx⟩
  let I : Set N := { z | z ∈ segment ℝ y₁ y₂ ∧ C z ⊆ A}
  let J : Set N := { z | z ∈ segment ℝ y₁ y₂ ∧ C z ⊆ B}
  have hI₁ : I.Nonempty := ⟨y₁, left_mem_segment ℝ y₁ y₂, hC_subset_C' y₁⟩
  have hJ₁ : J.Nonempty := ⟨y₂, right_mem_segment ℝ y₁ y₂, hC_subset_C' y₂⟩
  rw [Set.nonempty_iff_ne_empty] at hI₁ hJ₁
  have hIJ : I ∩ J = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨hz, hCzA⟩, -, hCzB⟩
    obtain ⟨x, hx⟩ := hC_nonempty z hz
    exact Set.eq_empty_iff_forall_notMem.mp hAB x ⟨hCzA hx, hCzB hx⟩
  have hIJ₂ : I ∪ J = segment ℝ y₁ y₂ := by
    simp [I, J, Set.ext_iff]
    grind
  have hseg : IsClosed (segment ℝ y₁ y₂) := closure_openSegment (𝕜 := ℝ) y₁ y₂ ▸ isClosed_closure
  have hI : IsClosed I := by
    refine IsSeqClosed.isClosed fun zs z hzI hzs ↦ ?_
    have hz_mem : z ∈ segment ℝ y₁ y₂ := hseg.isSeqClosed (fun n ↦ (hzI n).1) hzs
    obtain ⟨x, hxS, hxz⟩ := hC_nonempty z hz_mem
    refine ⟨hz_mem, (hCzAB z hz_mem).resolve_right fun hCB ↦ ?_⟩
    obtain ⟨n, hn⟩ := ((hfc₁ x hxS).frequently_lt_of_tendsto hzs (hxz.trans_lt hβ₁)
      (fun n ↦ hT₂.segment_subset hy₁ hy₂ (hzI n).1) (hT₂.segment_subset hy₁ hy₂ hz_mem)).exists
    have hxA : x ∈ A := (hC'zAB (zs n) (hzI n).1).resolve_right
      (fun h ↦ h_not_CzAB (zs n) (hzI n).1 ⟨(hzI n).2, (hC_subset_C' _).trans h⟩) ⟨hxS, hn.le⟩
    exact Set.eq_empty_iff_forall_notMem.mp hAB x ⟨hxA, hCB ⟨hxS, hxz⟩⟩
  have hJ : IsClosed J := by
    refine IsSeqClosed.isClosed fun zs z hzI hzs ↦ ?_
    have hz_mem : z ∈ segment ℝ y₁ y₂ := hseg.isSeqClosed (fun n ↦ (hzI n).1) hzs
    obtain ⟨x, hxS, hxz⟩ := hC_nonempty z hz_mem
    refine ⟨hz_mem, (hCzAB z hz_mem).resolve_left fun hCA ↦ ?_⟩
    obtain ⟨n, hn⟩ := ((hfc₁ x hxS).frequently_lt_of_tendsto hzs (hxz.trans_lt hβ₁)
      (fun n ↦ hT₂.segment_subset hy₁ hy₂ (hzI n).1) (hT₂.segment_subset hy₁ hy₂ hz_mem)).exists
    have hxB : x ∈ B := (hC'zAB (zs n) (hzI n).1).resolve_left
      (fun h ↦ h_not_CzAB (zs n) (hzI n).1 ⟨(hC_subset_C' _).trans h, (hzI n).2⟩) ⟨hxS, hn.le⟩
    exact Set.eq_empty_iff_forall_notMem.mp hAB x ⟨hCA ⟨hxS, hxz⟩, hxB⟩
  have hConnected := segment.isConnected y₁ y₂
  rw [IsConnected, isPreconnected_iff_subset_of_fully_disjoint_closed hseg] at hConnected
  replace hConnected := hConnected.right I J
  simp [hIJ, ← hIJ₂, Set.disjoint_iff_inter_eq_empty] at hConnected
  obtain hL | hR := hConnected hI hJ
  · rw [Set.inter_eq_self_of_subset_right hL] at hIJ
    exact hJ₁ hIJ
  · rw [Set.inter_eq_self_of_subset_left hR] at hIJ
    exact hI₁ hIJ

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ in
private lemma sion_exists_min_fin
  (h_bddA : BddAbove (Set.image2 f S T)) (h_bddB : BddBelow (Set.image2 f S T))
  (ys : Finset N) (hys_n : ys.Nonempty) (hys : (ys : Set N) ⊆ T)
  (a : ℝ) (ha : a < ⨅ x : S, ⨆ yi : ys, f x yi)
    : ∃ y₀ : T, a < ⨅ x : S, f x y₀ := by
  induction hys_n using Finset.Nonempty.cons_induction generalizing S
  case singleton x =>
    simp at ha hys
    use ⟨x, hys⟩
  case cons yₙ t hxt htn ih =>
    classical rw [Finset.cons_eq_insert] at hys ha
    simp [Set.insert_subset_iff] at hys
    rcases hys with ⟨hyₙ, ht⟩
    let _ := hS₃.to_subtype
    obtain ⟨b, hab, hb⟩ := exists_between ha
    let S' := {z : M | z ∈ S ∧ f z yₙ ≤ b}
    have hS'_sub : S' ⊆ S := Set.sep_subset ..
    rcases S'.eq_empty_or_nonempty with hS'_e | hS'_n
    · simp [S'] at hS'_e
      exact ⟨⟨yₙ, hyₙ⟩, (lt_ciInf_iff (((hfc₂ yₙ hyₙ).bddBelow hS₁).mono
        (by rw [Set.image_eq_range]))).2 ⟨b, hab, fun i ↦ (hS'_e i i.2).le⟩⟩
    let _ := hS'_n.to_subtype
    have hS'₁ : IsCompact S' := by
      have := hS₁.isClosed
      exact hS₁.of_isClosed_subset
        (lowerSemicontinuousOn_iff_isClosed_preimage.mp (hfc₂ yₙ hyₙ) b) hS'_sub
    have hS'₂ : Convex ℝ S' := hfq₂ _ hyₙ _
    have ha' : a < ⨅ x : S', ⨆ yi : t, f x yi := by
      classical
      refine hab.trans_le (le_ciInf fun x ↦ ?_)
      have h1 : b < ⨆ yi : { x // x ∈ (Insert.insert yₙ t : Finset N)}, f ↑x ↑yi :=
        hb.trans_le (ciInf_le (BddBelow.range_sup_of_image2
          (T := S) (S := { x | x ∈ insert yₙ t }) (f := flip f)
          (by apply h_bddA.mono; simp [flip]; grind)
          (by apply h_bddB.mono; simp [flip]; grind)) ⟨↑x, hS'_sub x.2⟩)
      rw [t.ciSup_insert htn] at h1
      exact ((lt_sup_iff.mp h1).resolve_left (not_lt.mpr x.2.2)).le
    specialize @ih S'
      (hfc₂ · · |>.mono hS'_sub) hS'₁ hS'_n
      (hfc₁ · <| hS'_sub ·) (hfq₂ · · |>.subset hS'_sub hS'₂)
      (hfq₁ · <| hS'_sub ·) hS'₂
      (h_bddA.mono <| Set.image2_subset_right hS'_sub)
      (h_bddB.mono <| Set.image2_subset_right hS'_sub) ht ha'
    obtain ⟨y₀', hy₀'⟩ := ih
    refine (sion_exists_min_2 hfc₂ hS₁ hS₃ hfc₁ hfq₂ hfq₁
      hT₂ y₀' yₙ y₀'.2 hyₙ a ?_)
    by_cases hS'eq : S' = S
    · rw [hS'eq] at hy₀'
      apply hy₀'.trans_le
      gcongr
      · exact ((hfc₂ y₀' y₀'.2).bddBelow hS₁).mono (by rw [Set.image_eq_range])
      exact le_sup_left
    have hS_diff_ne : (S \ S').Nonempty :=
      Set.nonempty_of_ssubset (hS'_sub.ssubset_of_ne hS'eq)
    apply Set.Nonempty.to_subtype at hS_diff_ne
    have h_non_inter : Nonempty ↑(S ∩ S') := by
      rwa [Set.inter_eq_self_of_subset_right hS'_sub]
    rw [ciInf_eq_min_cInf_inter_diff (f := fun x ↦ max (f x y₀') (f x yₙ)) S S']; swap
    · --BddAbove ((fun x => max (f x y₀') (f x yₙ)) '' S)
      apply h_bddB.mono
      rintro _ ⟨x, hx, rfl⟩
      use x, hx
      grind
    rw [lt_inf_iff]
    constructor
    · rw [Set.inter_eq_self_of_subset_right hS'_sub]
      apply hy₀'.trans_le
      gcongr
      · exact h_bddB.mono (Set.range_subset_iff.2
          fun x ↦ Set.mem_image2_of_mem (hS'_sub x.2) y₀'.2)
      exact le_sup_left
    · exact hab.trans_le (le_ciInf fun x ↦
        le_sup_of_le_right (not_le.mp fun h ↦ x.2.2 ⟨x.2.1, h⟩).le)

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃ in
/-- **Sion's Minimax theorem**. Because of `ciSup` and `ciInf` junk values when f isn't
bounded, we need to assume that it's bounded above and below. -/
theorem sion_minimax
  (h_bddA : BddAbove (Set.image2 f S T))
  (h_bddB : BddBelow (Set.image2 f S T))
    : ⨅ x : S, ⨆ y : T, f x y = ⨆ y : T, ⨅ x : S, f x y := by
  have _ := hS₁.isClosed
  have _ := hS₃.to_subtype
  have _ := hT₃.to_subtype
  have h_bdd_0 (i : T) : BddBelow (Set.range fun j : S ↦ f j i) :=
    --This one doesn't require h_bddB, it follows from compactness + semicontinuity
    ((hfc₂ i i.2).bddBelow hS₁).mono (by rw [Set.image_eq_range])
  have h_bdd_1 (j : S) : BddAbove (Set.range fun (x : T) => f j x) :=
    h_bddA.mono (T.range_restrict (f j) ▸ Set.image_subset_image2_right j.coe_prop)
  have h_bdd_2 : BddAbove (Set.range fun y : T ↦ ⨅ x : S, f x y) :=
    h_bddA.range_inf_of_image2 h_bddB
  have h_bdd_3 : BddBelow (Set.range fun x : S ↦ ⨆ y : T, f x y) :=
    BddBelow.range_sup_of_image2 (f := flip f) (by simpa) (by simpa)
  apply le_antisymm; swap
  · exact ciSup_ciInf_le_ciInf_ciSup _ h_bdd_1 h_bdd_0
  by_contra! h
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h; clear h
  obtain ⟨b, hb₁, hb₂⟩ := exists_between ha₂; clear ha₂
  revert ha₁
  rw [imp_false, not_lt]
  have := hS₁.elim_finite_subfamily_closed (fun (y : T) ↦ { x | x ∈ S ∧ f x y ≤ b}) ?_ ?_
  · rcases this with ⟨u, hu⟩
    have hu' : u.Nonempty := by
      grind [Finset.not_nonempty_iff_eq_empty, Set.iInter_univ,
        Set.inter_univ, Set.not_nonempty_empty]
    have hau : a < ⨅ x : S, ⨆ yi : u.map ⟨_, Subtype.val_injective⟩, f ↑x ↑yi := by
      simp +contextual only [Set.iInter_coe_set, Set.ext_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, true_and, not_forall,
        not_le] at hu
      rw [lt_ciInf_iff]; swap
      · exact BddBelow.range_sup_of_image2 (T := S)
          (S := u.map ⟨_, Subtype.val_injective⟩) (f := flip f)
          (by apply h_bddA.mono; simp [flip]; grind) (by apply h_bddB.mono; simp [flip]; grind)
      refine ⟨b, hb₁, fun i ↦ ?_⟩
      obtain ⟨c, hc₁, hc₂, hc₃⟩ := hu i i.2
      refine le_ciSup_of_le ?_ ⟨c, by simpa using ⟨hc₁, hc₂⟩⟩ hc₃.le
      --BddAbove (Set.range fun yi : Finset.map ⋯ => f ↑i ↑yi)
      apply h_bddA.mono
      simp [Set.range, Set.image2]; grind
    obtain ⟨y₀, hy₀⟩ := sion_exists_min_fin hfc₂ hS₁ hS₃ hfc₁ hfq₂ hfq₁ hT₂ hS₂
      h_bddA h_bddB (u.map ⟨_, Subtype.val_injective⟩) (by simpa) (by simp) a hau
    exact hy₀.le.trans (le_ciSup h_bdd_2 y₀)
  · exact fun i ↦ lowerSemicontinuousOn_iff_isClosed_preimage.mp (hfc₂ i i.2) b
  · convert Set.inter_empty _
    by_contra hu
    simp only [Set.iInter_coe_set, Set.iInter_eq_empty_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Classical.not_imp, not_and, not_le, not_forall, not_exists, not_lt] at hu
    obtain ⟨x, hx⟩ := hu
    exact hb₂.not_ge ((ciInf_le h_bdd_3 ⟨x, hx _ hT₃.some_mem |>.1⟩).trans
      (ciSup_le (hx _ ·.2 |>.2)))
