/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.Superadditive
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.MonotoneConvergence

/-! Definition of "Regularized quantities" as are common in information theory,
from one-shot versions, and good properties coming from Fekete's lemma.
-/

@[expose] public section

variable {T : Type*} [ConditionallyCompleteLattice T]

/-- An `InfRegularized` value is the lim sup of value at each natural number, but requires
 a proof of lower- and upper-bounds to be defined. -/
noncomputable def InfRegularized (fn : ℕ → T) {lb ub : T}
    (_ : ∀ n, lb ≤ fn n) (_ : ∀ n, fn n ≤ ub) : T :=
  Filter.atTop.liminf fn

/-- A `SupRegularized` value is the lim sup of value at each natural number, but requires
 a proof of lower- and upper-bounds to be defined. -/
noncomputable def SupRegularized (fn : ℕ → T) {lb ub : T}
    (_ : ∀ n, lb ≤ fn n) (_ : ∀ n, fn n ≤ ub) : T :=
  Filter.atTop.limsup fn

namespace InfRegularized

variable {fn : ℕ → T} {_lb _ub : T} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- The `InfRegularized` value is also lower bounded. -/
theorem lb : _lb ≤ InfRegularized fn hl hu :=
  Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le _ hu) (.of_forall hl)

/-- The `InfRegularized` value is also upper bounded. -/
theorem ub : InfRegularized fn hl hu ≤ _ub :=
  Filter.liminf_le_of_le (Filter.isBoundedUnder_of_eventually_ge (.of_forall hl))
    fun _ hb => hb.exists.choose_spec.trans (hu _)

/-- For `Antitone` functions, the `InfRegularized` is the supremum of values. -/
theorem anti_inf (h : Antitone fn) :
    InfRegularized fn hl hu = sInf (Set.range fn) :=
  le_antisymm
    (le_csInf (Set.range_nonempty fn) fun _ ⟨n, hn⟩ => hn ▸
      Filter.liminf_le_of_le (Filter.isBoundedUnder_of_eventually_ge (.of_forall hl))
        fun _ hb => ((Filter.eventually_atTop.1 hb).choose_spec _ (le_max_left _ n)).trans
          (h (le_max_right _ n)))
    (Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le _ hu)
      (.of_forall fun n => csInf_le ⟨_lb, Set.forall_mem_range.2 hl⟩ ⟨n, rfl⟩))

/-- For `Antitone` functions, the `InfRegularized` is lower bounded by
  any particular value. -/
theorem anti_ub (h : Antitone fn) : ∀ n, InfRegularized fn hl hu ≤ fn n := fun n =>
  Filter.liminf_le_of_le (Filter.isBoundedUnder_of_eventually_ge (.of_forall hl))
    fun _ hb => ((Filter.eventually_atTop.1 hb).choose_spec _ (le_max_left _ n)).trans
      (h (le_max_right _ n))

end InfRegularized

namespace SupRegularized

variable {fn : ℕ → T} {_lb _ub : T} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- The `SupRegularized` value is also lower bounded. -/
theorem lb : _lb ≤ SupRegularized fn hl hu :=
  Filter.le_limsup_of_le (Filter.isBoundedUnder_of_eventually_le (.of_forall hu))
    fun _ hb => (hl _).trans hb.exists.choose_spec

/-- The `SupRegularized` value is also upper bounded. -/
theorem ub : SupRegularized fn hl hu ≤ _ub :=
  Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le _ hl) (.of_forall hu)

/-- For `Monotone` functions, the `SupRegularized` is the supremum of values. -/
theorem mono_sup (h : Monotone fn) :
    SupRegularized fn hl hu = sSup { fn n | n : ℕ} :=
  le_antisymm
    (Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le _ hl)
      (.of_forall fun n => le_csSup ⟨_ub, Set.forall_mem_range.2 hu⟩ ⟨n, rfl⟩))
    (csSup_le ⟨fn 0, 0, rfl⟩ fun _ ⟨n, hn⟩ => hn ▸
      Filter.le_limsup_of_le (Filter.isBoundedUnder_of_eventually_le (.of_forall hu))
        fun _ hb => (h (le_max_right _ n)).trans
          ((Filter.eventually_atTop.1 hb).choose_spec _ (le_max_left _ n)))

/-- For `Monotone` functions, the `SupRegularized` is lower bounded by
  any particular value. -/
theorem mono_lb (h : Monotone fn) : ∀ n, fn n ≤ SupRegularized fn hl hu := fun n =>
  Filter.le_limsup_of_le (Filter.isBoundedUnder_of_eventually_le (.of_forall hu))
    fun _ hb => (h (le_max_right _ n)).trans
      ((Filter.eventually_atTop.1 hb).choose_spec _ (le_max_left _ n))

end SupRegularized

section real

private def realNegOrderIso : ℝ ≃o ℝᵒᵈ where
  toEquiv := Equiv.neg ℝ
  map_rel_iff' := neg_le_neg_iff

private theorem limsup_eq_neg_liminf_neg {fn : ℕ → ℝ} {_lb _ub : ℝ}Expand commentComment on line R131Resolved
    (hl : ∀ n, _lb ≤ fn n) (hu : ∀ n, fn n ≤ _ub) :
    Filter.atTop.limsup fn = -Filter.atTop.liminf (fun n => -fn n) := by
  have hneg : -Filter.atTop.limsup fn = Filter.atTop.liminf (fun n => -fn n) := by
    have hdual := OrderIso.limsup_apply (f := Filter.atTop) (u := fn) realNegOrderIso
      (hu := Filter.isBoundedUnder_of_eventually_le (f := Filter.atTop) (u := fn)
        (Filter.Eventually.of_forall hu))
      (hu_co := Filter.isCoboundedUnder_le_of_le Filter.atTop hl)
      (hgu := Filter.isBoundedUnder_of_eventually_le (α := ℝᵒᵈ) (f := Filter.atTop)
        (u := fun n => (-fn n : ℝᵒᵈ)) (Filter.Eventually.of_forall fun n => neg_le_neg (hu n)))
      (hgu_co := Filter.isCoboundedUnder_le_of_le (α := ℝᵒᵈ) Filter.atTop
        (f := fun n => (-fn n : ℝᵒᵈ)) (x := (-_lb : ℝᵒᵈ)) fun n => neg_le_neg (hl n))
    simpa [Filter.limsup, Filter.liminf, Filter.limsSup, Filter.limsInf, realNegOrderIso] using
      congrArg OrderDual.ofDual hdual
  linarith

variable {fn : ℕ → ℝ} {_lb _ub : ℝ} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

theorem InfRegularized.to_SupRegularized : InfRegularized fn hl hu = -SupRegularized (-fn ·)
    (lb := -_ub) (ub := -_lb) (neg_le_neg_iff.mpr <| hu ·) (neg_le_neg_iff.mpr <| hl ·) := by
  have liminf_neg : Filter.liminf fn Filter.atTop = -(Filter.limsup (-fn) Filter.atTop) := by
    simp [Filter.limsup_eq, Filter.liminf_eq, Real.sInf_def]
  exact Real.ext_cauchy (congrArg Real.cauchy liminf_neg)

theorem SupRegularized.to_InfRegularized : SupRegularized fn hl hu = -InfRegularized (-fn ·)
    (lb := -_ub) (ub := -_lb) (neg_le_neg_iff.mpr <| hu ·) (neg_le_neg_iff.mpr <| hl ·) := by
  have limsup_neg : Filter.limsup fn Filter.atTop = -(Filter.liminf (-fn) Filter.atTop) := by
    simp [Filter.limsup_eq, Filter.liminf_eq, Real.sInf_def, le_neg]
  exact Real.ext_cauchy (congrArg Real.cauchy limsup_neg)

/-- For `Antitone` functions, the value `Filter.Tendsto` the `InfRegularized` value. -/
theorem InfRegularized.anti_tendsto (h : Antitone fn) :
    Filter.Tendsto fn .atTop (nhds (InfRegularized fn hl hu)) := by
  convert tendsto_atTop_ciInf h ⟨_lb, fun _ ⟨a,b⟩ ↦ b ▸ hl a⟩
  rw [InfRegularized.anti_inf h, iInf.eq_1]

variable {f₁ : ℕ → ℝ} {_lb _ub : ℝ} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

theorem InfRegularized.of_Subadditive (hf : Subadditive (fun n ↦ fn n * n))
    :
    hf.lim = InfRegularized fn hl hu := by
  have h₁ := hf.tendsto_lim (by
    use min 0 _lb
    rw [mem_lowerBounds]
    rintro x ⟨y,(rfl : _ / _ = _)⟩
    rcases y with (_|n)
    · simp
    · rw [mul_div_cancel_right₀ _ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)]
      exact inf_le_of_right_le (hl _)
  )
  have h₂ : Filter.Tendsto fn .atTop (nhds hf.lim) := by
    refine h₁.congr' ?_
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  exact h₂.liminf_eq.symm
