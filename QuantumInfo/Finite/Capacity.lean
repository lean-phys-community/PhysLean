/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

public import QuantumInfo.Finite.Entropy
public import QuantumInfo.Finite.CPTPMap
public import QuantumInfo.Finite.Distance


/-! # Quantum Capacity

This focuses on defining and proving theorems about the quantum capacity, the maximum asymptotic rate at which quantum information can be coherently transmitted. The precise definition is not consistent in the literature, see [Capacity_doc](./QuantumInfo/Finite/Capacity_doc.html) for a note on what has been used and how that was used to arrive at the following definition:

 1. A channel A `Emulates` another channel B if there are D and E such that D∘A∘E = B.
 2. A channel A `εApproximates` channel B (of the same dimensions) if the for every state ρ, the fidelity F(A(ρ), B(ρ)) is at least 1-ε.
 3. A channel A `AchievesRate` R:ℝ if for every ε>0, n copies of A emulates some channel B such that log2(dimout(B))/n ≥ R, and that B is εApproximately the identity.
 4. The `quantumCapacity` of the channel A is the supremum of the achievable rates, i.e. `sSup { R : ℝ | AchievesRate A R }`.

The most basic facts:
 * `emulates_self`: Every channel emulates itself.
 * `emulates_trans`: If A emulates B and B emulates C, then A emulates C. (That is, emulation is an ordering.)
 * `εApproximates A B ε` is equivalent to the existence of some δ (depending ε and dims(A)) so that |A-B| has diamond norm at most δ, and δ→0 as ε→0.
 * `achievesRate_0`: Every channel achievesRate 0. So, the set of achievable rates is Nonempty.
 * If a channel achievesRate R₁, it also every achievesRate R₂ every R₂ ≤ R₁, i.e. it is an interval extending left towards -∞. Achievable rates are `¬BddBelow`.
 * `bddAbove_achievesRate`: A channel C : dimX → dimY cannot achievesRate R with `R > log2(min(dimX, dimY))`. Thus, the interval is `BddAbove`.

The nice lemmas we would want:
 * Capacity of a replacement channel is zero.
 * Capacity of an identity channel is `log2(D)`.
 * Capacity is superadditive under tensor products. (That is, at least additive. Showing that it isn't _exactly_ additive, unlike classical capacity which is additive, is a much harder task.)
 * Capacity of a kth tensor power is exactly k times the capacity of the original channel.
 * Capacity does not decrease under tensor sums.
 * Capacity does not increase under composition.

Then, we should show that our definition is equivalent to some above. Most, except (3), should be not too hard to prove.

Then the LSD theorem establishes that the single-copy coherent information is a lower bound. This is stated in `coherentInfo_le_quantumCapacity`. The corollary, that the n-copy coherent information converges to the capacity, is `quantumCapacity_eq_piProd_coherentInfo`.

# TODO

The only notion of "capacity" here currently is "quantum capacity" in the usual sense. But there are several non-equal capacities relevant to quantum channels, see e.g. [Watrous's notes](https://cs.uwaterloo.ca/~watrous/TQI/TQI.8.pdf) for a list:
 * Quantum capacity (`quantumCapacity`)
 * Quantum 1-shot capacity
 * Entanglement-assisted classical capacity
 * Qss, the quantum side-channel capacity
 * Holevo capacity, aka Holevo χ. The Holevo–Schumacher–Westmoreland theorem as a major theorem
 * Entanglement-assisted Holevo capacity
 * Entanglement-assisted quantum capacity
 * One- and two-way distillable entanglement

And other important theorems like superdense coding, nonadditivity, superactivation
-/

@[expose] public section

namespace CPTPMap

variable {d₁ d₂ d₃ d₄ d₅ d₆ : Type*}
variable [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype d₄] [Fintype d₅] [Fintype d₆] [DecidableEq d₁] [DecidableEq d₂]

variable [DecidableEq d₃] [DecidableEq d₄] in
/--
A channel Λ₁ `Emulates` another channel Λ₂ if there are D and E such that D∘Λ₁∘E = Λ₂.
-/
def Emulates (Λ₁ : CPTPMap d₁ d₂) (Λ₂ : CPTPMap d₃ d₄) : Prop :=
  ∃ (E : CPTPMap d₃ d₁) (D : CPTPMap d₂ d₄), D.compose (Λ₁.compose E) = Λ₂

/--
A channel A `εApproximates` channel B of the same dimensions if the for every state ρ, the fidelity F(A(ρ), B(ρ)) is at least 1-ε.
-/
def εApproximates (A B : CPTPMap d₁ d₂) (ε : ℝ) : Prop :=
  ∀ (ρ : MState d₁), (A ρ).fidelity (B ρ) ≥ 1-ε

/--
A channel A `AchievesRate` R:ℝ if for every ε>0, some n copies of A emulates a channel B such that log2(dimout(B))/n ≥ R, and that B εApproximates the identity channel.
-/
def AchievesRate (A : CPTPMap d₁ d₂) (R : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ n > 0, ∃ (dimB : ℕ) (B : CPTPMap (Fin dimB) (Fin dimB)),
      (CPTPMap.piProd (fun (_ : Fin n) ↦ A)).Emulates B ∧
      Real.logb 2 dimB ≥ R*n ∧
      B.εApproximates CPTPMap.id ε

noncomputable def quantumCapacity (A : CPTPMap d₁ d₂) : ℝ :=
  sSup { R : ℝ | AchievesRate A R }

section emulates
variable [DecidableEq d₃] [DecidableEq d₄] [DecidableEq d₅]

/-- Every quantum channel emulates itself. -/
@[refl]
theorem emulates_self (Λ : CPTPMap d₁ d₂) : Λ.Emulates Λ :=
  ⟨CPTPMap.id, CPTPMap.id, by simp⟩

/-- If a quantum channel A emulates B, and B emulates C, then A emulates C. -/
@[trans]
theorem emulates_trans (Λ₁ : CPTPMap d₁ d₂) (Λ₂ : CPTPMap d₃ d₄) (Λ₃ : CPTPMap d₅ d₆)
  (h₁₂ : Λ₁.Emulates Λ₂) (h₂₃ : Λ₂.Emulates Λ₃) : Λ₁.Emulates Λ₃ := by
  obtain ⟨E₁, D₁, hED₁⟩ := h₁₂
  obtain ⟨E₂, D₂, hED₂⟩ := h₂₃
  exact ⟨E₁.compose E₂, D₂.compose D₁, by classical simp [← hED₁, ← hED₂, compose_assoc]⟩

end emulates

section εApproximates

/-- Every quantum channel perfectly approximates itself, that is, `εApproximates` with `ε = 0`. -/
theorem εApproximates_self (Λ : CPTPMap d₁ d₂) : Λ.εApproximates Λ 0 :=
  fun ρ ↦ ((Λ ρ).fidelity_self_eq_one.trans (sub_zero 1).symm).ge

/-- If a quantum channel A approximates B with ε₀, it also approximates B with all larger ε₁. -/
theorem εApproximates_monotone {A B : CPTPMap d₁ d₂} {ε₀ : ℝ} (h : A.εApproximates B ε₀)
    {ε₁ : ℝ} (h₂ : ε₀ ≤ ε₁) : A.εApproximates B ε₁ :=
  fun ρ ↦ (tsub_le_tsub_left h₂ 1).trans (h ρ)

end εApproximates

section AchievesRate

/-- Every quantum channel achieves a rate of zero. -/
theorem achievesRate_0 (Λ : CPTPMap d₁ d₂) : Λ.AchievesRate 0 := by
  intro ε hε
  use 1, zero_lt_one, 1, default
  constructor
  · have : Nonempty d₁ := by sorry--having a CPTPMap should be enough to conclude in- and out-spaces are nonempty
    have : Nonempty d₂ := by sorry
    use Classical.ofNonempty, Classical.ofNonempty
    sorry--exact Unique.eq_default _
  constructor
  · norm_num
  · rw [Unique.eq_default id]
    sorry--apply εApproximates_monotone (εApproximates_self default) hε.le

/-- The identity channel on D dimensional space achieves a rate of log2(D). -/
theorem id_achievesRate_log_dim : (id (dIn := d₁)).AchievesRate (Real.logb 2 (Fintype.card d₁)) := by
  intro ε hε
  use 1, zero_lt_one, Fintype.card d₁, id
  constructor
  · --they are equivalent up to permutation
    -- TODO: Instead this proof should be `@[simp] piProd (fun x => id) = id` and `emulates_self`
    refine' ⟨ _, _, _ ⟩;
    exact CPTPMap.ofEquiv ( Fintype.equivFinOfCardEq ( by simp +decide ) ).symm;
    exact CPTPMap.ofEquiv ( Fintype.equivFinOfCardEq ( by simp +decide ) );
    apply CPTPMap.ext;
    ext; simp +decide [ CPTPMap.piProd ];
    unfold MatrixMap.piProd
    simp_all only [gt_iff_lt, PiTensorProduct.map_id, LinearMap.toMatrix_id_eq_basis_toMatrix,
      Module.Basis.toMatrix_self, Matrix.reindex_apply, Matrix.submatrix_one_equiv, Matrix.toLin_one]
    erw [ MatrixMap.submatrix_apply ]
    simp_all only [Equiv.symm_symm, Equiv.apply_symm_apply, Matrix.submatrix_apply]
  constructor
  · norm_num
  · exact εApproximates_monotone (εApproximates_self id) hε.le

/-- A channel cannot achieve a rate greater than log2(D), where D is the input dimension. -/
theorem not_achievesRate_gt_log_dim_in (Λ : CPTPMap d₁ d₂) {R : ℝ} (hR : Real.logb 2 (Fintype.card d₁) < R) :
    ¬Λ.AchievesRate R := by
  sorry

noncomputable section AristotleLemmas

end AristotleLemmas

/-- A channel cannot achieve a rate greater than log2(D), where D is the output dimension. -/
theorem not_achievesRate_gt_log_dim_out (Λ : CPTPMap d₁ d₂) {R : ℝ} (hR : Real.logb 2 (Fintype.card d₂) < R): ¬Λ.AchievesRate R := by
  intro h;
  -- We show that the identity channel on the output space `d₂` emulates `Λ`. Since capacity is monotonic under emulation, `Q(Λ) ≤ Q(id_{d₂})`.
  have h_emulate : (CPTPMap.id (dIn := d₂)).Emulates Λ := by
    exact ⟨Λ, CPTPMap.id, by simp⟩
  -- If `Λ` achieves rate `R`, then `id_{d₂}` achieves rate `R`. This follows because if `Λ^{\otimes n}` emulates `B`, and `id^{\otimes n}` emulates `Λ^{\otimes n}` (by functoriality of tensor product), then `id^{\otimes n}` emulates `B`.
  have h_id_achieves : (CPTPMap.id (dIn := d₂)).AchievesRate R := by
    intro ε hε_pos
    obtain ⟨n, hn, dimB, B, hB_emulate, hB_rate, hB_approx⟩ := h ε hε_pos
    have h_id_emulate : (CPTPMap.piProd (fun (_ : Fin n) => CPTPMap.id (dIn := d₂))).Emulates B := by
      -- Since `id_{d₂}` emulates `Λ`, we can use the fact that the tensor product of emulations is an emulation.
      have h_tensor_emulate : ∀ (n : ℕ), (CPTPMap.piProd (fun (_ : Fin n) => CPTPMap.id (dIn := d₂))).Emulates (CPTPMap.piProd (fun (_ : Fin n) => Λ)) := by
        intro n
        obtain ⟨E, D, hD⟩ := h_emulate
        use CPTPMap.piProd (fun (_ : Fin n) => E), CPTPMap.piProd (fun (_ : Fin n) => D);
        simp [ ← hD, ← CPTPMap.piProd_comp];
      exact emulates_trans _ _ _ ( h_tensor_emulate n ) hB_emulate;
    exact ⟨ n, hn, dimB, B, h_id_emulate, hB_rate, hB_approx ⟩;
  refine not_le_of_gt hR <| not_lt.mp fun h => ?_
  exact not_lt_of_ge ( le_of_not_gt fun h' => not_achievesRate_gt_log_dim_in _ h' h_id_achieves ) h

/-- The achievable rates are a bounded set. -/
theorem bddAbove_achievesRate (Λ : CPTPMap d₁ d₂) : BddAbove {R | Λ.AchievesRate R} := by
  use Real.logb 2 (Fintype.card d₁)
  intro R h
  contrapose h
  exact not_achievesRate_gt_log_dim_in Λ (lt_of_not_ge h)

end AchievesRate

section capacity

/-- Quantum channel capacity is nonnegative. -/
theorem zero_le_quantumCapacity (Λ : CPTPMap d₁ d₂) : 0 ≤ Λ.quantumCapacity :=
  le_csSup (bddAbove_achievesRate Λ) (achievesRate_0 Λ)

/-- Quantum channel capacity is at most log2(D), where D is the input dimension. -/
theorem quantumCapacity_ge_log_dim_in (Λ : CPTPMap d₁ d₂) : Λ.quantumCapacity ≤ Real.logb 2 (Fintype.card d₁) :=
  Real.sSup_le (by
    intro R h
    contrapose h
    exact not_achievesRate_gt_log_dim_in Λ (lt_of_not_ge h))
  (by
    by_cases h : Nonempty d₁
    · apply Real.logb_nonneg one_lt_two (Nat.one_le_cast.mpr Fintype.card_pos)
    · simp [not_nonempty_iff.mp h])

/-- The LSD (Lloyd-Shor-Devetak) theorem: the quantum capacity is at least as large the single-copy coherent
information. The "coherent information" is used in literature to refer to both a function of state and
a channel (`coherentInfo`), or a function of just a channel. In the latter case, the state is implicitly
maximized over. Here we use the former definition and state that the lower bound is true for all states. -/
theorem coherentInfo_le_quantumCapacity (Λ : CPTPMap d₁ d₂) (ρ : MState d₁) : coherentInfo ρ Λ ≤ Λ.quantumCapacity := by
  sorry

/-- The quantum capacity is the limit of the coherent information of n-copy uses of the channel. -/
theorem quantumCapacity_eq_piProd_coherentInfo (Λ : CPTPMap d₁ d₂) : Λ.quantumCapacity =
    sSup { r : ℝ | ∃ n ρ, r = coherentInfo ρ (CPTPMap.piProd (fun (_ : Fin n) ↦ Λ))} := by
  sorry

end capacity
