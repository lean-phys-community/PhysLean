/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/
module

public import QuantumInfo.ForMathlib.ContinuousLinearMap
public import QuantumInfo.ForMathlib.ComplexLaplaceTransform
public import QuantumInfo.ForMathlib.ContinuousSup
public import QuantumInfo.ForMathlib.Filter
public import QuantumInfo.ForMathlib.HermitianMat
public import QuantumInfo.ForMathlib.Isometry
public import QuantumInfo.ForMathlib.LinearEquiv
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.Minimax
public import QuantumInfo.ForMathlib.Misc
public import QuantumInfo.ForMathlib.Unitary
public import QuantumInfo.ClassicalInfo.Distribution
public import QuantumInfo.States.Pure.Braket

public import Mathlib.Logic.Equiv.Basic

/-!
Finite dimensional quantum mixed states, ρ.

The same comments apply as in `Braket`:

These could be done with a Hilbert space of Fintype, which would look like
```lean4
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
```
or by choosing a particular `Basis` and asserting it is `Fintype`. But frankly it seems easier to
mostly focus on the basis-dependent notion of `Matrix`, which has the added benefit of an obvious
"classical" interpretation (as the basis elements, or diagonal elements of a mixed state). In that
sense, this quantum theory comes with the a particular classical theory always preferred.

Important definitions:
 * `instMixable`: the `Mixable` instance allowing convex combinations of `MState`s
 * `ofClassical`: Mixed states representing classical distributions
 * `purity`: The purity `Tr[ρ^2]` of a state
 * `spectrum`: The spectrum of the matrix
 * `uniform`: The maximally mixed state
 * `mix`: The total state corresponding to an ensemble
 * `average`: Averages a function over an ensemble, with appropriate weights
-/

@[expose] public section

noncomputable section

open BigOperators
open ComplexConjugate
open HermitianMat
open scoped Matrix ComplexOrder

/-- A **mixed quantum state** is a PSD matrix with trace 1.

We don't `extend (M : HermitianMat d ℂ)` because that gives an annoying thing where
`M` is actually a `Subtype`, which means `ρ.M.foo` notation doesn't work. -/
@[ext]
structure MState (d : Type*) [Fintype d] [DecidableEq d] where
  M : HermitianMat d ℂ
  nonneg : 0 ≤ M
  tr : M.trace = 1

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

variable (ψ φ : Ket d)
variable (ρ σ : MState d)

namespace MState

attribute [coe] MState.M
instance instCoe : Coe (MState d) (HermitianMat d ℂ) := ⟨MState.M⟩

attribute [simp] MState.tr

/-- The underlying `Matrix` in an MState. Prefer `MState.M` for the `HermitianMat`. -/
def m (ρ : MState d) : Matrix d d ℂ := ρ.M.mat

@[simp]
theorem mat_M : ρ.M.mat = ρ.m := by
  rfl

theorem pos (ρ : MState d) : 0 < ρ.M :=
  ρ.nonneg.lt_of_ne' fun h ↦ by simpa [h] using ρ.tr

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `MState.M`: it is always positive (`0 < ρ.M`).
Note: we must not call `whnfR` on `e` because `MState.M` is a structure
projection (reducible), so `whnfR` would reduce it and destroy the pattern. -/
@[positivity MState.M _]
meta def evalMStateM : PositivityExt where eval {_u _α} _zα _pα e := do
  let ρ := e.appArg!
  pure (.positive (← mkAppM ``MState.pos #[ρ]))

--TODO: There should be a bunch of places where we can use `positivity` to prove things,
-- that are currently proved manually.
example (ρ : MState d) : 0 < ρ.M := by positivity

--XXX These are methods that directly reference the matrix, "m" or ".val".
-- We'd like to remove these (where possible) so that mostly go through HermitianMat
-- where possible.
theorem psd : ρ.m.PosSemidef :=
  HermitianMat.zero_le_iff.mp ρ.nonneg


/-- Every mixed state is Hermitian. -/
theorem Hermitian : ρ.m.IsHermitian :=
  ρ.M.H

@[simp]
theorem tr' : ρ.m.trace = 1 := by
  rw [MState.m.eq_def, ← HermitianMat.trace_eq_trace_rc, ρ.tr, RCLike.ofReal_one]

theorem ext_m {ρ₁ ρ₂ : MState d} (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ :=
  MState.ext (HermitianMat.ext h)

/-- The map from mixed states to their matrices is injective -/
theorem m_inj : (MState.m (d := d)).Injective :=
  fun _ _ h ↦ ext_m h

theorem M_Injective : Function.Injective (MState.M (d := d)) :=
  fun _ _ ↦ MState.ext

variable (d) in
/-- The matrices corresponding to MStates are `Convex ℝ` -/
theorem convex : Convex ℝ (Set.range (MState.M (d := d))) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb hab
  exact ⟨⟨_, HermitianMat.convex_cone x.nonneg y.nonneg ha hb, by simp [hab]⟩, rfl⟩

instance instMixable : Mixable (HermitianMat d ℂ) (MState d) where
  to_U := MState.M
  to_U_inj := MState.ext
  mkT {u} := fun h ↦
    ⟨⟨u, h.casesOn fun t ht ↦ ht ▸ t.nonneg,
      h.casesOn fun t ht ↦ ht ▸ t.tr⟩, rfl⟩
  convex := convex d

/-- An MState is a witness that d is nonempty. -/
@[implicit_reducible]
def nonempty : Nonempty d := by
  by_contra h
  simpa [HermitianMat.trace_eq_re_trace, not_nonempty_iff.mp h] using ρ.tr

-- Could have used properties of ρ.spectrum
theorem eigenvalue_nonneg : ∀ i, 0 ≤ ρ.Hermitian.eigenvalues i :=
  fun i => ρ.psd.eigenvalues_nonneg i

set_option backward.isDefEq.respectTransparency false in
-- Could have used properties of ρ.spectrum
theorem eigenvalue_le_one : ∀ i, ρ.Hermitian.eigenvalues i ≤ 1 := by
  intro i
  convert! Finset.single_le_sum (fun y _ ↦ ρ.psd.eigenvalues_nonneg y) (Finset.mem_univ i)
  rw [ρ.M.sum_eigenvalues_eq_trace, ρ.tr]

theorem le_one : ρ.M ≤ 1 := by
  open MatrixOrder in
  have h := (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff ρ.Hermitian 1).mp
    ρ.eigenvalue_le_one
  rwa [one_smul] at h

open scoped RealInnerProductSpace InnerProductSpace

/-- The inner product of two MState's, as a real number between 0 and 1. -/
scoped instance : Inner Prob (MState d) where
  inner := fun ρ σ ↦ ⟨⟪ρ.M, σ.M⟫,
    inner_ge_zero ρ.nonneg σ.nonneg,
    (inner_le_mul_trace ρ.nonneg σ.nonneg).trans (by simp)⟩

theorem inner_def : ⟪ρ, σ⟫_Prob = ⟨⟪ρ.M, σ.M⟫,
    inner_ge_zero ρ.nonneg σ.nonneg,
    (inner_le_mul_trace ρ.nonneg σ.nonneg).trans (by simp)⟩ := by
  rfl

theorem val_inner : (⟪ρ, σ⟫_Prob : ℝ) = ⟪ρ.M, σ.M⟫ := by
  rfl

section exp_val

def exp_val_ℂ (T : Matrix d d ℂ) : ℂ :=
  (T * ρ.m).trace

--TODO: Bundle as a ContinuousLinearMap.
/-- The **expectation value** of an operator on a quantum state. -/
def exp_val (T : HermitianMat d ℂ) : ℝ :=
  ⟪ρ.M, T⟫

theorem exp_val_nonneg {T : HermitianMat d ℂ} (h : 0 ≤ T) : 0 ≤ ρ.exp_val T :=
  inner_ge_zero ρ.nonneg h

--TODO: Positivity extension for `MState.exp_val`. (Use the `inner` extension that we need
-- to write first.)

@[simp]
theorem exp_val_zero : ρ.exp_val 0 = 0 := by
  simp [MState.exp_val]

@[simp]
theorem exp_val_one : ρ.exp_val 1 = 1 := by
  simp [MState.exp_val]

theorem exp_val_le_one {T : HermitianMat d ℂ} (h : T ≤ 1) : ρ.exp_val T ≤ 1 := by
  simpa [exp_val, inner_one] using inner_mono ρ.nonneg h

theorem exp_val_prob {T : HermitianMat d ℂ} (h : 0 ≤ T ∧ T ≤ 1) :
    0 ≤ ρ.exp_val T ∧ ρ.exp_val T ≤ 1 :=
  ⟨ρ.exp_val_nonneg h.1, ρ.exp_val_le_one h.2⟩

theorem exp_val_sub (A B : HermitianMat d ℂ) :
    ρ.exp_val (A - B) = ρ.exp_val A - ρ.exp_val B := by
  simp [exp_val, inner_sub_right]

/-- If a PSD observable `A` has expectation value of 0 on a state `ρ`, it must entirely contain the
support of `ρ` in its kernel. -/
theorem exp_val_eq_zero_iff {A : HermitianMat d ℂ} (hA₁ : 0 ≤ A) :
    ρ.exp_val A = 0 ↔ ρ.M.support ≤ A.ker :=
  inner_zero_iff ρ.nonneg hA₁

/-- If an observable `A` has expectation value of 1 on a state `ρ`, it must entirely contain the
support of `ρ` in its 1-eigenspace. -/
theorem exp_val_eq_one_iff {A : HermitianMat d ℂ} (hA₂ : A ≤ 1) :
    ρ.exp_val A = 1 ↔ ρ.M.support ≤ (1 - A).ker := by
  rw [← exp_val_eq_zero_iff ρ (A := 1 - A) (HermitianMat.zero_le_iff.mpr hA₂), exp_val_sub,
    exp_val_one, sub_eq_zero, eq_comm]

theorem exp_val_add (A B : HermitianMat d ℂ) :
    ρ.exp_val (A + B) = ρ.exp_val A + ρ.exp_val B := by
  simp [exp_val, inner_add_right]

@[simp]
theorem exp_val_smul (r : ℝ) (A : HermitianMat d ℂ) :
    ρ.exp_val (r • A) = r * ρ.exp_val A := by
  simp [MState.exp_val]

@[gcongr]
theorem exp_val_le_exp_val (ρ : MState d) {A B : HermitianMat d ℂ} (h : A ≤ B) :
    ρ.exp_val A ≤ ρ.exp_val B :=
  inner_mono ρ.nonneg h

end exp_val

section pure

/-- A mixed state can be constructed as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  M := {
    val := Matrix.vecMulVec ψ (ψ : Bra d)
    property := (Matrix.PosSemidef.outer_self_conj ψ).1
  }
  nonneg := HermitianMat.zero_le_iff.mpr (.outer_self_conj ψ)
  tr := by
    simpa [HermitianMat.trace_eq_re_trace, Matrix.trace, Matrix.vecMulVec_apply, Bra.eq_conj,
      ← Complex.normSq_eq_conj_mul_self, mul_comm (ψ _)] using ψ.normalized

theorem pure_inner : ⟪pure ψ, pure φ⟫_Prob = ‖Braket.dot ψ φ‖^2 := by
  simp [MState.inner_def, HermitianMat.inner_def, pure, Matrix.vecMulVec_mul_vecMulVec,
    Braket.dot_eq_dotProduct, Matrix.trace_smul]
  rw [show (ψ : d → ℂ) ⬝ᵥ ((φ : Bra d) : d → ℂ) = conj (((ψ : Bra d) : d → ℂ) ⬝ᵥ (φ : d → ℂ))
    from (dotProduct_comm _ _).trans
      (by simpa [Braket.dot_eq_dotProduct] using Braket.dot_swap_conj ψ φ)]
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

@[simp]
theorem pure_apply {i j : d} : (pure ψ).m i j = (ψ i) * conj (ψ j) := by
  rfl

theorem pure_mul_self : (pure ψ).m * (pure ψ).m = (pure ψ : Matrix d d ℂ) := by
  dsimp [pure, MState.m]
  simp [Matrix.vecMulVec_mul_vecMulVec, ← Braket.dot_eq_dotProduct]

/-- The purity of a state is Tr[ρ^2]. This is a `Prob`, because it is always
between zero and one. -/
def purity (ρ : MState d) : Prob := ⟪ρ, ρ⟫_Prob

/-- The eigenvalue spectrum of a mixed quantum state, as a `Distribution`. -/
def spectrum (ρ : MState d) : ProbDistribution d :=
  ProbDistribution.mk'
    (ρ.M.H.eigenvalues ·)
    (ρ.psd.eigenvalues_nonneg ·)
    (by rw [sum_eigenvalues_eq_trace, ρ.tr])

/-- The spectrum of a pure state is (1,0,0,...), i.e. a constant distribution. -/
theorem spectrum_pure_eq_constant :
    ∃ i, (pure ψ).spectrum = ProbDistribution.constant i := by
  obtain ⟨i, hi⟩ : ∃ i, (pure ψ).M.H.eigenvalues i = 1 := by
    have hv : (pure ψ).m *ᵥ (ψ : d → ℂ) = ψ := by
      ext i
      simp [Matrix.mulVec, dotProduct, pure_apply, mul_assoc, ← Finset.mul_sum,
        ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum, ψ.normalized]
    rw [← Set.mem_range, ← (pure ψ).M.H.spectrum_real_eq_range_eigenvalues, spectrum.mem_iff]
    obtain ⟨j, hj⟩ := ψ.exists_ne_zero
    intro h
    rw [map_one, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at h
    refine hj (congrFun (Matrix.eq_zero_of_mulVec_eq_zero h ?_) j)
    simp [Matrix.sub_mulVec, hv]
  exact ⟨i, ProbDistribution.constant_of_exists_one (Subtype.ext hi)⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the spectrum of a mixed state is (1,0,0...) i.e. a constant distribution, it is
 a pure state. -/
theorem pure_of_constant_spectrum (h : ∃ i, ρ.spectrum = ProbDistribution.constant i) :
    ∃ ψ, ρ = pure ψ := by
  obtain ⟨i, h'⟩ := h
  -- Translate assumption to eigenvalues being (1,0,0,...)
  have hEig : ρ.M.H.eigenvalues = fun x => if x = i then 1 else 0 := by
    ext x
    simpa [spectrum, ProbDistribution.mk', ProbDistribution.constant, Prob.ext_iff, eq_comm,
      apply_ite] using congrFun (congrArg DFunLike.coe h') x
  -- The eigenvector v of ρ with eigenvalue 1 makes a normalized ψ with ρ = pure ψ
  have hUvNorm : ∑ x, ‖ρ.M.H.eigenvectorBasis i x‖ ^ 2 = 1 := by
    have h1 := ρ.M.H.eigenvectorBasis.orthonormal.1 i
    rwa [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
  refine ⟨⟨ρ.M.H.eigenvectorBasis i, hUvNorm⟩, ?_⟩
  ext j k
  conv_lhs => rw [ρ.M.H.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp [Matrix.mul_apply, hEig, Matrix.diagonal, apply_ite, ite_mul, Finset.sum_ite_eq']
  rfl

/-- A state ρ is pure iff its spectrum is (1,0,0,...) i.e. a constant distribution. -/
theorem pure_iff_constant_spectrum : (∃ ψ, ρ = pure ψ) ↔
    ∃ i, ρ.spectrum = ProbDistribution.constant i :=
  ⟨fun h ↦ h.rec fun ψ h₂ ↦ h₂ ▸ spectrum_pure_eq_constant ψ,
  pure_of_constant_spectrum ρ⟩

set_option backward.isDefEq.respectTransparency false in
theorem pure_iff_purity_one : (∃ ψ, ρ = pure ψ) ↔ ρ.purity = 1 := by
  --purity = exp(-Collision entropy)
  --purity eq 1 iff collision entropy is zero
  --entropy is zero iff distribution is constant
  --distribution is constant iff pure
  constructor <;> intro h
  · obtain ⟨w, rfl⟩ := h
    exact Prob.ext (by simp [purity, pure_inner, Braket.dot_self_eq_one])
  · -- A state is pure iff its spectrum is constant.
    apply (pure_iff_constant_spectrum ρ).mpr
    have h_eigenvalues : ∑ i, (ρ.spectrum i).val ^ 2 = 1 := by
      have key : ∑ i, (ρ.M.H.eigenvalues i) ^ 2 = (ρ.M.mat * ρ.M.mat).trace := by
        conv_rhs => rw [ρ.M.H.spectral_theorem]
        simp [Matrix.trace_mul_comm, Matrix.mul_assoc]
        exact Finset.sum_congr rfl fun _ _ => by ring
      convert! congr_arg Complex.re key using 1
      exact ((HermitianMat.inner_eq_re_trace ρ.M ρ.M).symm.trans (congrArg Subtype.val h)).symm
    -- Each eigenvalue satisfies `λᵢ (1 - λᵢ) ≥ 0`, and these terms sum to
    -- `∑ λᵢ - ∑ λᵢ² = 1 - 1 = 0`, so every `λᵢ` is `0`, as none is `1`.
    obtain ⟨i, hi⟩ : ∃ i, (ρ.spectrum i).val = 1 := by
      by_contra hcon
      push Not at hcon
      have hz : ∑ i, (ρ.spectrum i).val * (1 - (ρ.spectrum i).val) = 0 := by
        simp only [mul_one_sub, ← sq, Finset.sum_sub_distrib, h_eigenvalues,
          ρ.spectrum.normalized, sub_self]
      have hz0 : ∀ i, (ρ.spectrum i).val = 0 := fun i =>
        (mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg
          (ρ.spectrum j).2.1 (by linarith [(ρ.spectrum j).2.2])).mp hz i
          (Finset.mem_univ i))).resolve_right fun h => hcon i (by linarith)
      simpa [hz0] using ρ.spectrum.normalized
    exact ⟨i, ProbDistribution.constant_of_exists_one (Subtype.ext hi)⟩

set_option backward.isDefEq.respectTransparency false in
--TODO: Would be better if there was an `MState.eigenstate` or similar (maybe extending
-- a similar thing for `HermitianMat`) and then this could be an equality with that, as
-- an explicit formula, instead of this `Exists`.
theorem spectralDecomposition (ρ : MState d) :
    ∃ (ψs : d → Ket d), ρ.M = ∑ i, (ρ.spectrum i : ℝ) • (MState.pure (ψs i)).M := by
  use (fun i ↦ ⟨(ρ.M.H.eigenvectorUnitary · i), Matrix.unitaryGroup_row_norm _ i⟩)
  ext i j
  nth_rw 1 [ρ.M.H.spectral_theorem]
  --TODO Cleanup
  simp only [Complex.coe_algebraMap, spectrum, ProbDistribution.mk',
    ProbDistribution.funlike_apply, pure, Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [HermitianMat.mat_finset_sum]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Finset.sum_apply, Finset.sum_apply, Matrix.mul_apply]
  congr!
  simp only [Matrix.mul_diagonal, Matrix.IsHermitian.eigenvectorUnitary_apply,
    mul_comm, Matrix.star_apply, RCLike.star_def]
  simp only [Function.comp_apply, mat_M, mat_apply, HermitianMat.smul_apply, Complex.real_smul]
  rw [mul_assoc]
  rfl

end pure

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  M := ρ₁.M ⊗ₖ ρ₂.M
  nonneg := HermitianMat.zero_le_iff.mpr (ρ₁.psd.PosSemidef_kronecker ρ₂.psd)
  tr := by simp

infixl:100 " ⊗ᴹ " => MState.prod

theorem prod_inner_prod (ξ1 ψ1 : MState d₁) (ξ2 ψ2 : MState d₂) :
    ⟪ξ1 ⊗ᴹ ξ2, ψ1 ⊗ᴹ ψ2⟫_Prob = ⟪ξ1, ψ1⟫_Prob * ⟪ξ2, ψ2⟫_Prob := by
  ext1
  simp only [inner_def, Prob.coe_mul, ← Complex.ofReal_inj]
  --Lots of this should actually be facts about HermitianMat first
  simp only [prod, Complex.ofReal_mul]
  simp only [← RCLike.ofReal_eq_complex_ofReal, inner_eq_trace_rc]
  simp only [kronecker, ← Matrix.trace_kronecker]
  simp only [mat_M, mat_mk, Matrix.mul_kronecker_mul]

/-- The product of pure states is a pure product state , `Ket.prod`. -/
theorem pure_prod_pure (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : pure (ψ₁ ⊗ᵠ ψ₂) = (pure ψ₁) ⊗ᴹ (pure ψ₂) := by
  ext : 3
  simp [Ket.prod, Ket.apply, prod, -mat_apply]
  ac_rfl

end prod

/-- A representation of a classical distribution as a quantum state, diagonal in the given basis. -/
def ofClassical (dist : ProbDistribution d) : MState d where
  M := diagonal ℂ (fun x ↦ dist x)
  nonneg := by simp [zero_le_iff, diagonal, Matrix.posSemidef_diagonal_iff]
  tr := by simp [trace_diagonal]

@[simp]
theorem coe_ofClassical (dist : ProbDistribution d) :
    (ofClassical dist).M = diagonal ℂ (dist ·) := by
  rfl

theorem ofClassical_pow (dist : ProbDistribution d) (p : ℝ) :
    (ofClassical dist).M ^ p = diagonal ℂ (fun i ↦ (dist i) ^ p) := by
  rw [coe_ofClassical, diagonal_pow]

/-- The maximally mixed state. -/
def uniform [Nonempty d] : MState d :=
  ofClassical ProbDistribution.uniform

/-- There is exactly one state on a dimension-1 system. -/
--note that this still takes (and uses) the `Fintype d` and `DecidableEq d` instances on `MState d`.
--Even though instances for those can be derived from `Unique d`, we want this `Unique` instance to
--apply on `@MState d ?x ?y` for _any_ x and y.
instance instUnique [Unique d] : Unique (MState d) where
  default := @uniform _ _ _ _
  uniq := by
    intro ρ
    ext
    have h₁ := ρ.tr
    have h₂ := (@uniform _ _ _ _ : MState d).tr
    simp [Matrix.trace, Unique.eq_default, -MState.tr, HermitianMat.trace_eq_re_trace] at h₁ h₂ ⊢
    apply Complex.ext
    · exact h₁.trans h₂.symm
    · rw [complex_im_eq_zero, complex_im_eq_zero]

/-- There exists a mixed state for every nonempty `d`.
Here, the maximally mixed one is chosen. -/
instance instInhabited [Nonempty d] : Inhabited (MState d) where
  default := uniform

lemma default_eq [Nonempty d] : (default : MState d) = uniform := rfl

@[simp]
theorem M_default [Unique d] : (default : MState d).M = 1 := by
  simp [default_eq, uniform]
  rfl

section ptrace

/-- Partial tracing out the left half of a system. -/
@[simps]
def traceLeft (ρ : MState (d₁ × d₂)) : MState d₂ where
  M := ρ.M.traceLeft
  nonneg := zero_le_iff.mpr ρ.psd.traceLeft
  tr := by simp [trace]

/-- Partial tracing out the right half of a system. -/
@[simps]
def traceRight (ρ : MState (d₁ × d₂)) : MState d₁ where
  M := ρ.M.traceRight
  nonneg := zero_le_iff.mpr ρ.psd.traceRight
  tr := by simp [trace]

/-- Taking the direct product on the left and tracing it back out gives the same state. -/
@[simp]
theorem traceLeft_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).traceLeft = ρ₂ := by
  ext1
  simp [prod]

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
@[simp]
theorem traceRight_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).traceRight = ρ₁ := by
  ext1
  simp [prod]

end ptrace

-- TODO: direct sum (by zero-padding)

--TODO: Spectra of left- and right- partial traces of a pure state are equal.

/-- Spectrum of direct product. There is a permutation σ so that the spectrum of the direct product of
  ρ₁ and ρ₂, as permuted under σ, is the pairwise products of the spectra of ρ₁ and ρ₂. -/
theorem spectrum_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : ∃(σ : d₁ × d₂ ≃ d₁ × d₂),
    ∀i, ∀j, (ρ₁ ⊗ᴹ ρ₂).spectrum (σ (i, j)) = (ρ₁.spectrum i) * (ρ₂.spectrum j) := by
  obtain ⟨σ, hσ⟩ := (ρ₁ ⊗ᴹ ρ₂).M.H.eigenvalues_eq_of_unitary_similarity_diagonal
    (Matrix.kronecker_mem_unitary ρ₁.M.H.eigenvectorUnitary.2 ρ₂.M.H.eigenvectorUnitary.2)
    (f := fun p => ρ₁.M.H.eigenvalues p.1 * ρ₂.M.H.eigenvalues p.2) (by
      conv_lhs => rw [show (ρ₁ ⊗ᴹ ρ₂).M = ρ₁.M ⊗ₖ ρ₂.M from rfl, HermitianMat.kronecker_mat,
        ρ₁.M.H.spectral_theorem, ρ₂.M.H.spectral_theorem]
      simp [Unitary.conjStarAlgAut_apply, Matrix.mul_kronecker_mul,
        Matrix.diagonal_kronecker_diagonal, Function.comp_def]
      congr 1
      exact (Matrix.star_kron _ _).symm)
  exact ⟨σ, fun i j => Subtype.ext (congrFun hσ (i, j))⟩

theorem sInf_spectrum_prod (ρ : MState d) (σ : MState d₂) :
    sInf (_root_.spectrum ℝ (ρ ⊗ᴹ σ).m) = sInf (_root_.spectrum ℝ ρ.m) * sInf (_root_.spectrum ℝ σ.m) := by
  rcases isEmpty_or_nonempty d with _ | _; · simp
  rcases isEmpty_or_nonempty d₂ with _ | _; · simp
  rw [MState.m, MState.prod, HermitianMat.spectrum_prod, ← MState.m, ← MState.m]
  apply csInf_mul_nonneg
  · exact ContinuousFunctionalCalculus.spectrum_nonempty _ ρ.M.H
  · rw [MState.m, ρ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply ρ.eigenvalue_nonneg
  · exact ContinuousFunctionalCalculus.spectrum_nonempty _ σ.M.H
  · rw [MState.m, σ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply σ.eigenvalue_nonneg

--TODO: Spectrum of direct sum. Spectrum of partial trace?

/-- A mixed state is separable iff it can be written as a convex combination of product mixed states. -/
def IsSeparable (ρ : MState (d₁ × d₂)) : Prop :=
  ∃ ρLRs : Finset (MState d₁ × MState d₂), --Finite set of (ρL, ρR) pairs
    ∃ ps : ProbDistribution ρLRs, --ProbDistribution over those pairs, an ensemble
      ρ.M = ∑ ρLR : ρLRs, (ps ρLR : ℝ) • (Prod.fst ρLR.val).M ⊗ₖ (Prod.snd ρLR.val).M

/-- A product state `MState.prod` is separable. -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ᴹ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }, ProbDistribution.constant ⟨only, Finset.mem_singleton_self only⟩
  simp [prod, Unique.eq_default, only]

set_option backward.isDefEq.respectTransparency false in
theorem eq_of_sum_eq_pure {d : Type*} [Fintype d] [DecidableEq d]
    {ι : Type*} {s : Finset ι} {p : ι → ℝ} {ρs : ι → MState d}
    {ρ : MState d} (h_pure : ρ.purity = 1) (h_sum : ρ.M = ∑ i ∈ s, p i • (ρs i).M)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1) (i : ι) (hi : i ∈ s) (hpi : 0 < p i) :
    ρs i = ρ := by
  have h_tr_le_one : ∀ j ∈ s, ⟪ρ.M, (ρs j).M⟫ ≤ 1 := fun j hj => by
    simpa using HermitianMat.inner_le_mul_trace ρ.nonneg (ρs j).nonneg
  have h_tr_pure : ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫ = 1 := by
    calc ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫
        = ⟪ρ.M, ∑ j ∈ s, p j • (ρs j).M⟫ := by simp [inner_sum]
      _ = 1 := by rw [← h_sum]; exact congrArg Subtype.val h_pure
  have h_trace : ⟪ρ.M, (ρs i).M⟫ = 1 := by
    by_contra h_contra
    have h_lt : ∑ j ∈ s, p j • ⟪ρ.M, (ρs j).M⟫ < ∑ j ∈ s, p j :=
      Finset.sum_lt_sum (fun k hk => mul_le_of_le_one_right (hp_nonneg k hk) (h_tr_le_one k hk))
        ⟨i, hi, mul_lt_of_lt_one_right hpi ((h_tr_le_one i hi).lt_of_ne h_contra)⟩
    rw [h_tr_pure, hp_sum] at h_lt
    exact lt_irrefl 1 h_lt
  have h1 : ⟪(ρs i).M, (ρs i).M⟫ ≤ 1 := by
    simpa using HermitianMat.inner_le_mul_trace (ρs i).nonneg (ρs i).nonneg
  have h2 : ⟪ρ.M, ρ.M⟫ = 1 := congrArg Subtype.val h_pure
  have h3 := (ρ.M - (ρs i).M).inner_self_nonneg
  have h0 : ⟪ρ.M - (ρs i).M, ρ.M - (ρs i).M⟫ = 0 := by
    rw [real_inner_sub_sub_self] at h3 ⊢
    linarith
  exact MState.ext (eq_of_sub_eq_zero (inner_self_eq_zero.mp h0)).symm

theorem purity_prod {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).purity = ρ₁.purity * ρ₂.purity := by
  exact prod_inner_prod ρ₁ ρ₁ ρ₂ ρ₂

theorem pure_eq_pure_iff {d : Type*} [Fintype d] [DecidableEq d] (ψ φ : Ket d) :
    pure ψ = pure φ ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ ψ.vec = z • φ.vec := by
  constructor
  · intro h
    have h_eq : ∀ i j, ψ.vec i * conj (ψ.vec j) = φ.vec i * conj (φ.vec j) :=
      fun i j => congrArg (fun ρ => ρ.m i j) h
    obtain ⟨k, hk⟩ := φ.exists_ne_zero
    replace hk : φ.vec k ≠ 0 := hk
    have hn : ‖ψ.vec k‖ = ‖φ.vec k‖ := by
      have h1 := h_eq k k
      rw [Complex.mul_conj, Complex.mul_conj, Complex.ofReal_inj,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h1
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
    have hψk : ψ.vec k ≠ 0 := norm_ne_zero_iff.mp (hn ▸ norm_ne_zero_iff.mpr hk)
    refine ⟨ψ.vec k / φ.vec k, ?_, funext fun i => ?_⟩
    · rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hk)]
    · rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hk]
      refine mul_right_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hψk) ?_
      linear_combination φ.vec k * h_eq i k - φ.vec i * h_eq k k
  · rintro ⟨z, hz₁, hz₂⟩
    refine MState.ext_m (Matrix.ext fun i j => ?_)
    show ψ.vec i * conj (ψ.vec j) = φ.vec i * conj (φ.vec j)
    rw [hz₂]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [mul_mul_mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz₁]
    simp

/-- Two kets are phase-equivalent if and only if their pure states are equal. -/
theorem PhaseEquiv_iff_pure_eq {d : Type*} [Fintype d] [DecidableEq d] (ψ φ : Ket d) :
    Ket.PhaseEquiv.r ψ φ ↔ MState.pure ψ = MState.pure φ :=
  (pure_eq_pure_iff ψ φ).symm

/-- `MState.pure` descends to the quotient `KetUpToPhase`. -/
def pureQ {d : Type*} [Fintype d] [DecidableEq d] : KetUpToPhase d → MState d :=
  @Quotient.lift _ _ Ket.PhaseEquiv MState.pure (fun a b h => (PhaseEquiv_iff_pure_eq a b).mp h)

@[simp]
theorem pureQ_mk {d : Type*} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    pureQ (Quotient.mk Ket.PhaseEquiv ψ) = MState.pure ψ := rfl

theorem pureQ_injective {d : Type*} [Fintype d] [DecidableEq d] : Function.Injective (pureQ (d := d)) := by
  intro a b h
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact Quotient.sound ((PhaseEquiv_iff_pure_eq _ _).mpr h)

theorem pure_separable_imp_IsProd {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) (h : IsSeparable (pure ψ)) : ψ.IsProd := by
  obtain ⟨ρLRs, ps, hps⟩ := h
  have h_pure : (pure ψ).purity = 1 := (pure_iff_purity_one _).mp ⟨ψ, rfl⟩
  -- Some component `k` of the ensemble has positive weight, so `ρL_k ⊗ᴹ ρR_k = pure ψ`.
  obtain ⟨k, hk⟩ : ∃ k, 0 < (ps k : ℝ) := by
    by_contra hc
    push Not at hc
    have h1 : ∀ k, (ps k : ℝ) = 0 := fun k => le_antisymm (hc k) (ps k).2.1
    simpa [h1] using ps.normalized
  have hk2 : k.val.1 ⊗ᴹ k.val.2 = pure ψ :=
    eq_of_sum_eq_pure (p := fun x => (ps x : ℝ)) (ρs := fun x => x.val.1 ⊗ᴹ x.val.2) h_pure hps
      (fun i _ => (ps i).2.1) ps.normalized k (Finset.mem_univ k) hk
  -- Both factors have purity one, hence are pure states `pure ξ'` and `pure φ'`.
  have h_pp : k.val.1.purity * k.val.2.purity = 1 := by
    rw [← purity_prod, hk2, h_pure]
  obtain ⟨ξ', hξ'⟩ := (pure_iff_purity_one _).mpr ((Prob.mul_eq_one_iff _ _).mp h_pp).1
  obtain ⟨φ', hφ'⟩ := (pure_iff_purity_one _).mpr ((Prob.mul_eq_one_iff _ _).mp h_pp).2
  -- Since `pure ψ = pure (ξ' ⊗ᵠ φ')`, we have `ψ = ξ' ⊗ᵠ φ'` up to a global phase `z`.
  obtain ⟨z, hz₁, hz₂⟩ := (pure_eq_pure_iff ψ (ξ' ⊗ᵠ φ')).mp
    (by rw [pure_prod_pure, ← hξ', ← hφ', hk2])
  refine ⟨⟨fun i => z * ξ' i, ?_⟩, φ', ?_⟩
  · simpa [norm_mul, hz₁, Ket.apply] using ξ'.normalized'
  · ext ⟨i, j⟩
    simpa [Ket.prod, Ket.apply, mul_assoc] using congrFun hz₂ (i, j)

/-- A pure state is separable iff the ket is a product state. -/
theorem pure_separable_iff_IsProd (ψ : Ket (d₁ × d₂)) :
    IsSeparable (pure ψ) ↔ ψ.IsProd := by
  apply Iff.intro
  · exact pure_separable_imp_IsProd ψ
  · rintro ⟨ ξ, φ, rfl ⟩
    rw [pure_prod_pure ξ φ]
    exact IsSeparable_prod _ _;

/--
A mixed state is pure if and only if its rank is 1.
-/
theorem pure_iff_rank_eq_one {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    (∃ ψ, ρ = pure ψ) ↔ ρ.m.rank = 1 := by
  constructor <;> intro h
  · -- The spectrum of a pure state is constant, so exactly one eigenvalue is nonzero.
    obtain ⟨w, rfl⟩ := h
    obtain ⟨i, hs⟩ := spectrum_pure_eq_constant w
    rw [(pure w).Hermitian.rank_eq_card_non_zero_eigs, Fintype.card_eq_one_iff]
    have he : ∀ j, (pure w).Hermitian.eigenvalues j = if i = j then 1 else 0 := fun j => by
      simpa [spectrum, ProbDistribution.mk', ProbDistribution.constant_eq, apply_ite] using
        congrArg Subtype.val (congrFun (congrArg DFunLike.coe hs) j)
    exact ⟨⟨i, by simp [he]⟩, fun y =>
      Subtype.ext (not_not.mp fun hy => y.2 (by rw [he, if_neg fun h => hy h.symm]))⟩
  · -- Rank one means exactly one nonzero eigenvalue; by the trace it is `1`, so the
    -- spectrum is constant and `ρ` is pure.
    rw [ρ.Hermitian.rank_eq_card_non_zero_eigs] at h
    obtain ⟨⟨i, hi⟩, huniq⟩ := Fintype.card_eq_one_iff.mp h
    have hone : ρ.Hermitian.eigenvalues i = 1 := by
      have h2 := ρ.M.sum_eigenvalues_eq_trace
      rw [ρ.tr] at h2
      rw [← h2]
      exact (Finset.sum_eq_single i
        (fun j _ hj => not_not.mp fun hj0 => hj (congrArg Subtype.val (huniq ⟨j, hj0⟩)))
        (by simp)).symm
    exact pure_of_constant_spectrum ρ
      ⟨i, ProbDistribution.constant_of_exists_one (Subtype.ext hone)⟩

/--
A ket on a product space is a product state if and only if its coefficient matrix has rank 1.
-/
theorem Ket.IsProd_iff_rank_eq_one {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) :
    ψ.IsProd ↔ (Matrix.of (fun i j => ψ (i, j))).rank = 1 := by
  rw [Ket.IsProd_iff_mul_eq_mul]
  constructor
  · intro h
    -- The matrix factors as `vecMulVec`, so has rank at most one; it is nonzero, so exactly one.
    obtain ⟨⟨i₀, j₀⟩, hne⟩ := ψ.exists_ne_zero
    have hle : (Matrix.of fun i j => ψ (i, j)).rank ≤ 1 := by
      have hf : (Matrix.of fun i j => ψ (i, j)) =
          Matrix.vecMulVec (fun i => ψ (i, j₀) / ψ (i₀, j₀)) (fun j => ψ (i₀, j)) := by
        ext i j
        rw [Matrix.vecMulVec_apply, div_mul_eq_mul_div, eq_comm, div_eq_iff hne, Matrix.of_apply]
        linear_combination -h i i₀ j j₀
      rw [hf]
      exact Matrix.rank_vecMulVec_le _ _
    refine le_antisymm hle ?_
    have hpos : 0 < (Matrix.of fun i j => ψ (i, j)).rank := by
      rw [Matrix.rank, Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨⟨_, LinearMap.mem_range_self _ (Pi.single j₀ 1)⟩, fun h0 => hne ?_⟩
      simpa using congrFun (congrArg Subtype.val h0) i₀
    exact hpos
  · -- Rank one means all columns are multiples of one vector `v`, giving cross-multiplicativity.
    intro h i₁ i₂ j₁ j₂
    rw [Matrix.rank, finrank_eq_one_iff'] at h
    obtain ⟨v, -, hv⟩ := h
    obtain ⟨c, hc⟩ := hv ⟨_, LinearMap.mem_range_self _ (Pi.single j₁ 1)⟩
    obtain ⟨e, he⟩ := hv ⟨_, LinearMap.mem_range_self _ (Pi.single j₂ 1)⟩
    have h1 : ∀ i, ψ (i, j₁) = c * v.val i := fun i => by
      simpa using (congrFun (congrArg Subtype.val hc) i).symm
    have h2 : ∀ i, ψ (i, j₂) = e * v.val i := fun i => by
      simpa using (congrFun (congrArg Subtype.val he) i).symm
    rw [h1, h2, h1, h2]
    ring

/-- A pure state is separable iff the partial trace on the left is pure. -/
theorem pure_separable_iff_traceLeft_pure (ψ : Ket (d₁ × d₂)) : IsSeparable (pure ψ) ↔
    ∃ ψ₁, pure ψ₁ = (pure ψ).traceLeft := by
  rw [pure_separable_iff_IsProd, Ket.IsProd_iff_rank_eq_one]
  have h4 : (pure ψ).traceLeft.m.rank = (Matrix.of fun i j => ψ (i, j)).rank := by
    have h5 : (pure ψ).traceLeft.m =
        ((Matrix.of fun i j => ψ (i, j))ᴴ * Matrix.of fun i j => ψ (i, j))ᵀ := by
      ext i j
      simp [MState.traceLeft, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [h5, Matrix.rank_transpose, Matrix.rank_conjTranspose_mul_self]
  rw [← h4, ← pure_iff_rank_eq_one]
  exact exists_congr fun ψ₁ => eq_comm

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.traceRight_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorUnitary i j
    ρ2 * (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := by
    have h₁ := fun i ↦ ρ.psd.eigenvalues_nonneg i
    simp only [Complex.norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, h₁, Real.sq_sqrt,
      Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    have : ∀ x, ∑ i : d, ‖ρ.Hermitian.eigenvectorUnitary i x‖ ^ 2 = 1 :=
      Matrix.unitaryGroup_row_norm ρ.Hermitian.eigenvectorUnitary
    apply @RCLike.ofReal_injective ℂ
    simp_rw [this, one_mul, Matrix.IsHermitian.sum_eigenvalues_eq_trace]
    exact ρ.tr'

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem purify_spec (ρ : MState d) : (pure ρ.purify).traceRight = ρ := by
  apply ext_m
  have key : ρ.m = Matrix.of fun i j => ∑ x, ρ.Hermitian.eigenvectorUnitary i x *
      ρ.Hermitian.eigenvalues x * conj (ρ.Hermitian.eigenvectorUnitary j x) := by
    conv_lhs => rw [ρ.Hermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq',
      Matrix.star_apply]
  rw [key]
  ext i j
  show ∑ x, ρ.purify (i, x) * conj (ρ.purify (j, x)) =
    ∑ x, ρ.Hermitian.eigenvectorUnitary i x * ρ.Hermitian.eigenvalues x *
      conj (ρ.Hermitian.eigenvectorUnitary j x)
  refine Finset.sum_congr rfl fun x _ => ?_
  show ρ.Hermitian.eigenvectorUnitary i x * (√(ρ.Hermitian.eigenvalues x) : ℝ) *
    conj (ρ.Hermitian.eigenvectorUnitary j x * (√(ρ.Hermitian.eigenvalues x) : ℝ)) = _
  rw [map_mul, Complex.conj_ofReal, mul_mul_mul_comm, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (ρ.psd.eigenvalues_nonneg x)]
  ring

/-- `MState.purify` bundled with its defining property `MState.traceRight_of_purify`. -/
def purifyX (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).traceRight = ρ } :=
  ⟨ρ.purify, ρ.purify_spec⟩

end purification

@[simps]
def relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : MState d₂ where
  M := ρ.M.reindex e.symm
  nonneg := by simp [zero_le_iff, ρ.psd]
  tr := by simp [trace]

@[simp]
theorem relabel_m (ρ : MState d₁) (e : d₂ ≃ d₁) :
    (ρ.relabel e).m = ρ.m.submatrix e e := by
  rfl

@[simp]
theorem relabel_refl {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    ρ.relabel (Equiv.refl d) = ρ := by
  ext
  simp

/-- Relabeling a pure state by a bijection yields another pure state. -/
theorem relabel_pure_exists (ψ : Ket d₁) (e : d₂ ≃ d₁) :
    ∃ ψ' : Ket d₂, (pure ψ).relabel e = pure ψ' := by
  refine ⟨⟨fun i => ψ (e i), ?_⟩, rfl⟩
  rw [← ψ.normalized', Fintype.sum_equiv e]
  congr!

@[simp]
theorem relabel_relabel {d d₂ d₃ : Type*}
    [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]
    (ρ : MState d) (e : d₂ ≃ d) (e₂ : d₃ ≃ d₂) : (ρ.relabel e).relabel e₂ = ρ.relabel (e₂.trans e) := by
  rfl

theorem eq_relabel_iff {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState d₁) (σ : MState d₂) (h : d₁ ≃ d₂) :
    ρ = σ.relabel h ↔ ρ.relabel h.symm = σ := by
  simp only [MState.ext_iff, HermitianMat.ext_iff, mat_M, relabel_m]
  exact ⟨(by simp[·]), (by simp[← ·])⟩

theorem relabel_comp {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (e : d₂ ≃ d₁) (f : d₃ ≃ d₂) :
    (ρ.relabel e).relabel f = ρ.relabel (f.trans e) := by
  ext
  simp

theorem relabel_cast {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂]
       (ρ : MState d₁) (e : d₂ = d₁) :
    ρ.relabel (Equiv.cast e) = cast (by have := e.symm; congr <;> (apply Subsingleton.helim; congr)) ρ := by
  ext i j
  simp only [relabel_M, mat_reindex, mat_M, Matrix.reindex_apply, Matrix.submatrix_apply]
  subst e
  congr!
  symm
  apply cast_heq

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem spectrum_relabel {ρ : MState d} (e : d₂ ≃ d) :
    _root_.spectrum ℝ (ρ.relabel e).m = _root_.spectrum ℝ ρ.m := by
  ext1 v
  rw [spectrum.mem_iff] --TODO make a plain `Matrix` version of this
  rw [Algebra.algebraMap_eq_smul_one v]
  rw [MState.relabel_m, ← Matrix.submatrix_one_equiv e]
  rw [← Matrix.smul_apply, ← Matrix.submatrix_smul]
  rw [← Matrix.sub_apply, ← Matrix.submatrix_sub]
  rw [Matrix.isUnit_submatrix_equiv]
  rw [← Algebra.algebraMap_eq_smul_one v, ← spectrum.mem_iff]

/-- The purity of a state is invariant under relabeling of the basis. -/
@[simp]
theorem purity_relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : (ρ.relabel e).purity = ρ.purity := by
  simp [purity, inner_def, -inner_self_eq_norm_sq_to_K]
--TODO: Swap and assoc for kets.
--TODO: Connect these to unitaries (when they can be)

/-- The heterogeneous SWAP gate that exchanges the left and right halves of a quantum system.
  This can apply even when the two "halves" are of different types, as opposed to (say) the SWAP
  gate on quantum circuits that leaves the qubit dimensions unchanged. Notably, it is not unitary. -/
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm

/--
The multiset of values in the spectrum of a relabeled state is the same as the multiset of values in the spectrum of the original state.
-/
lemma multiset_spectrum_relabel_eq {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState d₁) (e : d₂ ≃ d₁) :
    Multiset.map (ρ.relabel e).spectrum Finset.univ.val = Multiset.map ρ.spectrum Finset.univ.val := by
  have h_eig : Multiset.map (ρ.relabel e).M.H.eigenvalues Finset.univ.val =
      Multiset.map ρ.M.H.eigenvalues Finset.univ.val := by
    have h1 := ρ.M.H.roots_charpoly_eq_eigenvalues
    have h2 := (ρ.relabel e).M.H.roots_charpoly_eq_eigenvalues
    rw [show (ρ.relabel e).M.mat.charpoly = ρ.M.mat.charpoly from
      Matrix.charpoly_reindex e.symm _, h1] at h2
    simpa [Multiset.map_map, Function.comp_def] using congrArg (Multiset.map Complex.re) h2.symm
  refine Multiset.map_injective (f := Subtype.val) Subtype.val_injective ?_
  simpa only [Multiset.map_map, spectrum, ProbDistribution.mk', ProbDistribution.funlike_apply,
    Function.comp_def] using h_eig

def spectrum_SWAP (ρ : MState (d₁ × d₂)) : ∃ e, ρ.SWAP.spectrum.relabel e = ρ.spectrum := by
  -- Apply the lemma exists_equiv_of_multiset_map_eq with the appropriate parameters.
  obtain ⟨w, h⟩ := exists_equiv_of_multiset_map_eq (fun p => ρ.spectrum p) (fun p => ρ.SWAP.spectrum p)
    (ρ.multiset_spectrum_relabel_eq (Equiv.prodComm _ _).symm ▸ rfl)
  use w
  ext x
  simp_rw [h]
  rfl

@[simp]
theorem SWAP_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.SWAP = ρ :=
  rfl

@[simp]
theorem traceLeft_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceLeft = ρ.traceRight :=
  rfl

@[simp]
theorem traceRight_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceRight = ρ.traceLeft :=
  rfl

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃) :=
  ρ.relabel (Equiv.prodAssoc d₁ d₂ d₃).symm

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃) :=
  ρ.SWAP.assoc.SWAP.assoc.SWAP

@[simp]
theorem assoc_assoc' (ρ : MState (d₁ × d₂ × d₃)) : ρ.assoc'.assoc = ρ := by
  rfl

@[simp]
theorem assoc'_assoc (ρ : MState ((d₁ × d₂) × d₃)) : ρ.assoc.assoc' = ρ := by
  rfl

@[simp]
theorem traceLeft_right_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceRight = ρ.traceRight.traceLeft := by
  ext
  exact Finset.sum_comm

@[simp]
theorem traceRight_left_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceLeft = ρ.traceLeft.traceRight := by
  rw [← ρ.assoc'.traceLeft_right_assoc, assoc_assoc']

@[simp]
theorem traceRight_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceRight = ρ.traceRight.traceRight := by
  ext : 3
  apply Finset.sum_product

@[simp]
theorem traceLeft_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceLeft = ρ.traceLeft.traceLeft := by
  convert! ρ.SWAP.assoc.SWAP.traceRight_assoc
  simp

@[simp]
theorem traceLeft_left_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceLeft = ρ.traceLeft := by
  simp [← traceLeft_assoc']

@[simp]
theorem traceRight_right_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceRight = ρ.traceRight := by
  simp [assoc']

@[simp]
theorem traceNorm_eq_one (ρ : MState d) : ρ.m.traceNorm = 1 :=
  have := calc (ρ.m.traceNorm : ℂ)
    _ = ρ.m.trace := ρ.psd.traceNorm_eq_trace
    _ = 1 := ρ.tr'
  Complex.ofReal_eq_one.mp this

--TODO: This naming is very inconsistent. Should be better about "prod" vs "kron"

theorem relabel_kron (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₁) :
    ((ρ.relabel e) ⊗ᴹ σ) = (ρ ⊗ᴹ σ).relabel (e.prodCongr (Equiv.refl d₂)) := by
  rfl --is this defeq abuse? I don't know

theorem kron_relabel (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₂) :
    (ρ ⊗ᴹ σ.relabel e) = (ρ ⊗ᴹ σ).relabel ((Equiv.refl d₁).prodCongr e) := by
  rfl

theorem prod_assoc (ρ : MState d₁) (σ : MState d₂) (τ : MState d₃) :
    (ρ ⊗ᴹ (σ ⊗ᴹ τ)) = (ρ ⊗ᴹ σ ⊗ᴹ τ).relabel (Equiv.prodAssoc d₁ d₂ d₃).symm := by
  ext : 2
  simp [-Matrix.kronecker_assoc']
  exact (Matrix.kronecker_assoc' ρ.m σ.m τ.m).symm

section topology

/-- Mixed states inherit the subspace topology from matrices -/
instance : TopologicalSpace (MState d) :=
  TopologicalSpace.induced MState.M inferInstance

/-- The projection from mixed states to their Hermitian matrices is an embedding -/
theorem toMat_IsEmbedding : Topology.IsEmbedding (MState.M (d := d)) where
  eq_induced := rfl
  injective := @MState.ext _ _ _

instance : T3Space (MState d) :=
  Topology.IsEmbedding.t3Space toMat_IsEmbedding

instance : CompactSpace (MState d) := by
  constructor
  rw [(Topology.IsInducing.induced MState.M).isCompact_iff]
  suffices IsCompact (Set.Icc 0 1 ∩ { m | m.trace = 1} : Set (HermitianMat d ℂ)) by
    convert this
    ext1 m
    constructor
    · rintro ⟨ρ, _, rfl⟩
      simp [ρ.nonneg, ρ.le_one]
    · simpa using fun m_pos _ m_tr ↦ ⟨⟨m, m_pos, m_tr⟩, rfl⟩
  apply isCompact_Icc.inter_right
  refine isClosed_eq ?_ continuous_const
  rw [funext trace_eq_re_trace]
  fun_prop

noncomputable instance : MetricSpace (MState d) :=
  MetricSpace.induced MState.M MState.M_Injective inferInstance

theorem dist_eq (x y : MState d) : dist x y = dist x.M y.M := by
  rfl

set_option backward.isDefEq.respectTransparency false in
instance : BoundedSpace (MState d) where
  bounded_univ :=
    CompactSpace.isCompact_univ.isBounded

@[fun_prop]
theorem Continuous_HermitianMat : Continuous (MState.M (d := d)) :=
  continuous_iff_le_induced.mpr fun _ => id

@[fun_prop]
theorem Continuous_Matrix : Continuous (MState.m (d := d)) := by
  show Continuous (fun ρ : MState d => ρ.M.mat)
  fun_prop

theorem image_M_isBounded (S : Set (MState d)) : Bornology.IsBounded (MState.M '' S) := by
  rw [← Bornology.isBounded_induced]
  exact Bornology.IsBounded.all S

end topology

section finprod

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]

def piProd (ρi : (i:ι) → MState (dI i)) : MState ((i:ι) → dI i) where
  M := {
    val := Matrix.piProd (fun i ↦ (ρi i).m)
    property := Matrix.IsHermitian.piProd (fun i ↦ (ρi i).Hermitian)
  }
  nonneg := by
    rw [zero_le_iff]
    exact Matrix.PosSemidef.piProd (fun i => psd (ρi i))
  tr := by simp [trace, Matrix.trace_piProd]

/-- The n-copy "power" of a mixed state, with the standard basis indexed by pi types. -/
def npow (ρ : MState d) (n : ℕ) : MState (Fin n → d) :=
  piProd (fun _ ↦ ρ)

@[inherit_doc]
infixl:110 " ⊗ᴹ^ " => MState.npow

end finprod

section posdef

theorem PosDef.kron {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {σ₁ : MState d₁} {σ₂ : MState d₂} (hσ₁ : σ₁.m.PosDef) (hσ₂ : σ₂.m.PosDef) : (σ₁ ⊗ᴹ σ₂).m.PosDef :=
  hσ₁.kron hσ₂

theorem PosDef.relabel {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {ρ : MState d₁} (hρ : ρ.m.PosDef) (e : d₂ ≃ d₁) : (ρ.relabel e).m.PosDef :=
  Matrix.PosDef.reindex hρ e.symm

/-- If both states positive definite, so is their mixture. -/
theorem PosDef_mix {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₁ : σ₁.m.PosDef) (hσ₂ : σ₂.m.PosDef) (p : Prob) : (p [σ₁ ↔ σ₂]).m.PosDef :=
  Matrix.PosDef.Convex hσ₁ hσ₂ p.zero_le (1 - p).zero_le (by simp)

/-- If one state is positive definite and the mixture is nondegenerate, their mixture is also positive definite. -/
theorem PosDef_mix_of_ne_zero {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₁ : σ₁.m.PosDef) (p : Prob) (hp : p ≠ 0) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  rw [← zero_lt_iff] at hp
  exact (hσ₁.smul hp).add_posSemidef (σ₂.psd.rsmul (1 - p).zero_le)

/-- If the second state is positive definite and the mixture is nondegenerate, their mixture is also positive definite. -/
theorem PosDef_mix_of_ne_one {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₂ : σ₂.m.PosDef) (p : Prob) (hp : p ≠ 1) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  have h1 : 0 < 1 - p := by
    --TODO this is ridiculous, move to Prob
    rw [zero_lt_iff]
    intro h
    have h2 := congrArg Subtype.val h
    simp [sub_eq_zero] at h2
    exact hp (Subtype.ext (by simp [← h2]))
  exact (hσ₂.smul h1).posSemidef_add (σ₁.psd.rsmul p.zero_le)

theorem uniform_posDef {d : Type*} [Nonempty d] [Fintype d] [DecidableEq d] :
    (uniform (d := d)).m.PosDef := by
  simp [uniform, ofClassical, m, HermitianMat.diagonal]
  exact Fintype.card_pos

theorem posDef_of_unique {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) [Unique d] : ρ.m.PosDef := by
  rw [Subsingleton.allEq ρ uniform]
  exact uniform_posDef

end posdef

end MState
