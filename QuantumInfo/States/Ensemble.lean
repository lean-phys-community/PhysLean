/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa
-/
module

public import QuantumInfo.States.Mixed.MState
public import Physlib.Meta.Sorry

@[expose] public section

open MState
open BigOperators
open scoped RealInnerProductSpace InnerProductSpace

noncomputable section

/-- A mixed-state ensemble is a random variable valued in `MState d`. That is,
a collection of mixed states `var : α → MState d`, each with their own probability weight
described by `distr : ProbDistribution α`. -/
abbrev MEnsemble (d : Type*) (α : Type*) [Fintype d] [DecidableEq d] [Fintype α] := ProbDistribution.RandVar α (MState d)

/-- A pure-state ensemble is a random variable valued in `Ket d`. That is,
a collection of pure states `var : α → Ket d`, each with their own probability weight
described by `distr : ProbDistribution α`. -/
abbrev PEnsemble (d : Type*) (α : Type*) [Fintype d] [Fintype α] := ProbDistribution.RandVar α (Ket d)

variable {α β d : Type*} [Fintype α] [Fintype β] [Fintype d] [DecidableEq d]

/-- Alias for `ProbDistribution.var` for mixed-state ensembles. -/
abbrev MEnsemble.states : MEnsemble d α → (α → MState d) := ProbDistribution.RandVar.var

/-- Alias for `ProbDistribution.var` for pure-state ensembles. -/
abbrev PEnsemble.states : PEnsemble d α → (α → Ket d) := ProbDistribution.RandVar.var

namespace Ensemble

/-- A pure-state ensemble is a mixed-state ensemble if all kets are interpreted as mixed states. -/
@[coe] def toMEnsemble : PEnsemble d α → MEnsemble d α := Functor.map pure

instance : Coe (PEnsemble d α) (MEnsemble d α) := ⟨toMEnsemble⟩

@[simp]
theorem toMEnsemble_mk : (toMEnsemble ⟨ps, distr⟩ : MEnsemble d α) = ⟨pure ∘ ps, distr⟩ :=
  rfl

/-- A mixed-state ensemble comes from a pure-state ensemble if and only if all states are pure. -/
theorem coe_PEnsemble_iff_pure_states (me : MEnsemble d α): (∃ pe : PEnsemble d α, ↑pe = me) ↔ (∃ ψ : α → Ket d, me.states = MState.pure ∘ ψ) := by
  refine ⟨fun ⟨pe, hpe⟩ => ⟨pe.states, hpe ▸ rfl⟩,
    fun ⟨ψ, hψ⟩ => ⟨⟨ψ, me.distr⟩, by rw [toMEnsemble_mk, ← hψ]⟩⟩

/-- The resulting mixed state after mixing the states in an ensemble with their
respective probability weights. Note that, generically, a single mixed state has infinitely many
ensembles that mixes into it. -/
def mix (e : MEnsemble d α) : MState d := ProbDistribution.expect_val e

@[simp]
theorem mix_of (e : MEnsemble d α) : (mix e).m = ∑ i, (e.distr i : ℝ) • (e.states i).m := by
  apply AddSubgroup.val_finsetSum -- *laughs in defeq*

/-- Two mixed-state ensembles indexed by `\alpha` and `\beta` are equivalent if `α ≃ β`. -/
def congrMEnsemble (σ : α ≃ β) : MEnsemble d α ≃ MEnsemble d β := ProbDistribution.congrRandVar σ

/-- Two pure-state ensembles indexed by `\alpha` and `\beta` are equivalent if `α ≃ β`. -/
def congrPEnsemble (σ : α ≃ β) : PEnsemble d α ≃ PEnsemble d β := ProbDistribution.congrRandVar σ

/-- Equivalence of mixed-state ensembles leaves the resulting mixed state invariant -/
@[simp]
theorem mix_congrMEnsemble_eq_mix (σ : α ≃ β) (e : MEnsemble d α) : mix (congrMEnsemble σ e) = mix e :=
  ProbDistribution.expect_val_congr_eq_expect_val σ e

/-- Equivalence of pure-state ensembles leaves the resulting mixed state invariant -/
@[simp]
theorem mix_congrPEnsemble_eq_mix (σ : α ≃ β) (e : PEnsemble d α) : mix (toMEnsemble (congrPEnsemble σ e)) = mix (↑e : MEnsemble d α) := by
  exact (congrArg ProbDistribution.expect_val
    (ProbDistribution.map_congr_eq_congr_map MState.pure σ e)).trans
    (ProbDistribution.expect_val_congr_eq_expect_val σ (MState.pure <$> e))

/-- The average of a function `f : MState d → T`, where `T` is of `Mixable U T` instance, on a mixed-state ensemble `e`
is the expectation value of `f` acting on the states of `e`, with the corresponding probability weights from `e.distr`. -/
def average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (e : MEnsemble d α) : T :=
  ProbDistribution.expect_val <| f <$> e

/-- A version of `average` conveniently specialized for functions `f : MState d → ℝ≥0` returning nonnegative reals.
Notably, the average is also a nonnegative real number. -/
def average_NNReal {d : Type _} [Fintype d] [DecidableEq d] (f : MState d → NNReal) (e : MEnsemble d α) : NNReal :=
  ⟨average (NNReal.toReal ∘ f) e,
    ProbDistribution.zero_le_expect_val e.distr (NNReal.toReal ∘ f ∘ e.states) (fun n => (f <| e.states n).2)⟩

/-- The average of a function `f : Ket d → T`, where `T` is of `Mixable U T` instance, on a pure-state ensemble `e`
is the expectation value of `f` acting on the states of `e`, with the corresponding probability weights from `e.distr`. -/
def pure_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) (e : PEnsemble d α) : T :=
  ProbDistribution.expect_val <| f <$> e

/-- A version of `average` conveniently specialized for functions `f : Ket d → ℝ≥0` returning nonnegative reals.
Notably, the average is also a nonnegative real number. -/
def pure_average_NNReal {d : Type _} [Fintype d] (f : Ket d → NNReal) (e : PEnsemble d α) : NNReal :=
  ⟨pure_average (NNReal.toReal ∘ f) e,
    ProbDistribution.zero_le_expect_val e.distr (NNReal.toReal ∘ f ∘ e.states) (fun n => (f <| e.states n).2)⟩

/-- The average of `f : MState d → T` on a coerced pure-state ensemble `↑e : MEnsemble d α`
is equal to averaging the restricted function over Kets `f ∘ pure : Ket d → T` on `e`. -/
theorem average_of_pure_ensemble {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T]
  (f : MState d → T) (e : PEnsemble d α) :
  average f (toMEnsemble e) = pure_average (f ∘ pure) e := by
  simp only [average, pure_average, toMEnsemble, comp_map]

variable {ψ : Ket d}

@[simp]
theorem distr_toMEnsemble (e : PEnsemble d α) : (toMEnsemble e).distr = e.distr := by
  rfl

/-
A pure-state ensemble mixes into a pure state if and only if
the only states in the ensemble with nonzero probability are equal
to the same Ket `ψ` up to a global phase.
-/
theorem mix_pEnsemble_pure_iff_pure {e : PEnsemble d α} :
    mix (toMEnsemble e) = MState.pure ψ ↔
    ∀ i : α, e.distr i ≠ 0 → MState.pure (e.states i) = MState.pure ψ := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦ ?_⟩
  · apply MState.eq_of_sum_eq_pure ?_ ?_ ?_ e.distr.normalized i (Finset.mem_univ i)
    · exact_mod_cast lt_of_le_of_ne (e.distr i).zero_le hi.symm
    · exact (MState.pure_iff_purity_one _).mp ⟨ψ, rfl⟩
    · exact congr_arg MState.M h.symm
    · grind
  · have h_sum : mix (toMEnsemble e) = ∑ i, (e.distr i).val • (MState.pure ψ).M := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : e.distr i = 0
      · simp [hi]
      · rw [← h i hi]
        rfl
    simp [MState.ext_iff, h_sum, ← Finset.sum_smul]

/- The theorem below is also false for the same reason as the original `mix_pEnsemble_pure_iff_pure`:
   knowing `MState.pure (e.states i) = MState.pure ψ` does not imply `e.states i = ψ` as Kets,
   so `f (e.var i) ≠ f ψ` in general for a non-phase-invariant `f : Ket d → T`. -/
/-- The average of `f : Ket d → T` on an ensemble that mixes to a pure state `ψ` is `f ψ` -/
theorem mix_pEnsemble_pure_average {e : PEnsemble d α} {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U]
    [inst : Mixable U T] (f : Ket d → T) (hf : ∀ ψ φ, Ket.PhaseEquiv.r ψ φ → f ψ = f φ)
    (hmix : mix (toMEnsemble e) = MState.pure ψ) :
  pure_average f e = f ψ := by
  have hpure := mix_pEnsemble_pure_iff_pure.mp hmix
  simp only [pure_average, Functor.map, ProbDistribution.expect_val]
  apply Mixable.to_U_inj
  simp only [Mixable.to_U_of_mkT, Function.comp_apply]
  have h2 : ∀ i ∈ Finset.univ, (e.distr i : ℝ) • Mixable.to_U (f (e.var i))
      = (e.distr i : ℝ) • Mixable.to_U (f ψ) := fun i _ => by
    rcases eq_or_ne (e.distr i) 0 with hdi | hdi
    · simp [hdi]
    · rw [hf _ _ ((MState.PhaseEquiv_iff_pure_eq _ _).mpr (hpure i hdi))]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_smul, ProbDistribution.normalized, one_smul]

theorem sum_prob_mul_eq_one_iff {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hx : ∀ i, x i ≤ 1) :
    (∑ i, p i * x i = 1) ↔ ∀ i, p i ≠ 0 → x i = 1 := by
  nth_rewrite 1 [← hsum]
  rw [Finset.sum_eq_sum_iff_of_le fun i _ => mul_le_of_le_one_right (hp i) (hx i)]
  simp [mul_right_eq_self₀, or_iff_not_imp_right]

theorem MState.exp_val_pure_eq_one_iff {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (ψ : Ket d) :
    ρ.exp_val (pure ψ) = 1 ↔ ρ = pure ψ := by
  have hpure_inner : ⟪(MState.pure ψ).M, (MState.pure ψ).M⟫ = 1 := by
    simpa [MState.inner_def] using congrArg (fun p : Prob => (p : ℝ))
      (Subtype.ext (α := ℝ) (by simp [MState.pure_inner, Braket.dot_self_eq_one]) :
        ⟪MState.pure ψ, MState.pure ψ⟫_Prob = 1)
  constructor
  · intro h
    have hρ_le : ⟪ρ.M, ρ.M⟫ ≤ 1 := by
      simpa [ρ.tr] using HermitianMat.inner_le_mul_trace ρ.nonneg ρ.nonneg
    have hinner : ⟪ρ.M, (MState.pure ψ).M⟫ = 1 := by simpa [MState.exp_val] using h
    have hsq := real_inner_sub_sub_self ρ.M (MState.pure ψ).M
    exact MState.ext (eq_of_sub_eq_zero (inner_self_eq_zero.mp (le_antisymm
      (hsq.trans_le (by linarith)) (ρ.M - (MState.pure ψ).M).inner_self_nonneg)))
  · rintro rfl
    simpa [MState.exp_val] using hpure_inner

set_option backward.isDefEq.respectTransparency false in
theorem mix_mEnsemble_pure_iff_pure {e : MEnsemble d α} :
    mix e = pure ψ ↔ ∀ i : α, e.distr i ≠ 0 → e.states i = MState.pure ψ := by
  have h : (mix e).exp_val ↑(MState.pure ψ)
      = ∑ i, ↑(e.distr i) * (e.states i).exp_val ↑(MState.pure ψ) := by
    simp [MState.exp_val, HermitianMat.inner_def, Finset.sum_mul]
  rw [← MState.exp_val_pure_eq_one_iff, h, sum_prob_mul_eq_one_iff]
  · simp only [MState.exp_val_pure_eq_one_iff, ne_eq, Set.Icc.coe_eq_zero]
  · exact fun i => (e.distr i).2.1
  · simp
  · exact fun i => (e.states i).exp_val_le_one (MState.le_one _)

/-- The average of `f : MState d → T` on an ensemble that mixes to a pure state `ψ` is `f (pure ψ)` -/
theorem mix_mEnsemble_pure_average {e : MEnsemble d α} {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (hmix : mix e = pure ψ) :
  average f e = f (pure ψ) := by
  have hpure := mix_mEnsemble_pure_iff_pure.mp hmix
  simp only [average, Functor.map, ProbDistribution.expect_val]
  apply Mixable.to_U_inj
  simp only [Mixable.to_U_of_mkT, Function.comp_apply]
  have h2 : ∀ i ∈ Finset.univ, (e.distr i : ℝ) • Mixable.to_U (f (e.var i))
      = (e.distr i : ℝ) • Mixable.to_U (f (pure ψ)) := fun i _ => by
    rcases eq_or_ne (e.distr i) 0 with hdi | hdi
    · simp [hdi]
    · rw [show e.var i = MState.pure ψ from hpure i hdi]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_smul, ProbDistribution.normalized, one_smul]

/-- The trivial mixed-state ensemble of `ρ` consists of copies of `rho`, with the `i`-th one having
probability 1. -/
def trivial_mEnsemble (ρ : MState d) (i : α) : MEnsemble d α := ⟨fun _ ↦ ρ, ProbDistribution.constant i⟩

/-- The trivial mixed-state ensemble of `ρ` mixes to `ρ` -/
theorem trivial_mEnsemble_mix (ρ : MState d) : ∀ i : α, mix (trivial_mEnsemble ρ i) = ρ := fun i ↦by
  apply MState.ext_m
  classical simp [trivial_mEnsemble, ProbDistribution.constant, DFunLike.coe, apply_ite]

/-- The average of `f : MState d → T` on a trivial ensemble of `ρ` is `f ρ`-/
theorem trivial_mEnsemble_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (ρ : MState d):
  ∀ i : α, average f (trivial_mEnsemble ρ i) = f ρ := fun i ↦ by
    apply Mixable.to_U_inj
    classical simp [average, Functor.map, ProbDistribution.expect_val, trivial_mEnsemble,
      apply_ite]

instance MEnsemble.instInhabited [Nonempty d] [Inhabited α] : Inhabited (MEnsemble d α) where
  default := trivial_mEnsemble default default

/-- The trivial pure-state ensemble of `ψ` consists of copies of `ψ`, with the `i`-th one having
probability 1. -/
def trivial_pEnsemble (ψ : Ket d) (i : α) : PEnsemble d α := ⟨fun _ ↦ ψ, ProbDistribution.constant i⟩

variable (ψ : Ket d)

/-- The trivial pure-state ensemble of `ψ` mixes to `ψ` -/
theorem trivial_pEnsemble_mix : ∀ i : α, mix (toMEnsemble (trivial_pEnsemble ψ i)) = MState.pure ψ := fun i ↦ by
  apply MState.ext_m
  classical simp [trivial_pEnsemble, ProbDistribution.constant, DFunLike.coe, apply_ite,
    MEnsemble.states]

omit [DecidableEq d] in
/-- The average of `f : Ket d → T` on a trivial ensemble of `ψ` is `f ψ`-/
theorem trivial_pEnsemble_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) :
  ∀ i : α, pure_average f (trivial_pEnsemble ψ i) = f ψ := fun i ↦ by
    apply Mixable.to_U_inj
    classical simp [pure_average, Functor.map, ProbDistribution.expect_val, trivial_pEnsemble,
      apply_ite]

instance PEnsemble.instInhabited [Nonempty d] [Inhabited α] : Inhabited (PEnsemble d α) where
  default := trivial_pEnsemble default default

/-- The spectral pure-state ensemble of `ρ`. The states are its eigenvectors, and the probabilities, eigenvalues. -/
def spectral_ensemble (ρ : MState d) : PEnsemble d d where
  var i :=
    { vec := ρ.Hermitian.eigenvectorBasis i
      normalized' := by
        rw [← EuclideanSpace.norm_sq_eq, ρ.Hermitian.eigenvectorBasis.orthonormal.1 i, one_pow]
    }
  distr := ρ.spectrum

--PULLOUT
theorem spectral_decomposition_sum {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.IsHermitian) :
    A = ∑ i, (hA.eigenvalues i) • (Matrix.vecMulVec (hA.eigenvectorBasis i) (star (hA.eigenvectorBasis i))) := by
  nth_rw 1 [hA.spectral_theorem]
  ext
  simp only [Matrix.sum_apply, Unitary.conjStarAlgAut_apply, mul_assoc]
  simp [Matrix.mul_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec, Algebra.smul_def, mul_comm, mul_assoc, mul_ite]

/-- The spectral pure-state ensemble of `ρ` mixes to `ρ` -/
theorem spectral_ensemble_mix {ρ : MState d} : mix (↑(spectral_ensemble ρ) : MEnsemble d d) = ρ := by
  apply MState.ext_m
  rw [mix_of]
  exact (spectral_decomposition_sum ρ.Hermitian).symm

end Ensemble
