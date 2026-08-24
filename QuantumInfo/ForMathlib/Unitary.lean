/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import QuantumInfo.ForMathlib.HermitianMat.Unitary

open BigOperators
open Classical

namespace LinearMap
section unitary

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

open Module.End

@[simp]
theorem unitary_star_apply_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    (star U.val) (U.val v) = v := by
  rw [← mul_apply, (Unitary.mem_iff.mp U.prop).left, one_apply]

@[simp]
theorem unitary_apply_star_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    U.val ((star U.val) v) = v := by
  rw [← mul_apply, (Unitary.mem_iff.mp U.prop).right, one_apply]

/-- Conjugating a linear map by a unitary operator gives a map whose μ-eigenspace is
  isomorphic (same dimension) as those of the original linear map. -/
noncomputable def conj_unitary_eigenspace_equiv (T : E →ₗ[𝕜] E) (U : unitary (E →ₗ[𝕜] E)) (μ : 𝕜) :
    eigenspace T μ ≃ₗ[𝕜] eigenspace (U.val * T * star (U.val)) μ where
  toFun v := ⟨U.val v.val, by
    have hv := v.2
    rw [mem_eigenspace_iff] at hv ⊢
    simp [hv]⟩
  invFun v := ⟨(star U.val) v, by
    have hv := v.2
    rw [mem_eigenspace_iff] at hv ⊢
    simpa using congrArg ((star U.val) ·) hv⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv _ := by simp
  right_inv _ := by simp

end unitary
namespace IsSymmetric

open Module.End

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {T : E →ₗ[𝕜] E}

/-- A symmetric operator conjugated by a unitary is symmetric. -/
theorem conj_unitary_IsSymmetric (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    (U.val * T * star U.val).IsSymmetric := by
  intro i j
  rw [mul_assoc, mul_apply, ← LinearMap.adjoint_inner_right]
  rw [mul_apply, mul_apply, mul_apply, ← LinearMap.adjoint_inner_left U.val]
  exact hT (star U.val <| i) (star U.val j)

variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)

/-- The number of indices carrying the eigenvalue `μ` is the dimension of the `μ`-eigenspace. This
drops the `HasEigenvalue` hypothesis of `card_filter_eigenvalues_eq`: when `μ` is not an eigenvalue,
both sides are zero. -/
theorem card_filter_eigenvalues_eq_finrank (hT : T.IsSymmetric) (μ : 𝕜) :
    Finset.card {i | (hT.eigenvalues hn i : 𝕜) = μ} = Module.finrank 𝕜 (eigenspace T μ) := by
  by_cases hμ : HasEigenvalue T μ
  · exact hT.card_filter_eigenvalues_eq hn hμ
  · have hb : eigenspace T μ = ⊥ := not_ne_iff.mp (Module.End.hasEigenvalue_iff.not.mp hμ)
    rw [hb, finrank_bot, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun {i} _ h ↦ hμ (h ▸ hT.hasEigenvalue_eigenvalues hn i)

/-- Two antitone tuples of reals that take each value the same number of times are equal: an
antitone tuple is determined by, and determines, the multiset of its values. -/
private theorem eq_of_antitone_of_card_filter_eq {f g : Fin n → ℝ} (hf : Antitone f)
    (hg : Antitone g) (h : ∀ r : ℝ, Finset.card {i | f i = r} = Finset.card {i | g i = r}) :
    f = g := by
  have hm : Finset.univ.val.map f = Finset.univ.val.map g := by
    refine Multiset.ext.mpr fun r ↦ ?_
    have e : ∀ u : Fin n → ℝ, Multiset.filter (fun a ↦ r = u a) Finset.univ.val
        = Multiset.filter (fun a ↦ u a = r) Finset.univ.val :=
      fun u ↦ Multiset.filter_congr fun a _ ↦ eq_comm
    rw [Multiset.count_map, Multiset.count_map, e, e]
    exact h r
  have hcard : ∀ (p : ℝ → Prop) [DecidablePred p] (u : Fin n → ℝ),
      Finset.card {i | p (u i)} = Multiset.countP p (Finset.univ.val.map u) := by
    intro p _ u
    rw [Multiset.countP_map]
    rfl
  have hlt : ∀ r : ℝ, Finset.card {i | r < f i} = Finset.card {i | r < g i} := fun r ↦
    (hcard _ f).trans ((congrArg (Multiset.countP (r < ·)) hm).trans (hcard _ g).symm)
  -- For an antitone `u`, the indices with `r < u i` form an initial segment, so `r < u i` forces
  -- `i` to be less than the number of such indices.
  have key : ∀ u v : Fin n → ℝ, Antitone u → Antitone v →
      (∀ r : ℝ, Finset.card {i | r < u i} = Finset.card {i | r < v i}) → ∀ i, v i ≤ u i := by
    intro u v hu hv h i
    by_contra hlt
    push_neg at hlt
    have h1 : (i : ℕ) + 1 ≤ Finset.card {j | u i < v j} := by
      rw [← Fin.card_Iic i]
      exact Finset.card_le_card fun j hj ↦ Finset.mem_filter.mpr
        ⟨Finset.mem_univ j, hlt.trans_le (hv (Finset.mem_Iic.mp hj))⟩
    have h2 : Finset.card {j | u i < u j} ≤ (i : ℕ) := by
      rw [← Fin.card_Iio i]
      refine Finset.card_le_card fun j hj ↦ Finset.mem_Iio.mpr ?_
      by_contra hij
      exact absurd (hu (not_lt.mp hij)) (not_le.mpr (Finset.mem_filter.mp hj).2)
    rw [h (u i)] at h2
    omega
  exact funext fun i ↦ le_antisymm (key g f hg hf (fun r ↦ (hlt r).symm) i) (key f g hf hg hlt i)

/-- There is an equivalence between the eigenvalues of a finite dimensional symmetric operator,
and the eigenvalues of that operator conjugated by a unitary. Since `eigenvalues` lists the
eigenvalues in decreasing order, the two lists are in fact equal, and the permutation can be taken
to be the identity. -/
def conj_unitary_eigenvalue_equiv (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    { σ : Equiv.Perm (Fin n) // (hT.conj_unitary_IsSymmetric U).eigenvalues hn = hT.eigenvalues hn ∘ σ } := by
  refine ⟨Equiv.refl _, ?_⟩
  simp only [Equiv.coe_refl, Function.comp_id]
  refine eq_of_antitone_of_card_filter_eq (eigenvalues_antitone _ hn) (eigenvalues_antitone _ hn) ?_
  intro r
  have h1 := (hT.conj_unitary_IsSymmetric U).card_filter_eigenvalues_eq_finrank hn (r : 𝕜)
  have h2 := hT.card_filter_eigenvalues_eq_finrank hn (r : 𝕜)
  simp only [RCLike.ofReal_inj] at h1 h2
  rw [h1, h2]
  exact (LinearMap.conj_unitary_eigenspace_equiv T U (r : 𝕜)).symm.finrank_eq

end IsSymmetric
end LinearMap
