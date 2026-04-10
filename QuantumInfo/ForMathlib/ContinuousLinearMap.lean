/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
--For the first three lemmas
module

public import Mathlib.Topology.Algebra.Module.LinearMap

--For the third lemma
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace ContinuousLinearMap

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M M₂ : Type*)
variable [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace M₂] [AddCommMonoid M₂]
variable [Module R M] [Module S M₂]

--These two theorems might look a bit silly as aliases of `LinearMap.____`, but they don't `simp` on their
--TODO: I think we can remove these now that we've bumped to Lean 4.28.0
@[simp]
theorem range_zero [RingHomSurjective σ] : (0 : M →SL[σ] M₂).range = ⊥ := by
  simp

@[simp]
theorem ker_zero : (0 : M →SL[σ] M₂).ker = ⊤ := by
  simp

theorem ker_mk (f : M →ₛₗ[σ] M₂) (hf : Continuous f.toFun) :
    (ContinuousLinearMap.mk f hf).ker = LinearMap.ker f := by
  rfl

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]

/-- The support of a Hermitian matrix is the sum of its nonzero eigenspaces. -/
theorem support_eq_sup_eigenspace_nonzero (A : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)
    (hA : A.IsSymmetric) : A.range = ⨆ μ ≠ 0, Module.End.eigenspace A μ := by
  apply le_antisymm
  · rintro x ⟨y, hy⟩
    have h_decomp : y ∈ ⨆ (μ : 𝕜), Module.End.eigenspace A.toLinearMap μ := by
      have h_orth := hA.orthogonalComplement_iSup_eigenspaces_eq_bot
      rw [Submodule.orthogonal_eq_bot_iff] at h_orth
      rw [h_orth]
      exact Submodule.mem_top;
    rw [Submodule.mem_iSup_iff_exists_finsupp] at h_decomp
    rcases h_decomp with ⟨f, hf₁, hf₂⟩
    have h_apply_A : A y = ∑ i ∈ f.support, A (f i) := by
      rw [← hf₂, map_finsuppSum]
      exact rfl
    have h_eigen (i) : A (f i) = (i : 𝕜) • f i :=
      Module.End.mem_eigenspace_iff.mp (hf₁ i)
    rw [← hy, coe_coe, h_apply_A, Finset.sum_congr rfl (fun i _ ↦ h_eigen i)]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi0 : i = 0
    · simp [hi0]
    · apply Submodule.smul_mem
      apply Submodule.mem_iSup_of_mem i
      exact Submodule.mem_iSup_of_mem hi0 (hf₁ i)
  · simp only [iSup_le_iff]
    intro μ hμ x hx
    use μ⁻¹ • x
    simp_all

end ContinuousLinearMap
