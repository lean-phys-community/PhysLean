/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.Symmetric
/-!

# Spectral theory for self-adjoint operators

## i. Overview

In this module we develop the spectral theory for self-adjoint operators.

## ii. Key results

- `resolventSet_eq_regularityDomain` : The resolvent set and regularity domain coincide. That is,
    if `T - z • 1` has a continuous (equivalently, bounded) inverse then its range is all of `H`.
- `spectrum_real` : The spectrum of a self-adjoint unbounded operator is real.

## iii. Table of contents

- A. Resolvent set
- B. Spectrum

## iv. References

-/

@[expose] public section

namespace LinearPMap
namespace IsSelfAdjoint

open Complex
open ComplexConjugate
open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T)
include hT

/-!
## A. Resolvent set
-/

lemma resolventSet_eq_regularityDomain : ρ T = T.regularityDomain := by
  refine Subset.antisymm T.resolventSet_subset_regularityDomain fun z hz ↦ ?_
  obtain ⟨h_ker, h_cont⟩ := mem_regularityDomain_iff.mp hz
  refine ⟨h_ker, ?_, h_cont⟩
  have h_ker' : (T - conj z • 1).toFun.ker = ⊥ := by
    by_cases hz' : conj z = z
    · exact hz'.symm ▸ h_ker
    · exact (mem_regularityDomain_iff.mp <| (isSymmetric hT).mem_regularityDomain_of_im_ne_zero
        (by simp_all [Complex.conj_eq_iff_im])).1
  have h_orthog := (isUnbounded hT).orthogonal_adjoint_sub_ker hz
  rw [isSelfAdjoint_def.mp hT, (isClosed hT).closure_eq, h_ker'] at h_orthog
  simp [← h_orthog]

/-- `(T - z • 1).range = ⊤` is a sufficient condition for `z ∈ ρ T`
  (and it is a necessary condition by definition of `ρ`). -/
lemma mem_resolventSet_of_range_eq_top {z : ℂ} (h : (T - z • 1).toFun.range = ⊤) : z ∈ ρ T := by
  by_cases hz_im : z.im = 0
  · rw [(isClosed hT).resolventSet_eq]
    refine ⟨?_, h⟩
    have h_orthog := (isUnbounded hT).orthogonal_closure_sub_range z
    rwa [isSelfAdjoint_def.mp hT, (isClosed hT).closure_eq, conj_eq_iff_im.mpr hz_im, h,
      Submodule.top_orthogonal_eq_bot, Eq.comm, ← LinearMap.le_ker_iff_map, Submodule.ker_subtype,
      le_bot_iff] at h_orthog
  · rw [resolventSet_eq_regularityDomain hT]
    exact (isSymmetric hT).mem_regularityDomain_of_im_ne_zero hz_im

/-!
## B. Spectrum
-/

/-- The spectrum of a self-adjoint operator is real. -/
lemma spectrum_real : σ T ⊆ range ofReal := by
  rw [spectrum_eq, resolventSet_eq_regularityDomain hT]
  exact compl_subset_comm.mp (isSymmetric hT).compl_ofReal_subset_regularityDomain

/-- The residual spectrum of a self-adjoint operator is empty. -/
lemma residualSpectrum_eq_empty : σʳ T = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hz ↦ T.residualSpectrum_subset_spectrum hz
    (resolventSet_eq_regularityDomain hT ▸ T.residualSpectrum_subset_regularityDomain hz)

end IsSelfAdjoint
end LinearPMap
