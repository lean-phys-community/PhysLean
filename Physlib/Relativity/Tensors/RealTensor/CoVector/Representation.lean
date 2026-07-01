/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Physlib.Relativity.LorentzGroup.Basic
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Basic
/-!

# Representation of the Lorentz group on Lorentz vectors

In this module we define the representation of the Lorentz group on Lorentz covectors.
This does not define the MulAction on `Lorentz.CoVector`, which is induced
by its tensor structure.

-/

@[expose] public section


open Module Matrix MatrixGroups Complex TensorProduct

noncomputable section

namespace Lorentz

namespace CoVector
attribute [-simp] Fintype.sum_sum_type

/-- The representation of the Lorentz group on Lorentz vectors. -/
def rep {d : ℕ} : Representation ℝ (LorentzGroup d) (CoVector d) where
  toFun Λ := Matrix.toLinAlgEquiv basis (LorentzGroup.transpose Λ⁻¹)
  map_one' := by
    simp only [inv_one, LorentzGroup.transpose_one, lorentzGroupIsGroup_one_coe, _root_.map_one]
  map_mul' x y := by
    simp only [_root_.mul_inv_rev, LorentzGroup.inv_eq_dual, LorentzGroup.transpose_mul,
      lorentzGroupIsGroup_mul_coe, _root_.map_mul]

/-!

## Properties of the representation.

-/

lemma rep_apply_eq_mulVec (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) :
    rep Λ v = (LorentzGroup.transpose Λ⁻¹) *ᵥ v := by rfl

lemma rep_apply_eq_sum (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, (Λ⁻¹).1 j k • v j := rfl

lemma rep_apply_eq_sum_coe (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, Λ.1⁻¹ j k • v j := by
  rw [rep_apply_eq_sum, LorentzGroup.coe_inv]

lemma rep_apply_basis {d} (μ : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) :
    rep Λ (basis μ) = ∑ j, Λ.1⁻¹ μ j • basis j := by
  ext k
  simp [rep_apply_eq_sum_coe, apply_sum]

lemma rep_toMatrix (d : ℕ) (Λ : LorentzGroup d) :
    LinearMap.toMatrix basis basis (rep Λ) = Λ.1⁻¹ᵀ := by
  simp only [rep, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← LorentzGroup.coe_inv]
  exact (LinearEquiv.eq_symm_apply (LinearMap.toMatrix basis basis)).mp rfl

lemma rep_injective (d : ℕ) (Λ : LorentzGroup d) : Function.Injective (rep Λ) := by
  intro v1 v2 h
  rw [rep_apply_eq_mulVec, rep_apply_eq_mulVec] at h
  exact Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible _) h

lemma rep_surjective (d : ℕ) (Λ : LorentzGroup d) : Function.Surjective (rep Λ) := by
  intro v
  use (LorentzGroup.transpose Λ) *ᵥ v
  rw [rep_apply_eq_mulVec]
  simp [← LorentzGroup.transpose_inv, LorentzGroup.coe_inv]

lemma rep_bijective (d : ℕ) (Λ : LorentzGroup d) : Function.Bijective (rep Λ) :=
  ⟨rep_injective d Λ, rep_surjective d Λ⟩

end CoVector

end Lorentz
