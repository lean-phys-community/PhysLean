/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Physlib.Relativity.LorentzGroup.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
/-!

# Representation of the Lorentz group on Lorentz vectors

In this module we define the representation of the Lorentz group on Lorentz vectors.
This does not define the MulAction on `Lorentz.Vector`, which is induced
by its tensor structure.

-/

@[expose] public section


open Module Matrix MatrixGroups Complex TensorProduct

noncomputable section

namespace Lorentz

namespace Vector
attribute [-simp] Fintype.sum_sum_type

/-- The representation of the Lorentz group on Lorentz vectors. -/
def rep {d : ℕ} : Representation ℝ (LorentzGroup d) (Vector d) where
  toFun Λ := Matrix.toLinAlgEquiv basis Λ
  map_one' := EmbeddingLike.map_eq_one_iff.mpr rfl
  map_mul' x y := by simp only [lorentzGroupIsGroup_mul_coe, _root_.map_mul]

/-!

## Properties of the representation.

-/

lemma rep_apply_eq_mulVec (d : ℕ) (Λ : LorentzGroup d) (v : Vector d) :
    rep Λ v = Λ *ᵥ v := by rfl

lemma rep_apply_eq_sum (d : ℕ) (Λ : LorentzGroup d) (v : Vector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, Λ.1 k j • v j := rfl

lemma rep_apply_basis {d} (μ : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) :
    rep Λ (basis μ) = ∑ j, Λ.1 j μ • basis j := by
  ext k
  simp [rep_apply_eq_sum, apply_sum]

lemma rep_toMatrix (d : ℕ) (Λ : LorentzGroup d) :
    LinearMap.toMatrix basis basis (rep Λ) = Λ.1 := by
  simp only [rep, MonoidHom.coe_mk, OneHom.coe_mk]
  exact (LinearEquiv.eq_symm_apply (LinearMap.toMatrix basis basis)).mp rfl

lemma rep_injective (d : ℕ) (Λ : LorentzGroup d) : Function.Injective (rep Λ) := by
  intro v1 v2 h
  rw [rep_apply_eq_mulVec, rep_apply_eq_mulVec] at h
  exact Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible Λ.1) h

lemma rep_surjective (d : ℕ) (Λ : LorentzGroup d) : Function.Surjective (rep Λ) := by
  intro v
  use Λ⁻¹ *ᵥ v
  rw [rep_apply_eq_mulVec]
  simp

lemma rep_bijective (d : ℕ) (Λ : LorentzGroup d) : Function.Bijective (rep Λ) :=
  ⟨rep_injective d Λ, rep_surjective d Λ⟩

@[fun_prop]
lemma rep_contDiff (d : ℕ) {n} (Λ : LorentzGroup d) : ContDiff ℝ n (rep Λ) := by
  refine (contDiff_apply ⇑(rep Λ)).mp ?_
  intro μ
  simp only [rep_apply_eq_sum, smul_eq_mul]
  fun_prop

lemma rep_left_injective (d : ℕ) : Function.Injective (rep (d := d)) := by
  intro Λ Λ' h
  apply LorentzGroup.eq_of_mulVec_eq
  intro v
  rw [← rep_apply_eq_mulVec, ← rep_apply_eq_mulVec]
  exact LinearMap.congr_fun h v

end Vector

end Lorentz
