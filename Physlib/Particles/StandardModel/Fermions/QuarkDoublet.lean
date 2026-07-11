/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Weyl.Basic
/-!
# The type corresponding to quark doublets

In this module we define the type corresponding to
the target vector space of a quark field in the Standard Model.

On this type we define a representation of the Lorentz group, and a
representation of the Standard Model gauge group.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

TODO "Add other fermions similar to this file with the names:
 - UpSinglet (3, 1)_{4} (right-handed)
 - DownSinglet (3, 1)_{-2} (right-handed)
 - LeptonDoublet (1, 2)_{-3} (left-handed)
 - LeptonSinglet (1, 1)_{-6} (right-handed)"

/-- The vector space of a quark field in the Standard Model.
  These live in the (3, 2)_{1} representation of the gauge group. -/
@[ext]
structure QuarkDoublet where
  /-- The underlying value of the quark field in the tensor product space. -/
  val : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)

namespace QuarkDoublet

/-!

## Equivalence with the underlying tensor product space

-/

/-- The linear equivalence between `QuarkDoublet` and its underlying tensor product space. -/
def valEquiv : QuarkDoublet ≃
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩

/-!

## The structure of a module

The AddCommGroup and module instances are inherited from the underlying tensor product space.
-/

instance : AddCommGroup QuarkDoublet := Equiv.addCommGroup valEquiv

instance : Module ℂ QuarkDoublet := Equiv.module ℂ valEquiv

/-- The linear equivalence between `QuarkDoublet` and its underlying tensor product space. -/
def valLinEquiv : QuarkDoublet ≃ₗ[ℂ]
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (q : QuarkDoublet) : valLinEquiv q = q.val := rfl

@[simp]
lemma valLinEquiv_symm_apply
    (m : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl
/-!

## Lorentz group representation

-/
open Matrix MatrixGroups

open Representation in
/-- The representation of the Lorentz group on the space of quark fields. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) QuarkDoublet where
  toFun Λ :=  valLinEquiv.symm ∘ₗ
      TensorProduct.map
      (TensorProduct.map (Fermion.LeftHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 3)) Λ))
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 2)) Λ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp [Module.End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    ext1 q
    simp [TensorProduct.map_map, ← TensorProduct.map_comp, Module.End.mul_eq_comp]

/-!

## The representation of the Standard Model gauge group

-/

/-- The action of the Standard Model gauge group on quark fields. -/
noncomputable def repGaugeGroup : Representation ℂ GaugeGroupI QuarkDoublet where
  toFun g := valLinEquiv.symm ∘ₗ
      TensorProduct.map
        (TensorProduct.map
        (LinearMap.id (M := Fermion.LeftHandedWeyl)) -- action on the Lorentz indices
        g.toSU3.1.toEuclideanLin) -- SU(3) action
        g.toSU2.1.toEuclideanLin  -- SU(2) action
      ∘ₗ LinearMap.lsmul ℂ _ (g.toU1 : ℂ) -- U(1) action
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp
  map_mul' g1 g2 := by
    ext q
    simp [smul_smul, mul_comm, TensorProduct.map_map, ← TensorProduct.map_comp]

TODO "Find the subgroup of the Standard Model gauge group which acts trivially on the
  quark doublet."

end QuarkDoublet

end StandardModel
