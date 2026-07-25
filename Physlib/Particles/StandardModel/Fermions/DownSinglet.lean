/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!
# Down-type singlets

## i. Overview

The Standard Model down-type singlet is a right-handed Weyl spinor in the `(3, 1)_{-2}`
representation. Here charges are normalized as `6Y`, so `-2` is the usual hypercharge
`Y = -1/3`.

`DownSinglet` is the target vector space of one down-type quark multiplet. Its Weyl factor
carries the Lorentz index and its three-dimensional factor carries the colour index. The absence
of a weak factor makes it an `SU(2)` singlet.

The Lorentz and gauge actions are first defined separately. The gauge action is then computed on a
basis, used to identify its kernel, and descended to each supported global form of the Standard
Model gauge group.

## ii. Key results

- `DownSinglet` : the target space of the `(3, 1)_{-2}` multiplet.
- `repLorentzGroup` : the right-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_tmul_basis_eq_sum` : the gauge action in a tensor-product basis.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.

## iii. Table of contents

- A. The down-singlet space
- B. Linear structure
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The down-singlet space

The Weyl factor carries the right-handed Lorentz index, while
`EuclideanSpace ℂ (Fin 3)` carries the colour index.
-/

/-- The target vector space of one Standard Model down-type singlet quark.
It carries the `(3, 1)_{-2}` representation of the gauge group. -/
@[ext]
structure DownSinglet where
  /-- The right-handed Weyl spinor with its colour index. -/
  val : Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3)

namespace DownSinglet

/-!

## B. Linear structure

`DownSinglet` wraps its tensor-product carrier as a distinct type. The equivalences below identify
the two types and transport the additive and complex module structures to `DownSinglet`.
-/

/-- Identifies a down-type singlet with its underlying tensor-product value. -/
def valEquiv : DownSinglet ≃ Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup DownSinglet := Equiv.addCommGroup valEquiv

instance : Module ℂ DownSinglet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : DownSinglet ≃ₗ[ℂ]
    Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (d : DownSinglet) : valLinEquiv d = d.val := rfl

lemma valLinEquiv_symm_apply
    (m : Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (d₁ d₂ : DownSinglet) : (d₁ + d₂).val = d₁.val + d₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (d : DownSinglet) : (r • d).val = r • d.val := rfl

/-!

## C. Lorentz action

The Lorentz group acts on the right-handed Weyl factor and leaves the colour index fixed.
-/

open Matrix MatrixGroups

open Representation in
/-- The right-handed Lorentz representation on down-type singlet quarks. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) DownSinglet where
  toFun Λ := valLinEquiv.symm ∘ₗ
      TensorProduct.map (Fermion.RightHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 3)) Λ) ∘ₗ
      valLinEquiv
  map_one' := by
    ext d
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 d
    simp [TensorProduct.map_map, Module.End.mul_eq_comp]

/-!

## D. Gauge action

The `SU(3)` component acts on the colour index, while the `SU(2)` component acts trivially. The
`U(1)` action is `star z ^ 2`; since `z` is unitary, `star z = z⁻¹`, so this represents charge
`-2`.

The tensor and basis formulas below expose the coefficients used to compare actions and compute the
kernel.
-/

/-- The `(3, 1)_{-2}` action of the unquotiented Standard Model gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI DownSinglet where
  toFun g := valLinEquiv.symm ∘ₗ
      TensorProduct.map
        (LinearMap.id (M := Fermion.RightHandedWeyl))
        g.toSU3.1.toEuclideanLin ∘ₗ
      LinearMap.lsmul ℂ _ (star g.toU1.1 ^ 2 : ℂ) ∘ₗ
      valLinEquiv
  map_one' := by
    ext d
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext d
    simp [smul_smul, mul_comm, TensorProduct.map_map, valLinEquiv_symm_apply]
    ring_nf

/-- The gauge action on a pure spinor–colour tensor. -/
lemma repGaugeGroupI_tmul (g : GaugeGroupI) (ψ : Fermion.RightHandedWeyl)
    (v : EuclideanSpace ℂ (Fin 3)) :
    repGaugeGroupI g ⟨ψ ⊗ₜ v⟩ =
      ⟨(star g.toU1.1 ^ 2) • ψ ⊗ₜ g.toSU3.1.toEuclideanLin v⟩ := rfl

end DownSinglet

end StandardModel
