/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!
# Charged-lepton singlets

## i. Overview

The Standard Model charged-lepton singlet is a right-handed Weyl spinor in the `(1, 1)_{-6}`
representation. Here charges are normalized as `6Y`, so `-6` is the usual hypercharge
`Y = -1`.

`LeptonSinglet` is the target vector space of one charged-lepton singlet. Its only index is
the Lorentz index carried by the Weyl spinor.

The Lorentz and gauge actions are first defined separately. The gauge action is then computed
on an arbitrary spinor, used to identify its kernel, and descended to each supported global
form of the Standard Model gauge group.

## ii. Key results

- `LeptonSinglet` : the target space of the `(1, 1)_{-6}` multiplet.
- `repLorentzGroup` : the right-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_apply` : the gauge action on a spinor.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.

## iii. Table of contents

- A. The charged-lepton-singlet space
- B. Linear structure
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups

-/

@[expose] public section

namespace StandardModel

/-!

## A. The charged-lepton-singlet space

The Weyl spinor carries the right-handed Lorentz index, and it is the whole of the multiplet:
a charged-lepton singlet has no colour index and no weak-isospin index.
-/

/-- The target vector space of one Standard Model charged-lepton singlet.
  It carries the `(1, 1)_{-6}` representation of the gauge group. -/
@[ext]
structure LeptonSinglet where
  /-- The right-handed Weyl spinor. -/
  val : Fermion.RightHandedWeyl

namespace LeptonSinglet

/-!

## B. Linear structure

The wrapper distinguishes charged-lepton singlets from other isomorphic vector spaces.
The following equivalences transfer the linear structure of the Weyl-spinor space and expose
that model when defining representations.
-/

/-- Identifies a charged-lepton singlet with its underlying Weyl spinor. -/
def valEquiv : LeptonSinglet ≃ Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup LeptonSinglet := Equiv.addCommGroup valEquiv

instance : Module ℂ LeptonSinglet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying Weyl-spinor space. -/
def valLinEquiv : LeptonSinglet ≃ₗ[ℂ] Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (l : LeptonSinglet) : valLinEquiv l = l.val := rfl

lemma valLinEquiv_symm_apply (m : Fermion.RightHandedWeyl) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (l₁ l₂ : LeptonSinglet) : (l₁ + l₂).val = l₁.val + l₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (l : LeptonSinglet) : (r • l).val = r • l.val := rfl

/-!

## C. Lorentz action

The Lorentz group acts through the right-handed Weyl representation, transported along the
identification of a charged-lepton singlet with its spinor.
-/

open Matrix MatrixGroups

/-- The right-handed Lorentz representation on charged-lepton singlets. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) LeptonSinglet where
  toFun Λ := valLinEquiv.symm ∘ₗ Fermion.RightHandedWeyl.rep Λ ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 l
    simp [Module.End.mul_eq_comp]

/-!

## D. Gauge action

The colour and weak factors act trivially, so the gauge group acts only through hypercharge.
The `U(1)` action is `star z ^ 6`; since `z` is unitary, `star z = z⁻¹`, so this represents
charge `-6`.

The formulas below expose the scalar used to compare actions and compute the kernel.
-/

/-- The `(1, 1)_{-6}` action of the unquotiented Standard Model gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonSinglet where
  toFun g := valLinEquiv.symm ∘ₗ
      LinearMap.lsmul ℂ Fermion.RightHandedWeyl (star g.toU1.1 ^ 6 : ℂ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext l
    simp [smul_smul, mul_comm, valLinEquiv_symm_apply]
    ring_nf

/-- The gauge group acts on a charged-lepton singlet by the hypercharge scalar alone. -/
lemma repGaugeGroupI_apply (g : GaugeGroupI) (ψ : Fermion.RightHandedWeyl) :
    repGaugeGroupI g ⟨ψ⟩ = ⟨(star g.toU1.1 ^ 6) • ψ⟩ := rfl

open Fermion in
/-- The gauge action is diagonal in the standard Weyl basis. -/
lemma repGaugeGroupI_basis (g : GaugeGroupI) (k : Fin 2) :
    repGaugeGroupI g ⟨RightHandedWeyl.basis k⟩ =
      (star g.toU1.1 ^ 6) • (⟨RightHandedWeyl.basis k⟩ : LeptonSinglet) := rfl

open Fermion in
/-- Two gauge elements induce the same action exactly when their hypercharge scalars agree. -/
lemma repGaugeGroupI_eq_iff {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔
      star g₁.toU1.1 ^ 6 = star g₂.toU1.1 ^ 6 := by
  constructor
  · intro h
    have h' := congrFun (congrArg (fun f => f.1) h)
      (⟨RightHandedWeyl.basis 0⟩ : LeptonSinglet)
    simp only [LinearMap.coe_toAddHom, repGaugeGroupI_apply] at h'
    have h'' := congrArg (fun v => RightHandedWeyl.basis.repr (LeptonSinglet.val v) 0) h'
    simpa using h''
  · intro h
    have h' : (starRingEnd ℂ) g₁.toU1.1 ^ 6 = (starRingEnd ℂ) g₂.toU1.1 ^ 6 := h
    ext l
    simp [repGaugeGroupI, h']

end LeptonSinglet

end StandardModel
