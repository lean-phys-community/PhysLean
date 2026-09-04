/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Basic
public import Physlib.Meta.TODO.Basic
public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.LinearAlgebra.Complex.Module

/-!

# Jordan structure on observables

The observables of a complex C⋆-algebra carry the symmetrized product

    a ⊙ b = 1/2 (ab + ba),

equivalently the real part of their algebra product.

This product is commutative and satisfies the Jordan identity. The type
`JordanObservable A` equips the real vector space of observables with this
product as its multiplication, giving a commutative Jordan algebra.

-/

TODO "Investigate `https://github.com/Cobord/JordanAlgebra/` and determine
  which general Jordan-algebra results are relevant for quantum mechanics."

@[expose] public section

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

namespace Observable

/-- The symmetrized product of two observables. -/
noncomputable def jordan (a b : Observable A) : Observable A :=
  realPart ((a : A) * (b : A))

/-- The Jordan product on observables. -/
scoped[OperatorAlgebra] infixl:70 " ⊙ " => Observable.jordan

lemma coe_jordan (a b : Observable A) :
    (a ⊙ b : A) = (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a) := by
  change (↑(realPart ((a : A) * (b : A))) : A) =
    (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a)
  rw [realPart_apply_coe, star_mul, a.property.star_eq, b.property.star_eq]

lemma jordan_comm (a b : Observable A) :
    a ⊙ b = b ⊙ a := by
  apply Subtype.ext
  simp [coe_jordan, add_comm]

lemma jordan_self (a : Observable A) :
    (a ⊙ a : A) = (a : A) * a := by
  rw [coe_jordan]
  module

lemma add_jordan (a b c : Observable A) :
    (a + b) ⊙ c = a ⊙ c + b ⊙ c := by
  change realPart (((a + b : Observable A) : A) * (c : A)) =
    realPart ((a : A) * (c : A)) + realPart ((b : A) * (c : A))
  rw [AddSubgroup.coe_add, add_mul, map_add]

lemma jordan_add (a b c : Observable A) :
    a ⊙ (b + c) = a ⊙ b + a ⊙ c := by
  change realPart ((a : A) * ((b + c : Observable A) : A)) =
    realPart ((a : A) * (b : A)) + realPart ((a : A) * (c : A))
  rw [AddSubgroup.coe_add, mul_add, map_add]

lemma jordan_smul (t : ℝ) (a b : Observable A) :
    a ⊙ (t • b) = t • (a ⊙ b) := by
  change realPart ((a : A) * ((t • b : Observable A) : A)) =
    t • realPart ((a : A) * (b : A))
  rw [selfAdjoint.val_smul, mul_smul_comm]
  exact map_smul (realPart : A →ₗ[ℝ] Observable A) t ((a : A) * (b : A))

lemma jordan_identity (a b : Observable A) :
    (a ⊙ b) ⊙ (a ⊙ a) = a ⊙ (b ⊙ (a ⊙ a)) := by
  apply Subtype.ext
  simp only [coe_jordan, smul_add]
  norm_num [← smul_add]
  noncomm_ring

end Observable

/-! ## Jordan observables

`JordanObservable A` is a separate copy of `Observable A` whose multiplication is the Jordan
product.
-/

/-- An observable regarded as an element of the Jordan algebra. -/
noncomputable def JordanObservable (A : Type*) [OperatorAlgebra A] :=
  Observable A

namespace JordanObservable

variable {A : Type*} [OperatorAlgebra A]

noncomputable instance instAddCommGroup : AddCommGroup (JordanObservable A) :=
  inferInstanceAs (AddCommGroup (Observable A))

noncomputable instance instModule : Module ℝ (JordanObservable A) :=
  inferInstanceAs (Module ℝ (Observable A))

open scoped Observable

noncomputable instance instNonUnitalNonAssocCommRing :
    NonUnitalNonAssocCommRing (JordanObservable A) where
  mul a b := a ⊙ b
  mul_comm a b := Observable.jordan_comm a b
  left_distrib a b c := Observable.jordan_add a b c
  right_distrib a b c := Observable.add_jordan a b c
  zero_mul a := by
    change (0 : Observable A) ⊙ a = 0
    simp [Observable.jordan]
  mul_zero a := by
    change a ⊙ (0 : Observable A) = 0
    simp [Observable.jordan]

noncomputable instance instIsCommJordan :
    IsCommJordan (JordanObservable A) where
  lmul_comm_rmul_rmul a b := by
    change (a ⊙ b) ⊙ (a ⊙ a) = a ⊙ (b ⊙ (a ⊙ a))
    exact Observable.jordan_identity a b

end JordanObservable

end OperatorAlgebra
