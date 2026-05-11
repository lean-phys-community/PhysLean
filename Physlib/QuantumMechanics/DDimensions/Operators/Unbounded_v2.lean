/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Mathematics.InnerProductSpace.Submodule
/-!

# Unbounded operators

-/

@[expose] public section

namespace LinearPMap

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {T T₁ T₂ : H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'}

/-!
## A. Definitions
-/

/-- A LinearPMap `U` has dense domain iff `U.domain` is dense in `H`. -/
def HasDenseDomain (U : H →ₗ.[ℂ] H') : Prop := Dense (U.domain : Set H)

lemma hasDenseDomain_def : U.HasDenseDomain ↔ Dense (U.domain : Set H) := Iff.rfl

/-- A LinearPMap is an unbounded operator iff it has dense domain and is closable. -/
def IsUnbounded (U : H →ₗ.[ℂ] H') : Prop := U.HasDenseDomain ∧ U.IsClosable

lemma isUnbounded_def : U.IsUnbounded ↔ U.HasDenseDomain ∧ U.IsClosable := Iff.rfl

/-- A LinearPMap `U` is symmetric iff `⟪U x, y⟫_ℂ = ⟪x, U y⟫_ℂ` for all `x y : U.domain`. -/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop := T.IsFormalAdjoint T

lemma isSymmetric_def : T.IsSymmetric ↔ T.IsFormalAdjoint T := Iff.rfl

/-- A LinearPMap is essentially self-adjoint iff its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint [CompleteSpace H] (T : H →ₗ.[ℂ] H) : Prop := IsSelfAdjoint T.closure

lemma isEssentiallySelfAdjoint_def [CompleteSpace H] :
    T.IsEssentiallySelfAdjoint ↔ IsSelfAdjoint T.closure := Iff.rfl

end LinearPMap
