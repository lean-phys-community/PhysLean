/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Physlib.Meta.TODO.Basic
/-!

## Modules associated with Fermions

Weyl fermions live in the vector space `ℂ^2`, defined here as `Fin 2 → ℂ`.
However if we simply define the Module of Weyl fermions as `Fin 2 → ℂ` we get casting problems,
where e.g. left-handed fermions can be cast to right-handed fermions etc.
To overcome this, for each type of Weyl fermion we define a structure that wraps `Fin 2 → ℂ`,
and these structures we define the instance of a module. This prevents casting between different
types of fermions.


-/

@[expose] public section

namespace Fermion
noncomputable section

TODO "Make a directory in ./Physlib/Relativity called Fermions for these files.
  Make this file (currently ..../Modules.lean) the Basic file, and include the basic module
  definitions for the different types of Weyl fermions."

section LeftHanded

/-- The module in which left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure LeftHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace LeftHandedWeyl

/-- The equivalence between `LeftHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : LeftHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid LeftHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup LeftHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ LeftHandedWeyl := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `LeftHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : LeftHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `LeftHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : LeftHandedWeyl) := toFin2ℂEquiv ψ

end LeftHandedWeyl

end LeftHanded

/-- The module in which dual-left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure DualLeftHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace DualLeftHandedWeyl

/-- The equivalence between `DualLeftHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : DualLeftHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid DualLeftHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup DualLeftHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ DualLeftHandedWeyl := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `DualLeftHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : DualLeftHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `DualLeftHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : DualLeftHandedWeyl) := toFin2ℂEquiv ψ

end DualLeftHandedWeyl


section RightHanded

/-- The module in which right handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure RightHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace RightHandedWeyl

/-- The equivalence between `RightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : RightHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid RightHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup RightHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ RightHandedWeyl := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `RightHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : RightHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `RightHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : RightHandedWeyl) := toFin2ℂEquiv ψ

end RightHandedWeyl

end RightHanded

section DualRightHanded

/-- The module in which dual-right handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure DualRightHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace DualRightHandedWeyl

/-- The equivalence between `DualRightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : DualRightHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid DualRightHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup DualRightHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ DualRightHandedWeyl := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `DualRightHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : DualRightHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `DualRightHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : DualRightHandedWeyl) := toFin2ℂEquiv ψ

end DualRightHandedWeyl

end DualRightHanded

end
end Fermion
