/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Jordan
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Complex.Module

/-!

# Lie structure on observables

The observables of a complex C⋆-algebra carry the Lie bracket

    ⁅a, b⁆ = -(i / 2) (ab - ba),

equivalently the imaginary part of their product.

Together with the Jordan product, this gives the antisymmetric and symmetric
parts of observable multiplication. The Lie bracket measures noncommutativity
and governs infinitesimal unitary dynamics.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*} [OperatorAlgebra A]

namespace Observable

/-! ## Lie bracket -/

/-- The observable Lie bracket is the imaginary part of the algebra product. -/
noncomputable instance instBracket :
    Bracket (Observable A) (Observable A) :=
  ⟨fun a b => imaginaryPart ((a : A) * (b : A))⟩

@[simp]
lemma coe_bracket (a b : Observable A) :
    ((⁅a, b⁆ : Observable A) : A) =
      (-(Complex.I / 2)) • ((a : A) * b - (b : A) * a) := by
  change
    (↑(imaginaryPart ((a : A) * (b : A))) : A) =
      (-(Complex.I / 2)) • ((a : A) * b - (b : A) * a)
  rw [imaginaryPart_apply_coe, star_mul, a.property.star_eq, b.property.star_eq]
  module

/-- The product of two observables is observable exactly when they commute. -/
lemma isSelfAdjoint_mul_iff_commute (a b : Observable A) :
    IsSelfAdjoint ((a : A) * (b : A)) ↔ Commute (a : A) (b : A) := by
  rw [isSelfAdjoint_iff, star_mul, a.property.star_eq, b.property.star_eq,
    commute_iff_eq, eq_comm]

/-- The ambient product of two observables splits into its Jordan and Lie parts. -/
lemma mul_decomposition (a b : Observable A) :
    (a : A) * b = (a ⊙ b : A) + Complex.I • ((⁅a, b⁆ : Observable A) : A) := by
  change (a : A) * b =
    ↑(realPart ((a : A) * (b : A))) +
      Complex.I • ↑(imaginaryPart ((a : A) * (b : A)))
  exact (realPart_add_I_smul_imaginaryPart ((a : A) * (b : A))).symm

/-! ## Lie ring -/

lemma add_bracket (a b c : Observable A) :
    ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ := by
  change
    imaginaryPart (((a + b : Observable A) : A) * (c : A)) =
      imaginaryPart ((a : A) * (c : A)) +
        imaginaryPart ((b : A) * (c : A))
  rw [AddSubgroup.coe_add, add_mul, map_add]

lemma bracket_add (a b c : Observable A) :
    ⁅a, b + c⁆ = ⁅a, b⁆ + ⁅a, c⁆ := by
  change
    imaginaryPart ((a : A) * ((b + c : Observable A) : A)) =
      imaginaryPart ((a : A) * (b : A)) +
        imaginaryPart ((a : A) * (c : A))
  rw [AddSubgroup.coe_add, mul_add, map_add]

lemma bracket_self (a : Observable A) :
    ⁅a, a⁆ = 0 := by
  apply Subtype.ext
  simp [coe_bracket]

lemma leibniz_bracket (a b c : Observable A) :
    ⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ + ⁅b, ⁅a, c⁆⁆ := by
  let _ : LieRing A := LieRing.ofAssociativeRing
  apply Subtype.ext
  rw [AddSubgroup.coe_add]
  let s : ℂ := -(Complex.I / 2)
  simp only [coe_bracket]
  change
    s • ⁅(a : A), s • ⁅(b : A), (c : A)⁆⁆ =
      s • ⁅s • ⁅(a : A), (b : A)⁆, (c : A)⁆ +
        s • ⁅(b : A), s • ⁅(a : A), (c : A)⁆⁆
  rw [lie_smul, smul_lie, lie_smul, smul_smul, smul_smul, smul_smul,
    ← smul_add, leibniz_lie]

noncomputable instance instLieRing :
    LieRing (Observable A) where
  add_lie := add_bracket
  lie_add := bracket_add
  lie_self := bracket_self
  leibniz_lie := leibniz_bracket

/-! ## Real Lie algebra -/

lemma bracket_smul (t : ℝ) (a b : Observable A) :
    ⁅a, t • b⁆ = t • ⁅a, b⁆ := by
  change
    imaginaryPart ((a : A) * ((t • b : Observable A) : A)) =
      t • imaginaryPart ((a : A) * (b : A))
  rw [selfAdjoint.val_smul, mul_smul_comm]
  exact map_smul (imaginaryPart : A →ₗ[ℝ] Observable A) t ((a : A) * (b : A))

noncomputable instance instLieAlgebra :
    LieAlgebra ℝ (Observable A) where
  toModule := inferInstance
  lie_smul := bracket_smul

/-! ## Elementary identities -/

@[simp]
lemma bracket_one_right (a : Observable A) :
    ⁅a, (1 : Observable A)⁆ = 0 := by
  apply Subtype.ext
  rw [coe_bracket]
  simp

@[simp]
lemma bracket_one_left (a : Observable A) :
    ⁅(1 : Observable A), a⁆ = 0 := by
  apply Subtype.ext
  rw [coe_bracket]
  simp

end Observable

end OperatorAlgebra
