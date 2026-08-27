/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Automorphisms of the bounded operators

Reversible transformations of a quantum system act on its observable algebra by
⋆-automorphisms.

For a complex Hilbert space `H`, every ⋆-automorphism of `B(H)` is implemented by
unitary conjugation:
  `A ↦ U A U⋆`.

Two unitaries implement the same transformation exactly when they differ by a
scalar phase. Consequently,
  `Aut⋆(B(H)) ≅ U(H) / U(1) ≅ PU(H)`,
the projective unitary group.

For Hamiltonian dynamics, this projective ambiguity corresponds to
the freedom to shift a Hamiltonian by a scalar multiple of the identity.
-/

@[expose] public section

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every ⋆-automorphism of `B(H)` is implemented by unitary conjugation. -/
lemma conjStarAlgAut_surjective :
    Function.Surjective (Unitary.conjStarAlgAut ℂ (B(H))) := by
  intro φ
  obtain ⟨U, hU⟩ :=
    φ.eq_linearIsometryEquivConjStarAlgEquiv
      (NonUnitalStarAlgHom.isometry φ φ.injective).continuous
  refine ⟨Unitary.linearIsometryEquiv.symm U, ?_⟩
  rw [Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv]
  exact hU.symm

/-- Two unitaries implement the same ⋆-automorphism of `B(H)` exactly when they differ by a scalar
phase. -/
lemma conjStarAlgAut_eq_iff (u v : Unitary (B(H))) :
    Unitary.conjStarAlgAut ℂ (B(H)) u =
        Unitary.conjStarAlgAut ℂ (B(H)) v ↔
      ∃ c : unitary ℂ, u = c • v :=
  Unitary.conjStarAlgAut_ext_iff' u v

/-- The projective unitary group of `H`, obtained by quotienting out scalar phases. -/
def ProjectiveUnitary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :=
  Unitary (B(H)) ⧸ MonoidHom.ker (Unitary.conjStarAlgAut ℂ (B(H)))

noncomputable instance : Group (ProjectiveUnitary H) := QuotientGroup.Quotient.group _

/-- Reversible transformations of `B(H)` are precisely projective unitaries. -/
noncomputable def projectiveUnitaryEquivStarAlgAut :
    ProjectiveUnitary H ≃* ((B(H)) ≃⋆ₐ[ℂ] (B(H))) :=
  QuotientGroup.quotientKerEquivOfSurjective _ conjStarAlgAut_surjective

end OperatorAlgebra
