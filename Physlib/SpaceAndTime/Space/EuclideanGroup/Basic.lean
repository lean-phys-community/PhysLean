/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean group

This file defines the Euclidean group as translations composed with orthogonal maps, together
with the special Euclidean group, translation subgroup, and rotation subgroups.

The affine group, together with the inclusion of the Euclidean group into it, is defined in
`Physlib.SpaceAndTime.Space.EuclideanGroup.AffineGroup`.
-/

@[expose] public section

/-- An n-dimensional `Euclidean group` is a group of
rotations, reflections, and translations.
-/
@[ext]
structure EuclideanGroup (n : ℕ) where
  /-- The translation part of a Euclidean transformation. -/
  translation : EuclideanSpace ℝ (Fin n)
  /-- The orthogonal linear part of a Euclidean transformation. -/
  linear : Matrix.orthogonalGroup (Fin n) ℝ

namespace EuclideanGroup

/-- Group structure on `E(n) = ℝ^n ⋊ O(n)`. The orthogonal component acts on translations by
the inherited matrix-vector action on `EuclideanSpace ℝ (Fin n)`, transported through `WithLp`
from the coordinate action `Q.val *ᵥ v.ofLp`. -/
noncomputable instance : Group (EuclideanGroup n) where
  mul A B := ⟨A.translation + A.linear • B.translation, A.linear * B.linear⟩
  mul_assoc A B C := by
    refine EuclideanGroup.ext ?_ ?_
    · show A.translation + A.linear • B.translation + (A.linear * B.linear) • C.translation
        = A.translation + A.linear • (B.translation + B.linear • C.translation)
      rw [mul_smul, smul_add, add_assoc]
    · exact mul_assoc A.linear B.linear C.linear
  one := ⟨0, 1⟩
  one_mul A := by
    refine EuclideanGroup.ext ?_ ?_
    · show 0 + (1 : Matrix.orthogonalGroup (Fin n) ℝ) • A.translation = A.translation
      rw [zero_add, one_smul]
    · exact one_mul A.linear
  mul_one A := by
    refine EuclideanGroup.ext ?_ ?_
    · show A.translation + A.linear • 0 = A.translation
      rw [smul_zero, add_zero]
    · exact mul_one A.linear
  inv A := ⟨A.linear⁻¹ • (-A.translation), A.linear⁻¹⟩
  inv_mul_cancel A := by
    refine EuclideanGroup.ext ?_ ?_
    · show A.linear⁻¹ • (-A.translation) + A.linear⁻¹ • A.translation = 0
      rw [← smul_add, neg_add_cancel, smul_zero]
    · exact inv_mul_cancel A.linear

/-! ### `One`/`Mul` projection lemmas

These expose the semidirect-product formulas behind the `Group` instance so that `simp` can
reduce the translation/linear components of `1` and `A * B`. -/

@[simp] lemma one_translation : (1 : EuclideanGroup n).translation = 0 := rfl

@[simp] lemma one_linear : (1 : EuclideanGroup n).linear = 1 := rfl

@[simp] lemma mul_translation (A B : EuclideanGroup n) :
    (A * B).translation = A.translation + A.linear • B.translation := rfl

@[simp] lemma mul_linear (A B : EuclideanGroup n) :
    (A * B).linear = A.linear * B.linear := rfl

private lemma det_coe_inv {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Q⁻¹).val.det = (Q.val.det)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← Matrix.det_mul, ← Submonoid.coe_mul, mul_inv_cancel,
    OneMemClass.coe_one, Matrix.det_one]

private lemma coe_inv {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Q⁻¹).val = (Q.val)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]

/-- Special Euclidean Group is the subgroup with det(Q) = 1 where Q ∈ O(n) -/
def SpecialEuclideanGroup (n : ℕ) : Subgroup (EuclideanGroup n) where
  carrier := {g | g.linear.val.det = 1}
  mul_mem' {a b} ha hb := by
    show (a.linear * b.linear).val.det = 1
    rw [Submonoid.coe_mul, Matrix.det_mul, ha, hb, one_mul]
  one_mem' := by
    show (1 : ↥(Matrix.orthogonalGroup (Fin n) ℝ)).val.det = 1
    rw [OneMemClass.coe_one, Matrix.det_one]
  inv_mem' {a} ha := by
    show (a.linear⁻¹).val.det = 1
    rw [det_coe_inv, ha, inv_one]

/-- The inclusion of the special Euclidean group into the Euclidean group. -/
noncomputable def SpecialEuclideanGroup.incl (n : ℕ) :
    SpecialEuclideanGroup n →* EuclideanGroup n := (SpecialEuclideanGroup n).subtype

/-- Translation is the subgroup with Q = 1. -/
def TranslationGroup (n : ℕ) : Subgroup (EuclideanGroup n) where
  carrier := {g | g.linear.val = 1}
  mul_mem' {a b} ha hb := by
    show (a.linear * b.linear).val = 1
    rw [Submonoid.coe_mul, ha, hb, one_mul]
  one_mem' := by
    show (1 : ↥(Matrix.orthogonalGroup (Fin n) ℝ)).val = 1
    rw [OneMemClass.coe_one]
  inv_mem' {a} ha := by
    show (a.linear⁻¹).val = 1
    rw [coe_inv, ha, inv_one]

/-- The inclusion of the translation subgroup into the Euclidean group. -/
noncomputable def TranslationGroup.incl (n : ℕ) :
    TranslationGroup n →* EuclideanGroup n := (TranslationGroup n).subtype

/-- MonoidHom including a translation vector into the Euclidean Group. -/
def translationVector.incl (n : ℕ) :
    Multiplicative (EuclideanSpace ℝ (Fin n)) →* EuclideanGroup n where
  toFun v := ⟨v.toAdd, 1⟩
  map_one' := by rfl
  map_mul' x y := by
    refine EuclideanGroup.ext ?_ ?_
    · show Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x +
          (1 : Matrix.orthogonalGroup (Fin n) ℝ) • Multiplicative.toAdd y
      simp
    · show 1 = 1 * 1
      simp [mul_one]

/-- An API feature: the translation vector inclusion image is the `TranslationGroup` carrier. -/
lemma translationVector.incl_range :
    Set.range (@translationVector.incl n) = (TranslationGroup n : Set (EuclideanGroup n)) := by
  ext g
  constructor
  · rintro ⟨v, hv⟩
    show g.linear.val = 1
    rw [← hv]
    rfl
  · intro h
    rw [Set.mem_range]
    refine ⟨g.translation, ?_⟩
    show (⟨g.translation, 1⟩ : EuclideanGroup n) = g
    refine EuclideanGroup.ext rfl ?_
    apply Subtype.ext
    simp [h.symm]

/-- The translation by the zero vector is the identity of the Euclidean group. -/
lemma translation_zero : translationVector.incl n
    (Multiplicative.ofAdd (0 : EuclideanSpace ℝ (Fin n))) = 1 := by
  simp

/-- The subgroup of `EuclideanGroup n` whose elements fix the origin
(translation = 0). This is the copy of `O(n)` sitting inside `E(n)`. -/
def OriginStabilizer (n : ℕ) : Subgroup (EuclideanGroup n) where
  carrier := {g | g.translation = 0}
  mul_mem' {a b} ha hb := by
    show a.translation + a.linear • b.translation = 0
    rw [ha, hb, smul_zero, zero_add]
  one_mem' := rfl
  inv_mem' {a} ha := by
    show a.linear⁻¹ • (-a.translation) = 0
    rw [ha, neg_zero, smul_zero]

/-- Rotation Group is the subgroup of E(n) consisting of rotations about the origin:
elements with `det = 1` (orientation-preserving) and `translation = 0` (origin-fixing). -/
noncomputable def RotationGroup (n : ℕ) : Subgroup (EuclideanGroup n) :=
  SpecialEuclideanGroup n ⊓ OriginStabilizer n

/-- The inclusion of the rotation subgroup into the Euclidean group. -/
noncomputable def RotationGroup.incl (n : ℕ) :
    RotationGroup n →* EuclideanGroup n := (RotationGroup n).subtype

variable {n} (p : EuclideanSpace ℝ (Fin n))
/-- The subgroup of rotation about a spatial point `p : EuclideanSpace ℝ (Fin n)` consists of
elements of the form T(p) * r * T(-p) with T(·) : translationVector.incl n (Multiplicative.ofAdd ·)
and r : RotationGroup where r is viewed as a rotation about the origin. Note T(-p) = T(p)⁻¹.
-/
noncomputable def RotationsAbout : Subgroup (EuclideanGroup n) where
  carrier := {g | ∃ r : RotationGroup n, g = translationVector.incl n (Multiplicative.ofAdd p)
    * (r : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd (-p))}
  mul_mem' {a b} ha hb := by
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    use r1 * r2
    rw [hr1, hr2]
    simp only [ofAdd_neg, map_inv, conj_mul, Subgroup.coe_mul]
  one_mem' := by
    simp; use 1
    constructor
    · simp
    · simp
  inv_mem' {a} ha := by
    obtain ⟨ra, hra⟩ := ha
    use ra⁻¹
    rw [hra]
    simp [mul_inv_rev, mul_assoc]

/-- The inclusion of rotations about `p` into the Euclidean group. -/
noncomputable def RotationsAbout.incl : RotationsAbout p →* EuclideanGroup n :=
  (RotationsAbout p).subtype

/-- Conjugate a rotation about `p` back to a rotation about the origin. -/
noncomputable def RotationsAbout.toOrigin :
    RotationsAbout p →* RotationGroup n where
  toFun g := ⟨translationVector.incl n (Multiplicative.ofAdd (-p))
    * (g : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd p), by
      obtain ⟨g, hg⟩ := g
      obtain ⟨r, hr⟩ := hg
      simp; rw [hr]; simp [mul_assoc]⟩
  map_one' := by simp
  map_mul' := by
    intro x y
    obtain ⟨a, ha⟩ := x
    obtain ⟨b, hb⟩ := y
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hr1, hr2]
    simp [mul_assoc]

/-- Conjugate a rotation about the origin to a rotation about `p`. -/
noncomputable def RotationsAbout.fromOrigin :
    RotationGroup n →* RotationsAbout p where
  toFun g := ⟨translationVector.incl n (Multiplicative.ofAdd p)
    * (g : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd (-p)), by use g⟩
  map_one' := by simp
  map_mul' := by
    intro x y
    obtain ⟨a, ha⟩ := x
    obtain ⟨b, hb⟩ := y
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    simp

/-- `RotationsAbout.toOrigin p` followed by `RotationsAbout.fromOrigin p` is the identity; the
forward leg of the isomorphism `RotationsAboutEquiv`. -/
lemma RotationsAbout.fromOrigin_comp_toOrigin :
    (RotationsAbout.fromOrigin p).comp (RotationsAbout.toOrigin p) =
      MonoidHom.id (RotationsAbout p) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, SetLike.coe_eq_coe]
  unfold RotationsAbout.toOrigin
  unfold RotationsAbout.fromOrigin
  simp [mul_assoc]

/-- `RotationsAbout.fromOrigin p` followed by `RotationsAbout.toOrigin p` is the identity; the
backward leg of the isomorphism `RotationsAboutEquiv`. -/
lemma RotationsAbout.toOrigin_comp_fromOrigin :
    (RotationsAbout.toOrigin p).comp (RotationsAbout.fromOrigin p) =
      MonoidHom.id (RotationGroup n) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, SetLike.coe_eq_coe]
  unfold RotationsAbout.toOrigin
  unfold RotationsAbout.fromOrigin
  simp [mul_assoc]

/-- API feature: conjugation by the translation `T(p)` exhibits the rotations about `p` as
isomorphic to the rotations about the origin `RotationGroup n`. -/
noncomputable def RotationsAboutEquiv : RotationsAbout p ≃* RotationGroup n :=
  MonoidHom.toMulEquiv (RotationsAbout.toOrigin p) (RotationsAbout.fromOrigin p)
    (RotationsAbout.fromOrigin_comp_toOrigin p) (RotationsAbout.toOrigin_comp_fromOrigin p)

/-- API feature: the degenerate identity that `RotationsAbout 0 = RotationGroup n` -/
lemma RotationsAbout_zero : RotationsAbout (0 : EuclideanSpace ℝ (Fin n)) = RotationGroup n := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    obtain ⟨g1, hg1⟩ := hg
    simp at hg1
    rw [hg1]
    simp
  · intro hg
    use ⟨g, hg⟩
    simp
/-- Rotations are members of special orthogonal groups and can be viewed as members of
orthogonal groups. -/
def specialOrthogonal.incl (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →* Matrix.orthogonalGroup (Fin n) ℝ :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

/-- The Euclidean group element given by a rotation about the origin (zero translation). -/
def ofRotation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    EuclideanGroup n := ⟨0, specialOrthogonal.incl n Q⟩

/-- Specialization to a group element from a rotation and a translation. -/
def ofRotationTranslation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) : EuclideanGroup n :=
  ⟨t, specialOrthogonal.incl n Q⟩

/-- The specialization projects back to the translation component. -/
@[simp]
lemma ofRotationTranslation_translation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    (ofRotationTranslation Q t).translation = t := rfl

/-- The specialization projects back to the linear (rotation) component. -/
@[simp]
lemma ofRotationTranslation_linear (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    (ofRotationTranslation Q t).linear = specialOrthogonal.incl n Q := rfl

/-- API feature: the inclusion image decomposes as group product. -/
@[simp]
lemma ofRotationTranslation_decompose (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    (ofRotationTranslation Q t) =
    (translationVector.incl n (Multiplicative.ofAdd t)) * (ofRotation (Q)) := by
  refine EuclideanGroup.ext ?_ ?_
  · show t = t + (1 : Matrix.orthogonalGroup (Fin n) ℝ) • 0
    rw [smul_zero, add_zero]
  · show specialOrthogonal.incl n Q = 1 * specialOrthogonal.incl n Q
    rw [one_mul]

/-- The isomorphism's forward map: a special orthogonal matrix as a rotation about the origin. -/
noncomputable def specialOrthogonal.toRotation (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →* RotationGroup n where
  toFun g := ⟨ofRotation g, by
      refine ⟨?_, ?_⟩
      · show (ofRotation g).linear.val.det = 1
        exact (Matrix.mem_specialOrthogonalGroup_iff.mp g.property).right
      · show (ofRotation g).translation = 0
        rfl⟩
  map_one' := rfl
  map_mul' x y := by
    apply Subtype.ext
    refine EuclideanGroup.ext ?_ ?_
    · show (0 : EuclideanSpace ℝ (Fin n)) =
        0 + (specialOrthogonal.incl n x : Matrix.orthogonalGroup (Fin n) ℝ) • 0
      rw [smul_zero, add_zero]
    · show specialOrthogonal.incl n (x * y)
          = specialOrthogonal.incl n x * specialOrthogonal.incl n y
      rw [map_mul]

/-- The isomorphism's inverse map: the linear part of a rotation about the origin, as a special
orthogonal matrix. -/
noncomputable def specialOrthogonal.fromRotation (n : ℕ) :
    RotationGroup n →* Matrix.specialOrthogonalGroup (Fin n) ℝ where
  toFun g := ⟨g.val.linear, ⟨g.val.linear.property,(g.property).left⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `specialOrthogonal.toRotation n` followed by `specialOrthogonal.fromRotation n` is the identity;
the forward leg of the isomorphism `specialOrthogonalEquiv`. -/
lemma specialOrthogonal.fromRotation_comp_toRotation :
    (specialOrthogonal.fromRotation n).comp (specialOrthogonal.toRotation n) =
      MonoidHom.id (Matrix.specialOrthogonalGroup (Fin n) ℝ) := by
  apply MonoidHom.ext
  intro x
  rfl

/-- `specialOrthogonal.fromRotation n` followed by `specialOrthogonal.toRotation n` is the identity;
the backward leg of the isomorphism `specialOrthogonalEquiv`. -/
lemma specialOrthogonal.toRotation_comp_fromRotation :
    (specialOrthogonal.toRotation n).comp (specialOrthogonal.fromRotation n) =
      MonoidHom.id (RotationGroup n) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  refine EuclideanGroup.ext ?_ ?_
  · show (0 : EuclideanSpace ℝ (Fin n)) = x.val.translation
    have h : x.val.translation = 0 := x.property.right
    rw [h]
  · rfl

/-- API feature: SO(n) ≃* RotationGroup n -/
noncomputable def specialOrthogonalEquiv :
    Matrix.specialOrthogonalGroup (Fin n) ℝ ≃* RotationGroup n :=
    MonoidHom.toMulEquiv (specialOrthogonal.toRotation n) (specialOrthogonal.fromRotation n)
    specialOrthogonal.fromRotation_comp_toRotation specialOrthogonal.toRotation_comp_fromRotation

end EuclideanGroup
