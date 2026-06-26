/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Basic
public import Physlib.Meta.Linters.Sorry
public import Mathlib.RingTheory.RootsOfUnity.Complex
/-!
# The Standard Model

This file defines the basic properties of the standard model in particle physics.

-/

@[expose] public section

namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-!

## The unquotiented gauge group

-/

/-- The global gauge group of the Standard Model with no discrete quotients.
  The `I` in the Name is an indication of the statement that this has no discrete quotients. -/
abbrev GaugeGroupI : Type :=
  specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

namespace GaugeGroupI

/-- The underlying element of `SU(3)` of an element in `GaugeGroupI`. -/
def toSU3 : GaugeGroupI →* specialUnitaryGroup (Fin 3) ℂ where
  toFun g := g.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The underlying element of `SU(2)` of an element in `GaugeGroupI`. -/
def toSU2 : GaugeGroupI →* specialUnitaryGroup (Fin 2) ℂ where
  toFun g := g.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The underlying element of `U(1)` of an element in `GaugeGroupI`. -/
def toU1 : GaugeGroupI →* unitary ℂ where
  toFun g := g.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[ext]
lemma ext {g g' : GaugeGroupI} (hSU3 : toSU3 g = toSU3 g')
    (hSU2 : toSU2 g = toSU2 g') (hU1 : toU1 g = toU1 g') : g = g' := by
  rcases g with ⟨g1, g2, g3⟩
  cases g'
  simp only [toSU3, toSU2, toU1] at hSU3 hSU2 hU1
  simp_all

instance : Star GaugeGroupI where
  star g := (star g.1, star g.2.1, star g.2.2)

lemma star_eq (g : GaugeGroupI) : star g = (star g.1, star g.2.1, star g.2.2) := rfl

@[simp]
lemma star_toSU3 (g : GaugeGroupI) : toSU3 (star g) = star (toSU3 g) := rfl

@[simp]
lemma star_toSU2 (g : GaugeGroupI) : toSU2 (star g) = star (toSU2 g) := rfl

@[simp]
lemma star_toU1 (g : GaugeGroupI) : toU1 (star g) = star (toU1 g) := rfl

instance : InvolutiveStar GaugeGroupI where
  star_involutive g := by
    ext1 <;> simp

/-- The inclusion of a U(1) subgroup. -/
noncomputable def ofU1Subgroup (u1 : unitary ℂ) : GaugeGroupI :=
  (1,
  ⟨!![star (u1 ^ 3 : unitary ℂ), 0;0, (u1 ^ 3 : unitary ℂ)], by
    simp only [SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [conj_mul'], by
    simp only [RCLike.star_def, SetLike.mem_coe, MonoidHom.mem_mker, coe_detMonoidHom,
      det_fin_two_of, conj_mul', mul_zero, sub_zero]
    simp⟩, u1)

@[simp]
lemma ofU1Subgroup_toSU3 (u1 : unitary ℂ) :
    toSU3 (ofU1Subgroup u1) = 1 := rfl

@[simp]
lemma ofU1Subgroup_toSU2 (u1 : unitary ℂ) :
    toSU2 (ofU1Subgroup u1) = ⟨!![star (u1 ^ 3 : unitary ℂ), 0;0, (u1 ^ 3 : unitary ℂ)], by
    simp only [SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [conj_mul'], by
    simp only [RCLike.star_def, SetLike.mem_coe, MonoidHom.mem_mker, coe_detMonoidHom,
      det_fin_two_of, conj_mul', mul_zero, sub_zero]
    simp⟩ := rfl

@[simp]
lemma ofU1Subgroup_toU1 (u1 : unitary ℂ) :
    toU1 (ofU1Subgroup u1) = u1 := rfl
end GaugeGroupI

/-!

## The ℤ₆ quotient

-/

/-- The unitary complex number associated to a sixth root of unity. -/
noncomputable def gaugeGroupℤ₆UnitaryOfRoot (α : rootsOfUnity 6 ℂ) : unitary ℂ :=
  ⟨((α : ℂˣ) : ℂ), by
    have hα : ‖((α : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_mem_rootsOfUnity α.prop
    constructor
    · rw [RCLike.star_def, Complex.conj_mul', hα]
      norm_num
    · rw [RCLike.star_def, Complex.mul_conj', hα]
      norm_num⟩

@[simp]
lemma gaugeGroupℤ₆UnitaryOfRoot_coe (α : rootsOfUnity 6 ℂ) :
    (gaugeGroupℤ₆UnitaryOfRoot α : ℂ) = ((α : ℂˣ) : ℂ) := rfl

/-- The `SU(3)` scalar matrix associated to a sixth root of unity. -/
noncomputable def gaugeGroupℤ₆SU3OfRoot (α : rootsOfUnity 6 ℂ) :
    specialUnitaryGroup (Fin 3) ℂ :=
  let z : ℂ := ((α : ℂˣ) : ℂ)
  ⟨scalar (Fin 3) (z ^ 2), by
    rw [mem_specialUnitaryGroup_iff]
    have hz : ‖z‖ = 1 := by
      simpa [z] using Complex.norm_eq_one_of_mem_rootsOfUnity α.prop
    have hz2 : star (z ^ 2) * z ^ 2 = 1 := by
      rw [RCLike.star_def, Complex.conj_mul', Complex.norm_pow, hz]
      norm_num
    constructor
    · rw [mem_unitaryGroup_iff']
      rw [Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
      funext i
      simpa [Pi.star_def] using hz2
    · have hα : z ^ 6 = 1 := by
        simpa [z] using (mem_rootsOfUnity' 6 (α : ℂˣ)).mp α.prop
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three]
      calc
        z ^ 2 * z ^ 2 * z ^ 2 = z ^ 6 := by ring
        _ = 1 := hα⟩

/-- The `SU(2)` scalar matrix associated to a sixth root of unity. -/
noncomputable def gaugeGroupℤ₆SU2OfRoot (α : rootsOfUnity 6 ℂ) :
    specialUnitaryGroup (Fin 2) ℂ := by
  let u : unitary ℂ := gaugeGroupℤ₆UnitaryOfRoot α
  let z : ℂ := ((α : ℂˣ) : ℂ)
  let w : ℂ := star ((u ^ 3 : unitary ℂ) : ℂ)
  refine ⟨scalar (Fin 2) w, ?_⟩
  rw [mem_specialUnitaryGroup_iff]
  have hw : star w * w = 1 := by
    change star (star ((u ^ 3 : unitary ℂ) : ℂ)) *
      star ((u ^ 3 : unitary ℂ) : ℂ) = 1
    rw [star_star]
    exact (u ^ 3 : unitary ℂ).prop.2
  have hα : z ^ 6 = 1 := by
    simpa [z] using (mem_rootsOfUnity' 6 (α : ℂˣ)).mp α.prop
  have hw2 : w ^ 2 = 1 := by
    calc
      w ^ 2 = star (z ^ 6) := by
        simp [w, u, z, pow_succ]
        ring
      _ = 1 := by simp [hα]
  constructor
  · rw [mem_unitaryGroup_iff']
    rw [Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    simpa [Pi.star_def] using hw
  · rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
    simpa [pow_two] using hw2

/-- The element of `GaugeGroupI` associated to a sixth root of unity. -/
noncomputable def gaugeGroupℤ₆OfRoot (α : rootsOfUnity 6 ℂ) : GaugeGroupI :=
  (gaugeGroupℤ₆SU3OfRoot α, gaugeGroupℤ₆SU2OfRoot α, gaugeGroupℤ₆UnitaryOfRoot α)

@[simp]
lemma gaugeGroupℤ₆OfRoot_toSU3 (α : rootsOfUnity 6 ℂ) :
    GaugeGroupI.toSU3 (gaugeGroupℤ₆OfRoot α) = gaugeGroupℤ₆SU3OfRoot α := rfl

@[simp]
lemma gaugeGroupℤ₆OfRoot_toSU2 (α : rootsOfUnity 6 ℂ) :
    GaugeGroupI.toSU2 (gaugeGroupℤ₆OfRoot α) = gaugeGroupℤ₆SU2OfRoot α := rfl

@[simp]
lemma gaugeGroupℤ₆OfRoot_toU1 (α : rootsOfUnity 6 ℂ) :
    GaugeGroupI.toU1 (gaugeGroupℤ₆OfRoot α) = gaugeGroupℤ₆UnitaryOfRoot α := rfl

lemma gaugeGroupℤ₆OfRoot_mem_center (α : rootsOfUnity 6 ℂ) :
    gaugeGroupℤ₆OfRoot α ∈ Subgroup.center GaugeGroupI := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply GaugeGroupI.ext
  · change GaugeGroupI.toSU3 g * gaugeGroupℤ₆SU3OfRoot α =
      gaugeGroupℤ₆SU3OfRoot α * GaugeGroupI.toSU3 g
    ext i j
    simp [gaugeGroupℤ₆SU3OfRoot, Matrix.scalar_apply, mul_comm]
  · change GaugeGroupI.toSU2 g * gaugeGroupℤ₆SU2OfRoot α =
      gaugeGroupℤ₆SU2OfRoot α * GaugeGroupI.toSU2 g
    ext i j
    simp [gaugeGroupℤ₆SU2OfRoot, Matrix.scalar_apply, mul_comm]
  · change GaugeGroupI.toU1 g * gaugeGroupℤ₆UnitaryOfRoot α =
      gaugeGroupℤ₆UnitaryOfRoot α * GaugeGroupI.toU1 g
    exact mul_comm _ _

/-- The homomorphism from sixth roots of unity to `GaugeGroupI`. -/
noncomputable def gaugeGroupℤ₆Hom : rootsOfUnity 6 ℂ →* GaugeGroupI where
  toFun := gaugeGroupℤ₆OfRoot
  map_one' := by
    apply GaugeGroupI.ext
    · change gaugeGroupℤ₆SU3OfRoot 1 = 1
      ext i j
      simp [gaugeGroupℤ₆SU3OfRoot, Matrix.scalar_apply]
    · change gaugeGroupℤ₆SU2OfRoot 1 = 1
      ext i j
      simp [gaugeGroupℤ₆SU2OfRoot, gaugeGroupℤ₆UnitaryOfRoot, Matrix.scalar_apply]
    · change gaugeGroupℤ₆UnitaryOfRoot 1 = 1
      ext
      simp [gaugeGroupℤ₆UnitaryOfRoot]
  map_mul' α β := by
    apply GaugeGroupI.ext
    · change gaugeGroupℤ₆SU3OfRoot (α * β) =
        gaugeGroupℤ₆SU3OfRoot α * gaugeGroupℤ₆SU3OfRoot β
      ext i j
      simp [gaugeGroupℤ₆SU3OfRoot, Matrix.scalar_apply, pow_two, mul_left_comm, mul_comm]
    · change gaugeGroupℤ₆SU2OfRoot (α * β) =
        gaugeGroupℤ₆SU2OfRoot α * gaugeGroupℤ₆SU2OfRoot β
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gaugeGroupℤ₆SU2OfRoot, gaugeGroupℤ₆UnitaryOfRoot, Matrix.scalar_apply,
          pow_succ] <;>
        ring
    · change gaugeGroupℤ₆UnitaryOfRoot (α * β) =
        gaugeGroupℤ₆UnitaryOfRoot α * gaugeGroupℤ₆UnitaryOfRoot β
      ext
      simp [gaugeGroupℤ₆UnitaryOfRoot]

@[simp]
lemma gaugeGroupℤ₆Hom_apply (α : rootsOfUnity 6 ℂ) :
    gaugeGroupℤ₆Hom α = gaugeGroupℤ₆OfRoot α := rfl

@[simp]
lemma gaugeGroupℤ₆Hom_toSU3 (α : rootsOfUnity 6 ℂ) :
    GaugeGroupI.toSU3 (gaugeGroupℤ₆Hom α) = gaugeGroupℤ₆SU3OfRoot α := rfl

@[simp]
lemma gaugeGroupℤ₆Hom_toSU2 (α : rootsOfUnity 6 ℂ) :
    GaugeGroupI.toSU2 (gaugeGroupℤ₆Hom α) = gaugeGroupℤ₆SU2OfRoot α := rfl

@[simp]
lemma gaugeGroupℤ₆Hom_toU1 (α : rootsOfUnity 6 ℂ) :
    GaugeGroupI.toU1 (gaugeGroupℤ₆Hom α) = gaugeGroupℤ₆UnitaryOfRoot α := rfl

/-- The subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₆-subgroup of `GaugeGroupI` with elements `(α^2 * I₃, α^(-3) * I₂, α)`,
where `α` is a sixth complex root of unity.

See https://math.ucr.edu/home/baez/guts.pdf
-/
noncomputable def gaugeGroupℤ₆SubGroup : Subgroup GaugeGroupI :=
  gaugeGroupℤ₆Hom.range

lemma gaugeGroupℤ₆OfRoot_mem (α : rootsOfUnity 6 ℂ) :
    gaugeGroupℤ₆OfRoot α ∈ gaugeGroupℤ₆SubGroup :=
  ⟨α, rfl⟩

lemma mem_gaugeGroupℤ₆SubGroup_iff (g : GaugeGroupI) :
    g ∈ gaugeGroupℤ₆SubGroup ↔ ∃ α : rootsOfUnity 6 ℂ, gaugeGroupℤ₆OfRoot α = g := by
  simp [gaugeGroupℤ₆SubGroup]

lemma gaugeGroupℤ₆SubGroup_le_center :
    gaugeGroupℤ₆SubGroup ≤ Subgroup.center GaugeGroupI := by
  intro g hg
  rw [mem_gaugeGroupℤ₆SubGroup_iff] at hg
  rcases hg with ⟨α, rfl⟩
  exact gaugeGroupℤ₆OfRoot_mem_center α

instance gaugeGroupℤ₆SubGroup_normal : gaugeGroupℤ₆SubGroup.Normal where
  conj_mem n hn g := by
    have hn_center : n ∈ Subgroup.center GaugeGroupI := gaugeGroupℤ₆SubGroup_le_center hn
    have hcomm : g * n = n * g := (Subgroup.mem_center_iff.mp hn_center) g
    have hconj : g * n * g⁻¹ = n := by
      calc
        g * n * g⁻¹ = n * g * g⁻¹ := by rw [hcomm]
        _ = n := by simp [mul_assoc]
    simpa [hconj] using hn

/-- The smallest possible gauge group of the Standard Model, i.e., the quotient of `GaugeGroupI` by
the ℤ₆-subgroup `gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
def GaugeGroupℤ₆ : Type :=
  GaugeGroupI ⧸ gaugeGroupℤ₆SubGroup

noncomputable instance : Group GaugeGroupℤ₆ :=
  inferInstanceAs (Group (GaugeGroupI ⧸ gaugeGroupℤ₆SubGroup))

namespace GaugeGroupℤ₆

/-- The quotient map from `GaugeGroupI` to `GaugeGroupℤ₆`. -/
noncomputable def mk : GaugeGroupI →* GaugeGroupℤ₆ :=
  QuotientGroup.mk' gaugeGroupℤ₆SubGroup

@[simp]
lemma mk_gaugeGroupℤ₆OfRoot (α : rootsOfUnity 6 ℂ) :
    mk (gaugeGroupℤ₆OfRoot α) = 1 := by
  change ((gaugeGroupℤ₆OfRoot α : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₆SubGroup) = 1
  rw [QuotientGroup.eq_one_iff]
  exact gaugeGroupℤ₆OfRoot_mem α

end GaugeGroupℤ₆

/-!

## The ℤ₂ quotient

-/

/-- The inclusion of second roots of unity into sixth roots of unity. -/
noncomputable def gaugeGroupℤ₂RootToℤ₆Root : rootsOfUnity 2 ℂ →* rootsOfUnity 6 ℂ :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd (by norm_num : 2 ∣ 6))

/-- The element of `GaugeGroupI` associated to a second root of unity. -/
noncomputable def gaugeGroupℤ₂OfRoot (α : rootsOfUnity 2 ℂ) : GaugeGroupI :=
  gaugeGroupℤ₆OfRoot (gaugeGroupℤ₂RootToℤ₆Root α)

@[simp]
lemma gaugeGroupℤ₂OfRoot_toSU3 (α : rootsOfUnity 2 ℂ) :
    GaugeGroupI.toSU3 (gaugeGroupℤ₂OfRoot α) =
      gaugeGroupℤ₆SU3OfRoot (gaugeGroupℤ₂RootToℤ₆Root α) := rfl

@[simp]
lemma gaugeGroupℤ₂OfRoot_toSU2 (α : rootsOfUnity 2 ℂ) :
    GaugeGroupI.toSU2 (gaugeGroupℤ₂OfRoot α) =
      gaugeGroupℤ₆SU2OfRoot (gaugeGroupℤ₂RootToℤ₆Root α) := rfl

@[simp]
lemma gaugeGroupℤ₂OfRoot_toU1 (α : rootsOfUnity 2 ℂ) :
    GaugeGroupI.toU1 (gaugeGroupℤ₂OfRoot α) =
      gaugeGroupℤ₆UnitaryOfRoot (gaugeGroupℤ₂RootToℤ₆Root α) := rfl

lemma gaugeGroupℤ₂OfRoot_mem_center (α : rootsOfUnity 2 ℂ) :
    gaugeGroupℤ₂OfRoot α ∈ Subgroup.center GaugeGroupI :=
  gaugeGroupℤ₆OfRoot_mem_center (gaugeGroupℤ₂RootToℤ₆Root α)

/-- The homomorphism from second roots of unity to `GaugeGroupI`. -/
noncomputable def gaugeGroupℤ₂Hom : rootsOfUnity 2 ℂ →* GaugeGroupI :=
  gaugeGroupℤ₆Hom.comp gaugeGroupℤ₂RootToℤ₆Root

@[simp]
lemma gaugeGroupℤ₂Hom_apply (α : rootsOfUnity 2 ℂ) :
    gaugeGroupℤ₂Hom α = gaugeGroupℤ₂OfRoot α := rfl

@[simp]
lemma gaugeGroupℤ₂Hom_toSU3 (α : rootsOfUnity 2 ℂ) :
    GaugeGroupI.toSU3 (gaugeGroupℤ₂Hom α) =
      gaugeGroupℤ₆SU3OfRoot (gaugeGroupℤ₂RootToℤ₆Root α) := rfl

@[simp]
lemma gaugeGroupℤ₂Hom_toSU2 (α : rootsOfUnity 2 ℂ) :
    GaugeGroupI.toSU2 (gaugeGroupℤ₂Hom α) =
      gaugeGroupℤ₆SU2OfRoot (gaugeGroupℤ₂RootToℤ₆Root α) := rfl

@[simp]
lemma gaugeGroupℤ₂Hom_toU1 (α : rootsOfUnity 2 ℂ) :
    GaugeGroupI.toU1 (gaugeGroupℤ₂Hom α) =
      gaugeGroupℤ₆UnitaryOfRoot (gaugeGroupℤ₂RootToℤ₆Root α) := rfl

/-- The ℤ₂-subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₂-subgroup of `GaugeGroupI` derived from the ℤ₂ subgroup of
`gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
noncomputable def gaugeGroupℤ₂SubGroup : Subgroup GaugeGroupI :=
  gaugeGroupℤ₂Hom.range

lemma gaugeGroupℤ₂OfRoot_mem (α : rootsOfUnity 2 ℂ) :
    gaugeGroupℤ₂OfRoot α ∈ gaugeGroupℤ₂SubGroup :=
  ⟨α, rfl⟩

lemma mem_gaugeGroupℤ₂SubGroup_iff (g : GaugeGroupI) :
    g ∈ gaugeGroupℤ₂SubGroup ↔ ∃ α : rootsOfUnity 2 ℂ, gaugeGroupℤ₂OfRoot α = g := by
  simp [gaugeGroupℤ₂SubGroup]

lemma gaugeGroupℤ₂SubGroup_le_gaugeGroupℤ₆SubGroup :
    gaugeGroupℤ₂SubGroup ≤ gaugeGroupℤ₆SubGroup := by
  intro g hg
  rw [mem_gaugeGroupℤ₂SubGroup_iff] at hg
  rcases hg with ⟨α, rfl⟩
  exact gaugeGroupℤ₆OfRoot_mem (gaugeGroupℤ₂RootToℤ₆Root α)

lemma gaugeGroupℤ₂SubGroup_le_center :
    gaugeGroupℤ₂SubGroup ≤ Subgroup.center GaugeGroupI := by
  intro g hg
  rw [mem_gaugeGroupℤ₂SubGroup_iff] at hg
  rcases hg with ⟨α, rfl⟩
  exact gaugeGroupℤ₂OfRoot_mem_center α

instance gaugeGroupℤ₂SubGroup_normal : gaugeGroupℤ₂SubGroup.Normal where
  conj_mem n hn g := by
    have hn_center : n ∈ Subgroup.center GaugeGroupI := gaugeGroupℤ₂SubGroup_le_center hn
    have hcomm : g * n = n * g := (Subgroup.mem_center_iff.mp hn_center) g
    have hconj : g * n * g⁻¹ = n := by
      calc
        g * n * g⁻¹ = n * g * g⁻¹ := by rw [hcomm]
        _ = n := by simp [mul_assoc]
    simpa [hconj] using hn

/-- The gauge group of the Standard Model with a ℤ₂ quotient, i.e., the quotient of `GaugeGroupI` by
the ℤ₂-subgroup `gaugeGroupℤ₂SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
def GaugeGroupℤ₂ : Type :=
  GaugeGroupI ⧸ gaugeGroupℤ₂SubGroup

noncomputable instance : Group GaugeGroupℤ₂ :=
  inferInstanceAs (Group (GaugeGroupI ⧸ gaugeGroupℤ₂SubGroup))

namespace GaugeGroupℤ₂

/-- The quotient map from `GaugeGroupI` to `GaugeGroupℤ₂`. -/
noncomputable def mk : GaugeGroupI →* GaugeGroupℤ₂ :=
  QuotientGroup.mk' gaugeGroupℤ₂SubGroup

@[simp]
lemma mk_gaugeGroupℤ₂OfRoot (α : rootsOfUnity 2 ℂ) :
    mk (gaugeGroupℤ₂OfRoot α) = 1 := by
  change ((gaugeGroupℤ₂OfRoot α : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₂SubGroup) = 1
  rw [QuotientGroup.eq_one_iff]
  exact gaugeGroupℤ₂OfRoot_mem α

end GaugeGroupℤ₂

/-!

## The ℤ₃ quotient

-/

/-- The inclusion of third roots of unity into sixth roots of unity. -/
noncomputable def gaugeGroupℤ₃RootToℤ₆Root : rootsOfUnity 3 ℂ →* rootsOfUnity 6 ℂ :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd (by norm_num : 3 ∣ 6))

/-- The element of `GaugeGroupI` associated to a third root of unity. -/
noncomputable def gaugeGroupℤ₃OfRoot (α : rootsOfUnity 3 ℂ) : GaugeGroupI :=
  gaugeGroupℤ₆OfRoot (gaugeGroupℤ₃RootToℤ₆Root α)

@[simp]
lemma gaugeGroupℤ₃OfRoot_toSU3 (α : rootsOfUnity 3 ℂ) :
    GaugeGroupI.toSU3 (gaugeGroupℤ₃OfRoot α) =
      gaugeGroupℤ₆SU3OfRoot (gaugeGroupℤ₃RootToℤ₆Root α) := rfl

@[simp]
lemma gaugeGroupℤ₃OfRoot_toSU2 (α : rootsOfUnity 3 ℂ) :
    GaugeGroupI.toSU2 (gaugeGroupℤ₃OfRoot α) =
      gaugeGroupℤ₆SU2OfRoot (gaugeGroupℤ₃RootToℤ₆Root α) := rfl

@[simp]
lemma gaugeGroupℤ₃OfRoot_toU1 (α : rootsOfUnity 3 ℂ) :
    GaugeGroupI.toU1 (gaugeGroupℤ₃OfRoot α) =
      gaugeGroupℤ₆UnitaryOfRoot (gaugeGroupℤ₃RootToℤ₆Root α) := rfl

lemma gaugeGroupℤ₃OfRoot_mem_center (α : rootsOfUnity 3 ℂ) :
    gaugeGroupℤ₃OfRoot α ∈ Subgroup.center GaugeGroupI :=
  gaugeGroupℤ₆OfRoot_mem_center (gaugeGroupℤ₃RootToℤ₆Root α)

/-- The homomorphism from third roots of unity to `GaugeGroupI`. -/
noncomputable def gaugeGroupℤ₃Hom : rootsOfUnity 3 ℂ →* GaugeGroupI :=
  gaugeGroupℤ₆Hom.comp gaugeGroupℤ₃RootToℤ₆Root

@[simp]
lemma gaugeGroupℤ₃Hom_apply (α : rootsOfUnity 3 ℂ) :
    gaugeGroupℤ₃Hom α = gaugeGroupℤ₃OfRoot α := rfl

@[simp]
lemma gaugeGroupℤ₃Hom_toSU3 (α : rootsOfUnity 3 ℂ) :
    GaugeGroupI.toSU3 (gaugeGroupℤ₃Hom α) =
      gaugeGroupℤ₆SU3OfRoot (gaugeGroupℤ₃RootToℤ₆Root α) := rfl

@[simp]
lemma gaugeGroupℤ₃Hom_toSU2 (α : rootsOfUnity 3 ℂ) :
    GaugeGroupI.toSU2 (gaugeGroupℤ₃Hom α) =
      gaugeGroupℤ₆SU2OfRoot (gaugeGroupℤ₃RootToℤ₆Root α) := rfl

@[simp]
lemma gaugeGroupℤ₃Hom_toU1 (α : rootsOfUnity 3 ℂ) :
    GaugeGroupI.toU1 (gaugeGroupℤ₃Hom α) =
      gaugeGroupℤ₆UnitaryOfRoot (gaugeGroupℤ₃RootToℤ₆Root α) := rfl

/-- The ℤ₃-subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₃-subgroup of `GaugeGroupI` derived from the ℤ₃ subgroup of
`gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
noncomputable def gaugeGroupℤ₃SubGroup : Subgroup GaugeGroupI :=
  gaugeGroupℤ₃Hom.range

lemma gaugeGroupℤ₃OfRoot_mem (α : rootsOfUnity 3 ℂ) :
    gaugeGroupℤ₃OfRoot α ∈ gaugeGroupℤ₃SubGroup :=
  ⟨α, rfl⟩

lemma mem_gaugeGroupℤ₃SubGroup_iff (g : GaugeGroupI) :
    g ∈ gaugeGroupℤ₃SubGroup ↔ ∃ α : rootsOfUnity 3 ℂ, gaugeGroupℤ₃OfRoot α = g := by
  simp [gaugeGroupℤ₃SubGroup]

lemma gaugeGroupℤ₃SubGroup_le_gaugeGroupℤ₆SubGroup :
    gaugeGroupℤ₃SubGroup ≤ gaugeGroupℤ₆SubGroup := by
  intro g hg
  rw [mem_gaugeGroupℤ₃SubGroup_iff] at hg
  rcases hg with ⟨α, rfl⟩
  exact gaugeGroupℤ₆OfRoot_mem (gaugeGroupℤ₃RootToℤ₆Root α)

lemma gaugeGroupℤ₃SubGroup_le_center :
    gaugeGroupℤ₃SubGroup ≤ Subgroup.center GaugeGroupI := by
  intro g hg
  rw [mem_gaugeGroupℤ₃SubGroup_iff] at hg
  rcases hg with ⟨α, rfl⟩
  exact gaugeGroupℤ₃OfRoot_mem_center α

instance gaugeGroupℤ₃SubGroup_normal : gaugeGroupℤ₃SubGroup.Normal where
  conj_mem n hn g := by
    have hn_center : n ∈ Subgroup.center GaugeGroupI := gaugeGroupℤ₃SubGroup_le_center hn
    have hcomm : g * n = n * g := (Subgroup.mem_center_iff.mp hn_center) g
    have hconj : g * n * g⁻¹ = n := by
      calc
        g * n * g⁻¹ = n * g * g⁻¹ := by rw [hcomm]
        _ = n := by simp [mul_assoc]
    simpa [hconj] using hn

/-- The gauge group of the Standard Model with a ℤ₃-quotient, i.e., the quotient of `GaugeGroupI` by
the ℤ₃-subgroup `gaugeGroupℤ₃SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
def GaugeGroupℤ₃ : Type :=
  GaugeGroupI ⧸ gaugeGroupℤ₃SubGroup

noncomputable instance : Group GaugeGroupℤ₃ :=
  inferInstanceAs (Group (GaugeGroupI ⧸ gaugeGroupℤ₃SubGroup))

namespace GaugeGroupℤ₃

/-- The quotient map from `GaugeGroupI` to `GaugeGroupℤ₃`. -/
noncomputable def mk : GaugeGroupI →* GaugeGroupℤ₃ :=
  QuotientGroup.mk' gaugeGroupℤ₃SubGroup

@[simp]
lemma mk_gaugeGroupℤ₃OfRoot (α : rootsOfUnity 3 ℂ) :
    mk (gaugeGroupℤ₃OfRoot α) = 1 := by
  change ((gaugeGroupℤ₃OfRoot α : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₃SubGroup) = 1
  rw [QuotientGroup.eq_one_iff]
  exact gaugeGroupℤ₃OfRoot_mem α

end GaugeGroupℤ₃

/-!

## Gauge groups from quotient choices

-/

/-- Specifies the allowed quotients of `SU(3) x SU(2) x U(1)` which give a valid
  gauge group of the Standard Model. -/
inductive GaugeGroupQuot : Type
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₆`. -/
  | ℤ₆ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₂`. -/
  | ℤ₂ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₃`. -/
  | ℤ₃ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the full SM gauge group. -/
  | I : GaugeGroupQuot

/-- The (global) gauge group of the Standard Model given a choice of quotient, i.e., the map from
`GaugeGroupQuot` to `Type` which gives the gauge group of the Standard Model for a given choice of
quotient.

See https://math.ucr.edu/home/baez/guts.pdf
-/
def GaugeGroup : GaugeGroupQuot → Type
  | .ℤ₆ => GaugeGroupℤ₆
  | .ℤ₂ => GaugeGroupℤ₂
  | .ℤ₃ => GaugeGroupℤ₃
  | .I => GaugeGroupI

noncomputable instance (q : GaugeGroupQuot) : Group (GaugeGroup q) := by
  cases q <;> dsimp [GaugeGroup] <;> infer_instance

namespace GaugeGroupQuot

/-- The central subgroup of `GaugeGroupI` quotiented by a gauge-group quotient choice. -/
noncomputable def subgroup : GaugeGroupQuot → Subgroup GaugeGroupI
  | .ℤ₆ => gaugeGroupℤ₆SubGroup
  | .ℤ₂ => gaugeGroupℤ₂SubGroup
  | .ℤ₃ => gaugeGroupℤ₃SubGroup
  | .I => ⊥

/-- The subgroup attached to a gauge-group quotient choice lies in the center of `GaugeGroupI`. -/
lemma subgroup_le_center (q : GaugeGroupQuot) :
    subgroup q ≤ Subgroup.center GaugeGroupI := by
  cases q
  · exact gaugeGroupℤ₆SubGroup_le_center
  · exact gaugeGroupℤ₂SubGroup_le_center
  · exact gaugeGroupℤ₃SubGroup_le_center
  · intro g hg
    change g ∈ (⊥ : Subgroup GaugeGroupI) at hg
    rw [Subgroup.mem_bot] at hg
    simp [hg]

/-- The subgroup attached to a gauge-group quotient choice is normal in `GaugeGroupI`. -/
instance subgroup_normal (q : GaugeGroupQuot) : (subgroup q).Normal := by
  cases q
  · exact gaugeGroupℤ₆SubGroup_normal
  · exact gaugeGroupℤ₂SubGroup_normal
  · exact gaugeGroupℤ₃SubGroup_normal
  · change (⊥ : Subgroup GaugeGroupI).Normal
    infer_instance

/-- The quotient map from `GaugeGroupI` to the gauge group selected by a quotient choice. -/
noncomputable def quotientMap (q : GaugeGroupQuot) : GaugeGroupI →* GaugeGroup q :=
  match q with
  | .ℤ₆ => GaugeGroupℤ₆.mk
  | .ℤ₂ => GaugeGroupℤ₂.mk
  | .ℤ₃ => GaugeGroupℤ₃.mk
  | .I => MonoidHom.id GaugeGroupI

@[simp]
lemma quotientMap_I_apply (g : GaugeGroupI) :
    quotientMap .I g = g := rfl

@[simp]
lemma quotientMap_ℤ₆_gaugeGroupℤ₆OfRoot (α : rootsOfUnity 6 ℂ) :
    quotientMap .ℤ₆ (gaugeGroupℤ₆OfRoot α) = 1 :=
  GaugeGroupℤ₆.mk_gaugeGroupℤ₆OfRoot α

@[simp]
lemma quotientMap_ℤ₂_gaugeGroupℤ₂OfRoot (α : rootsOfUnity 2 ℂ) :
    quotientMap .ℤ₂ (gaugeGroupℤ₂OfRoot α) = 1 :=
  GaugeGroupℤ₂.mk_gaugeGroupℤ₂OfRoot α

@[simp]
lemma quotientMap_ℤ₃_gaugeGroupℤ₃OfRoot (α : rootsOfUnity 3 ℂ) :
    quotientMap .ℤ₃ (gaugeGroupℤ₃OfRoot α) = 1 :=
  GaugeGroupℤ₃.mk_gaugeGroupℤ₃OfRoot α

/-- The kernel of the quotient map is the subgroup selected by the quotient choice. -/
lemma mem_subgroup_iff_quotientMap_eq_one (q : GaugeGroupQuot) (g : GaugeGroupI) :
    g ∈ subgroup q ↔ quotientMap q g = 1 := by
  cases q
  · change g ∈ gaugeGroupℤ₆SubGroup ↔
      ((g : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₆SubGroup) = 1
    exact (QuotientGroup.eq_one_iff g).symm
  · change g ∈ gaugeGroupℤ₂SubGroup ↔
      ((g : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₂SubGroup) = 1
    exact (QuotientGroup.eq_one_iff g).symm
  · change g ∈ gaugeGroupℤ₃SubGroup ↔
      ((g : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₃SubGroup) = 1
    exact (QuotientGroup.eq_one_iff g).symm
  · change g ∈ (⊥ : Subgroup GaugeGroupI) ↔ (MonoidHom.id GaugeGroupI) g = 1
    simp

/-- Two representatives have the same image under the selected quotient map exactly when their
quotient lies in the subgroup selected by the quotient choice. -/
lemma quotientMap_eq_iff (q : GaugeGroupQuot) (g h : GaugeGroupI) :
    quotientMap q g = quotientMap q h ↔ g / h ∈ subgroup q := by
  cases q
  · change ((g : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₆SubGroup) =
      ((h : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₆SubGroup) ↔ g / h ∈ gaugeGroupℤ₆SubGroup
    exact QuotientGroup.eq_iff_div_mem
  · change ((g : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₂SubGroup) =
      ((h : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₂SubGroup) ↔ g / h ∈ gaugeGroupℤ₂SubGroup
    exact QuotientGroup.eq_iff_div_mem
  · change ((g : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₃SubGroup) =
      ((h : GaugeGroupI) : GaugeGroupI ⧸ gaugeGroupℤ₃SubGroup) ↔ g / h ∈ gaugeGroupℤ₃SubGroup
    exact QuotientGroup.eq_iff_div_mem
  · change g = h ↔ g / h ∈ (⊥ : Subgroup GaugeGroupI)
    rw [Subgroup.mem_bot, div_eq_one]

end GaugeGroupQuot

/-!

## Smoothness structure on the gauge group.

-/

/-- The gauge group `GaugeGroupI` is a Lie group. -/
informal_lemma gaugeGroupI_lie where
  deps := [``GaugeGroupI]
  tag := "6V2HL"

/-- For every `q` in `GaugeGroupQuot` the group `GaugeGroup q` is a Lie group. -/
informal_lemma gaugeGroup_lie where
  deps := [``GaugeGroup]
  tag := "6V2HR"

/-!

## Gauge bundles and transformations

-/

/-- The trivial principal bundle over SpaceTime with structure group `GaugeGroupI`. -/
informal_definition gaugeBundleI where
  deps := [``GaugeGroupI, ``SpaceTime]
  tag := "6V2HX"

/-- A global section of `gaugeBundleI`. -/
informal_definition gaugeTransformI where
  deps := [``gaugeBundleI]
  tag := "6V2H5"

end StandardModel
