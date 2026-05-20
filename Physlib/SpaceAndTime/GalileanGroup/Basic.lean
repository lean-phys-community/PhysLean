/-
Copyright (c) 2026 Zuo Zhidong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zuo Zhidong
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Physlib.SpaceAndTime.Space.Basic
public import Physlib.SpaceAndTime.Time.Basic
/-!
# The Galilean group

## i. Overview

In this module we define the type `GalileanGroup d`, whose elements are
Galilean transformations in `d` spatial dimensions. A Galilean transformation
is a kinematic symmetry of non-relativistic spacetime, built from four
independent pieces:

* a spatial rotation (or reflection) `R ∈ O(d)`,
* a boost velocity `v` (the relative velocity between two inertial frames),
* a spatial translation `a`,
* a time translation `b`.

On coordinates it acts as
```
t' = t + b
x' = R x + v t + a
```
so the action on `Time × Space d` reads
`(t, x) ↦ (t + b, R x + v t + a)`.

This file is the **first-step** API: it provides only the data type, four
"pure" constructors, the identity, and the coordinate action together with
its core `simp` lemmas. Subsequent PRs will add the group law, the inverse,
the smooth/Lie-group structure, subgroup inclusions, and actions on fields.
The current API is designed so those additions are non-breaking.

## ii. Key results

- `GalileanGroup` : The type of Galilean transformations in `d` spatial
  dimensions.
- `GalileanGroup.apply` : The action of a Galilean transformation on a
  point `(t, x) : Time × Space d`.
- `GalileanGroup.pureRotation`, `pureBoost`, `pureSpaceTranslation`,
  `pureTimeTranslation` : Smart constructors for the four kinematic
  building blocks.
- `GalileanGroup.id` : The identity Galilean transformation.

## iii. Table of contents

- A. The type `GalileanGroup`
- B. The identity and basic constructors
  - B.1. The identity
  - B.2. Pure rotations
  - B.3. Pure boosts
  - B.4. Pure spatial translations
  - B.5. Pure time translations
- C. The action on `Time × Space d`
  - C.1. The coordinate formulas
  - C.2. Action of the identity
  - C.3. Action of pure rotations
  - C.4. Action of pure boosts
  - C.5. Action of pure spatial translations
  - C.6. Action of pure time translations

## iv. References

- *Classical Mechanics*, Goldstein, Poole, Safko — §1.7 (Galilean
  transformations as a kinematic symmetry).
- *Foundations of Mechanics*, Abraham–Marsden — Ch. 4 (the Galilean group
  as the symmetry group of Newtonian spacetime).

-/

@[expose] public section

noncomputable section

/-!

## A. The type `GalileanGroup`

-/

/-- A `Galilean transformation` in `d` spatial dimensions. It bundles
the four independent pieces of data
`(rotation, boost velocity, spatial translation, time translation)`, and
acts on `(t, x) : Time × Space d` by
`(t, x) ↦ (t + b, R x + v t + a)`.

The default value of `d` is `3`, so `GalileanGroup = GalileanGroup 3`. -/
structure GalileanGroup (d : ℕ := 3) where
  /-- The spatial rotation (or reflection): an element of the full
  orthogonal group `O(d)`. Using `O(d)` rather than `SO(d)` so that
  parity transformations are included in the first-version API. -/
  rotation : Matrix.orthogonalGroup (Fin d) ℝ
  /-- The boost velocity (the relative velocity between two inertial
  frames). -/
  velocity : EuclideanSpace ℝ (Fin d)
  /-- The spatial translation. -/
  spaceTranslation : EuclideanSpace ℝ (Fin d)
  /-- The time translation. -/
  timeTranslation : Time

namespace GalileanGroup

variable {d : ℕ}

/-!

## B. The identity and basic constructors

-/

/-!

### B.1. The identity

-/

/-- The identity Galilean transformation: no rotation, no boost,
no spatial translation, no time translation. -/
def id : GalileanGroup d :=
  ⟨1, 0, 0, 0⟩

instance : Inhabited (GalileanGroup d) := ⟨id⟩

@[simp]
lemma id_rotation : (id : GalileanGroup d).rotation = 1 := rfl

@[simp]
lemma id_velocity : (id : GalileanGroup d).velocity = 0 := rfl

@[simp]
lemma id_spaceTranslation : (id : GalileanGroup d).spaceTranslation = 0 := rfl

@[simp]
lemma id_timeTranslation : (id : GalileanGroup d).timeTranslation = 0 := rfl

/-!

### B.2. Pure rotations

-/

/-- The Galilean transformation that is a pure rotation by `R`. -/
def pureRotation (R : Matrix.orthogonalGroup (Fin d) ℝ) : GalileanGroup d :=
  ⟨R, 0, 0, 0⟩

@[simp]
lemma pureRotation_rotation (R : Matrix.orthogonalGroup (Fin d) ℝ) :
    (pureRotation R).rotation = R := rfl

@[simp]
lemma pureRotation_velocity (R : Matrix.orthogonalGroup (Fin d) ℝ) :
    (pureRotation R).velocity = 0 := rfl

@[simp]
lemma pureRotation_spaceTranslation (R : Matrix.orthogonalGroup (Fin d) ℝ) :
    (pureRotation R).spaceTranslation = 0 := rfl

@[simp]
lemma pureRotation_timeTranslation (R : Matrix.orthogonalGroup (Fin d) ℝ) :
    (pureRotation R).timeTranslation = 0 := rfl

/-!

### B.3. Pure boosts

-/

/-- The Galilean transformation that is a pure boost of velocity `v`. -/
def pureBoost (v : EuclideanSpace ℝ (Fin d)) : GalileanGroup d :=
  ⟨1, v, 0, 0⟩

@[simp]
lemma pureBoost_rotation (v : EuclideanSpace ℝ (Fin d)) :
    (pureBoost v).rotation = 1 := rfl

@[simp]
lemma pureBoost_velocity (v : EuclideanSpace ℝ (Fin d)) :
    (pureBoost v).velocity = v := rfl

@[simp]
lemma pureBoost_spaceTranslation (v : EuclideanSpace ℝ (Fin d)) :
    (pureBoost v).spaceTranslation = 0 := rfl

@[simp]
lemma pureBoost_timeTranslation (v : EuclideanSpace ℝ (Fin d)) :
    (pureBoost v).timeTranslation = 0 := rfl

/-!

### B.4. Pure spatial translations

-/

/-- The Galilean transformation that is a pure spatial translation by `a`. -/
def pureSpaceTranslation (a : EuclideanSpace ℝ (Fin d)) : GalileanGroup d :=
  ⟨1, 0, a, 0⟩

@[simp]
lemma pureSpaceTranslation_rotation (a : EuclideanSpace ℝ (Fin d)) :
    (pureSpaceTranslation a).rotation = 1 := rfl

@[simp]
lemma pureSpaceTranslation_velocity (a : EuclideanSpace ℝ (Fin d)) :
    (pureSpaceTranslation a).velocity = 0 := rfl

@[simp]
lemma pureSpaceTranslation_spaceTranslation (a : EuclideanSpace ℝ (Fin d)) :
    (pureSpaceTranslation a).spaceTranslation = a := rfl

@[simp]
lemma pureSpaceTranslation_timeTranslation (a : EuclideanSpace ℝ (Fin d)) :
    (pureSpaceTranslation a).timeTranslation = 0 := rfl

/-!

### B.5. Pure time translations

-/

/-- The Galilean transformation that is a pure time translation by `b`. -/
def pureTimeTranslation (b : Time) : GalileanGroup d :=
  ⟨1, 0, 0, b⟩

@[simp]
lemma pureTimeTranslation_rotation (b : Time) :
    (pureTimeTranslation (d := d) b).rotation = 1 := rfl

@[simp]
lemma pureTimeTranslation_velocity (b : Time) :
    (pureTimeTranslation (d := d) b).velocity = 0 := rfl

@[simp]
lemma pureTimeTranslation_spaceTranslation (b : Time) :
    (pureTimeTranslation (d := d) b).spaceTranslation = 0 := rfl

@[simp]
lemma pureTimeTranslation_timeTranslation (b : Time) :
    (pureTimeTranslation (d := d) b).timeTranslation = b := rfl

/-!

## C. The action on `Time × Space d`

-/

/-- The action of a Galilean transformation `g` on a point `(t, x)` in
`Time × Space d`:
```
(t, x) ↦ (t + b, R x + v t + a)
```
where `R, v, a, b` are the four pieces of data of `g`. -/
def apply (g : GalileanGroup d) (tx : Time × Space d) : Time × Space d :=
  (tx.1 + g.timeTranslation,
    ⟨fun i => g.rotation.1.mulVec tx.2.val i
              + tx.1.val * g.velocity i
              + g.spaceTranslation i⟩)

/-!

### C.1. The coordinate formulas

-/

@[simp]
lemma apply_fst (g : GalileanGroup d) (t : Time) (x : Space d) :
    (g.apply (t, x)).1 = t + g.timeTranslation := rfl

@[simp]
lemma apply_snd_apply (g : GalileanGroup d) (t : Time) (x : Space d) (i : Fin d) :
    (g.apply (t, x)).2 i =
      g.rotation.1.mulVec x.val i + t.val * g.velocity i + g.spaceTranslation i :=
  rfl

/-!

### C.2. Action of the identity

-/

@[simp]
lemma id_apply (tx : Time × Space d) : id.apply tx = tx := by
  obtain ⟨t, x⟩ := tx
  ext
  · simp [apply]
  · simp [apply, Matrix.one_mulVec]

/-!

### C.3. Action of pure rotations

-/

@[simp]
lemma pureRotation_apply (R : Matrix.orthogonalGroup (Fin d) ℝ)
    (t : Time) (x : Space d) :
    (pureRotation R).apply (t, x) = (t, ⟨fun i => R.1.mulVec x.val i⟩) := by
  ext
  · simp [apply]
  · simp [apply]

/-!

### C.4. Action of pure boosts

-/

@[simp]
lemma pureBoost_apply (v : EuclideanSpace ℝ (Fin d))
    (t : Time) (x : Space d) :
    (pureBoost v).apply (t, x) =
      (t, ⟨fun i => x i + t.val * v i⟩) := by
  ext
  · simp [apply]
  · simp [apply, Matrix.one_mulVec]

/-!

### C.5. Action of pure spatial translations

-/

@[simp]
lemma pureSpaceTranslation_apply (a : EuclideanSpace ℝ (Fin d))
    (t : Time) (x : Space d) :
    (pureSpaceTranslation a).apply (t, x) =
      (t, ⟨fun i => x i + a i⟩) := by
  ext
  · simp [apply]
  · simp [apply, Matrix.one_mulVec]

/-!

### C.6. Action of pure time translations

-/

@[simp]
lemma pureTimeTranslation_apply (b : Time) (t : Time) (x : Space d) :
    (pureTimeTranslation b).apply (t, x) = (t + b, x) := by
  ext
  · simp [apply]
  · simp [apply, Matrix.one_mulVec]

end GalileanGroup

end
