/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Tactic.DeriveFintype
/-!

# Dimension

In this module we define the type `Dimension` which carries the dimension
of a physical quantity.

A `Dimension B` is parameterised by a *basis* `B` of base dimensions: it assigns a
rational `exponent` to each base dimension `b : B`. The parameterisation is purely in
the dimensional *algebra*: `Dimension B` is a `CommGroup` for every `B`
(multiplication adds exponents, inversion negates them), so quantities can be typed by
dimensions over any basis. The commutative-group and `ℚ`-power structure, decidable
equality (`DecidableEq`), the base vectors `single b`, and the change-of-basis map
`extend` are all generic in `B`.

PhysLib's default basis is `LTMCTDimensionBase` — length, time, mass, charge,
temperature — whose projections and named generators (`L𝓭`, `T𝓭`, …) live in
`Physlib.Units.LTMCTDimensionBase`. It is *charge*-based with five generators, so it
is **not** the SI/ISQ base-quantity set; the ISQ set is `ISQDimensionBase`, and other
systems (Gaussian–CGS, natural units, …) are equally expressible as `Dimension B` for
a suitable basis `B`.

-/

@[expose] public section

open NNReal

/-!

## Defining dimensions

-/

/-- A dimension over a basis `B` of base dimensions: a rational `exponent` for each
  base dimension `b : B`. PhysLib's default basis is `LTMCTDimensionBase`. -/
structure Dimension (B : Type) where
  /-- The exponent of each base dimension. -/
  exponent : B → ℚ

namespace Dimension

variable {B : Type}

@[ext]
lemma ext {d1 d2 : Dimension B} (h : ∀ b, d1.exponent b = d2.exponent b) : d1 = d2 := by
  cases d1
  cases d2
  congr
  funext b
  exact h b

instance : Mul (Dimension B) where
  mul d1 d2 := ⟨fun b => d1.exponent b + d2.exponent b⟩

@[simp]
lemma mul_exponent (d1 d2 : Dimension B) (b : B) :
    (d1 * d2).exponent b = d1.exponent b + d2.exponent b := rfl

instance : One (Dimension B) where
  one := ⟨fun _ => 0⟩

@[simp]
lemma one_exponent (b : B) : (1 : Dimension B).exponent b = 0 := rfl

instance : CommGroup (Dimension B) where
  mul_assoc a b c := by
    ext x
    simp [add_assoc]
  one_mul a := by
    ext x
    simp
  mul_one a := by
    ext x
    simp
  inv d := ⟨fun b => -d.exponent b⟩
  inv_mul_cancel a := by
    ext x
    simp
  mul_comm a b := by
    ext x
    simp [add_comm]

@[simp]
lemma inv_exponent (d : Dimension B) (b : B) : d⁻¹.exponent b = -d.exponent b := rfl

@[simp]
lemma div_exponent (d1 d2 : Dimension B) (b : B) :
    (d1 / d2).exponent b = d1.exponent b - d2.exponent b := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

@[simp]
lemma npow_exponent (d : Dimension B) (n : ℕ) (b : B) :
    (d ^ n).exponent b = n • d.exponent b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_exponent, ih, succ_nsmul]

instance : Pow (Dimension B) ℚ where
  pow d q := ⟨fun b => d.exponent b * q⟩

@[simp]
lemma qpow_exponent (d : Dimension B) (q : ℚ) (b : B) :
    (d ^ q).exponent b = d.exponent b * q := rfl

/-- Decidable equality of dimensions over a finite basis `B`. -/
instance [Fintype B] : DecidableEq (Dimension B) := fun d1 d2 =>
  decidable_of_iff (∀ b, d1.exponent b = d2.exponent b)
    ⟨fun h => Dimension.ext h, fun h _ => h ▸ rfl⟩

/-- The base-dimension vector for `b : B`: exponent `1` at `b`, `0` elsewhere. This
  is the generic analogue of the named generators `L𝓭`, `T𝓭`, … -/
def single [DecidableEq B] (b : B) : Dimension B := ⟨Pi.single b 1⟩

@[simp]
lemma single_exponent [DecidableEq B] (b b' : B) :
    (single b).exponent b' = if b' = b then 1 else 0 := by
  simp only [single, Pi.single_apply]

/-- Change of basis along a map `f : B → B'` of base dimensions: reindex a dimension
  over `B` into one over `B'` by placing each exponent at its image. For an embedding
  `f` (injective) this preserves every exponent (`extend_exponent_apply`), so a
  dimension in one system re-expresses faithfully in an extending one. -/
def extend {B' : Type} [Fintype B] [DecidableEq B'] (f : B → B') (d : Dimension B) :
    Dimension B' :=
  ⟨fun b' => ∑ b, if f b = b' then d.exponent b else 0⟩

@[simp]
lemma extend_exponent_apply {B' : Type} [Fintype B] [DecidableEq B'] {f : B → B'}
    (hf : Function.Injective f) (d : Dimension B) (b : B) :
    (extend f d).exponent (f b) = d.exponent b := by
  simp only [extend]
  rw [Finset.sum_eq_single b (fun b'' _ hne => by simp [hf.ne hne]) (by simp)]
  simp

/-!

## Dimension-preserving maps between bases

A cross-basis map of dimensions is only admissible if it preserves the dimensional
*algebra*. We record the two truth-preserving directions as bundled data:

* an `Embedding B B'` is an **injective** `MonoidHom (Dimension B) (Dimension B')` — a
  faithful, dimension-preserving inclusion of one basis into another; and
* a `Projection B' B` is a **surjective** `MonoidHom (Dimension B') (Dimension B)` — a
  truth-preserving *reduction* of a richer basis onto a coarser one.

Being a `MonoidHom` is what makes either map dimension-preserving (it respects
products, inverses and rational powers); the injectivity / surjectivity side condition
distinguishes the two directions. Cross-basis dimension maps should be produced as one
of these, so that dimension-preservation holds by construction — a bare relabelling
that sends a base dimension to an inequivalent one is *not* expressible as either.

-/

/-- `extend f` packaged as a monoid homomorphism of dimensions. -/
def extendHom {B' : Type} [Fintype B] [DecidableEq B'] (f : B → B') :
    Dimension B →* Dimension B' where
  toFun := extend f
  map_one' := by ext b'; simp [extend]
  map_mul' d1 d2 := by
    ext b'
    simp only [extend, mul_exponent]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp

/-- A **dimension embedding** `B ↪ B'`: an injective monoid homomorphism of
  dimensions. As a `MonoidHom` it is dimension-preserving (it respects products,
  inverses and rational powers); injectivity makes it a faithful inclusion of the basis
  `B` into `B'`. Cross-basis dimension injections are produced as `Embedding`s so that
  dimension-preservation holds by construction. -/
structure Embedding (B B' : Type) where
  /-- The underlying dimension-preserving homomorphism. -/
  toHom : Dimension B →* Dimension B'
  /-- The homomorphism is injective (a faithful embedding). -/
  inj : Function.Injective toHom

/-- A **dimension projection** `B' ↠ B`: a surjective monoid homomorphism of
  dimensions. As a `MonoidHom` it is truth-preserving, but it is lossy — it reduces a
  richer basis `B'` onto a coarser basis `B`, collapsing the base dimensions that `B`
  does not track. -/
structure Projection (B' B : Type) where
  /-- The underlying dimension-preserving homomorphism. -/
  toHom : Dimension B' →* Dimension B
  /-- The homomorphism is surjective (the reduction hits every dimension of `B`). -/
  surj : Function.Surjective toHom

/-- An injective *basis* map `f : B → B'` induces a dimension embedding, via `extend`.
  This is the label-level case: it sends each base dimension of `B` to a base dimension
  of `B'`, so it is automatically dimension-preserving and faithful. -/
def Embedding.ofBasis {B B' : Type} [Fintype B] [DecidableEq B']
    (f : B → B') (hf : Function.Injective f) : Embedding B B' where
  toHom := extendHom f
  inj := by
    intro d1 d2 h
    ext b
    have h2 : (extendHom f d1).exponent (f b) = (extendHom f d2).exponent (f b) := by
      rw [h]
    simpa only [extendHom, MonoidHom.coe_mk, OneHom.coe_mk, extend_exponent_apply hf]
      using h2

end Dimension
