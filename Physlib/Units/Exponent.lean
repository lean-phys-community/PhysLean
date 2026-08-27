/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Algebra.Order.Ring.Rat
/-!

# Reducible rational arithmetic for dimension exponents

This module defines `Exponent`, a wrapper around the rational numbers whose arithmetic is
reducible. This lets concrete arithmetic on dimension exponents hold by definitional equality.

The corresponding rational operations are irreducible in Lean. Locally unsealing them does not
export their reducibility to downstream modules, while globally changing the reducibility of an
imported declaration requires `allowUnsafeReducibility`. The wrapper instead owns transparent
operations while remaining equivalent to `ℚ`.

The reducibility guarantee applies to the custom addition, subtraction, multiplication, inversion,
and division below. Other operations supplied by the `Field` instance are transferred from `ℚ`.
In particular, rational scalar multiplication and negative integer powers may require propositional
reasoning rather than `rfl`.

-/

@[expose] public section

namespace Dimension

/-!

## A. Definition

-/

/-- A rational dimension exponent with reducible arithmetic. -/
structure Exponent where
  /-- The rational number represented by the exponent. -/
  toRat : ℚ
deriving DecidableEq

attribute [coe] Exponent.toRat

instance : Repr Exponent where
  reprPrec x := reprPrec x.toRat

namespace Exponent

/-- The equivalence between `Exponent` and the rational numbers. -/
def equivRat : Exponent ≃ ℚ :=
  Equiv.mk Exponent.toRat Exponent.mk Eq.refl Eq.refl

/-- Regard a rational number as a dimension exponent. -/
def ofRat (q : ℚ) : Exponent := ⟨q⟩

@[simp]
lemma ofRat_toRat (q : ℚ) : (ofRat q).toRat = q := rfl

/-- Fuel-bounded Euclidean algorithm used to make exponent normalization reducible. -/
def gcdAux : Nat → Nat → Nat → Nat
  | 0, _, n => n
  | fuel + 1, m, n => if m = 0 then n else gcdAux fuel (n % m) m

private lemma gcdAux_eq_nat_gcd (fuel m n : Nat) (m_lt_fuel : m < fuel) :
    gcdAux fuel m n = Nat.gcd m n := by
  induction fuel generalizing m n with
  | zero => omega
  | succ fuel ih =>
      rw [gcdAux, Nat.gcd_def]
      split
      · rfl
      · apply ih; have := Nat.mod_lt n (Nat.zero_lt_of_ne_zero ‹m ≠ 0›); omega

/-- Reducible greatest common divisor used when normalizing an exponent. -/
def gcd (m n : Nat) : Nat :=
  gcdAux (m + 1) m n

/-- The reducible exponent GCD agrees with `Nat.gcd`. -/
lemma gcd_eq_nat_gcd (m n : Nat) : gcd m n = Nat.gcd m n := by
  exact gcdAux_eq_nat_gcd (m + 1) m n (Nat.lt_add_one m)

/-- Construct an exponent by normalizing a numerator and a nonzero denominator. -/
def normalize (num : Int) (den : Nat) (den_ne_zero : den ≠ 0) : Exponent :=
  let g := gcd num.natAbs den
  let g_eq : g = num.natAbs.gcd den := gcd_eq_nat_gcd num.natAbs den
  ⟨Rat.maybeNormalize num den g
    (Rat.normalize.dvd_num g_eq)
    (Rat.normalize.dvd_den g_eq)
    (Rat.normalize.den_nz den_ne_zero g_eq)
    (Rat.normalize.reduced den_ne_zero g_eq)⟩

lemma normalize_toRat (num : Int) (den : Nat) (den_ne_zero : den ≠ 0) :
    (normalize num den den_ne_zero).toRat = Rat.normalize num den den_ne_zero := by
  unfold normalize Rat.normalize
  simp only [gcd_eq_nat_gcd]

/-- The normalized numerator of an exponent. -/
@[reducible] def num (x : Exponent) : Int :=
  x.toRat.num

/-- The normalized denominator of an exponent. -/
@[reducible] def den (x : Exponent) : Nat :=
  x.toRat.den

/-!

## B. Arithmetic

-/

/-- Reducible addition of dimension exponents. -/
def add (a b : Exponent) : Exponent :=
  normalize (a.num * b.den + b.num * a.den) (a.den * b.den)
    (Nat.mul_ne_zero a.toRat.den_nz b.toRat.den_nz)

instance : Add Exponent := Add.mk add

lemma add_equiv (a b : Exponent) : equivRat (add a b) = equivRat a + equivRat b := by
  rw [Rat.add_def]
  exact normalize_toRat _ _ _

/-- Reducible subtraction of dimension exponents. -/
def sub (a b : Exponent) : Exponent :=
  add a ⟨-b.toRat⟩

instance : Sub Exponent := Sub.mk sub

lemma sub_equiv (a b : Exponent) : equivRat (sub a b) = equivRat a - equivRat b := by
  rw [sub, add_equiv]
  simp [equivRat, sub_eq_add_neg]

/-- Reducible multiplication of dimension exponents. -/
def mul (a b : Exponent) : Exponent :=
  normalize (a.num * b.num) (a.den * b.den)
    (Nat.mul_ne_zero a.toRat.den_nz b.toRat.den_nz)

instance : Mul Exponent := Mul.mk mul

lemma mul_equiv (a b : Exponent) : equivRat (mul a b) = equivRat a * equivRat b := by
  rw [Rat.mul_def]
  exact normalize_toRat _ _ _

/-- Reducible inversion of a dimension exponent, with `0⁻¹ = 0`. -/
def inv (a : Exponent) : Exponent :=
  if ne_zero : a.toRat ≠ 0 then
    have num_ne_zero : a.num ≠ 0 := ne_zero ∘ Rat.num_eq_zero.mp
    ⟨{ num := a.num.sign * a.den
       den := a.num.natAbs
       den_nz := by exact Nat.ne_of_gt (Int.natAbs_pos.mpr num_ne_zero)
       reduced := by simpa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero num_ne_zero]
         using a.toRat.reduced.symm }⟩
  else a

instance : Inv Exponent := Inv.mk inv

lemma inv_equiv (a : Exponent) : equivRat (inv a) = (equivRat a)⁻¹ := by
  by_cases ne_zero : a.toRat ≠ 0
  · apply Rat.ext <;> simp [inv, ne_zero, equivRat, Rat.num_inv, Rat.den_inv]
  · push Not at ne_zero
    apply Rat.ext <;> simp [inv, ne_zero, equivRat]

/-- Reducible division of dimension exponents. -/
def div (a b : Exponent) : Exponent :=
  mul a (inv b)

instance : Div Exponent := Div.mk div

lemma div_equiv (a b : Exponent) : equivRat (div a b) = equivRat a / equivRat b := by
  rw [div, mul_equiv, inv_equiv, div_eq_mul_inv]

/-!

## C. Field structure

-/

instance instField : Field Exponent := by
  letI := equivRat.field
  apply equivRat.injective.field
  · rfl
  · rfl
  all_goals intros
  case add => apply add_equiv
  case sub => apply sub_equiv
  case inv => apply inv_equiv
  case mul => apply mul_equiv
  case div => apply div_equiv
  all_goals rfl

/-- The ring equivalence between dimension exponents and rational numbers. -/
def ringEquivRat : Exponent ≃+* ℚ where
  toEquiv := equivRat
  map_add' := add_equiv
  map_mul' := mul_equiv

/-- Regard a dimension exponent as a rational number. -/
instance : Coe Exponent ℚ := ⟨Exponent.toRat⟩

@[simp, norm_cast]
lemma coe_inj {a b : Exponent} : (a : ℚ) = b ↔ a = b :=
  ringEquivRat.injective.eq_iff

@[simp, norm_cast]
lemma coe_zero : ((0 : Exponent) : ℚ) = 0 := map_zero ringEquivRat

@[simp, norm_cast]
lemma coe_one : ((1 : Exponent) : ℚ) = 1 := map_one ringEquivRat

@[simp, norm_cast]
lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : Exponent) : ℚ) = ofNat(n) :=
  map_ofNat ringEquivRat n

@[simp, norm_cast]
lemma coe_add (a b : Exponent) : ((a + b : Exponent) : ℚ) = a + b :=
  map_add ringEquivRat a b

@[simp, norm_cast]
lemma coe_sub (a b : Exponent) : ((a - b : Exponent) : ℚ) = a - b :=
  map_sub ringEquivRat a b

@[simp, norm_cast]
lemma coe_neg (a : Exponent) : ((-a : Exponent) : ℚ) = -a :=
  map_neg ringEquivRat a

@[simp, norm_cast]
lemma coe_mul (a b : Exponent) : ((a * b : Exponent) : ℚ) = a * b :=
  map_mul ringEquivRat a b

@[simp, norm_cast]
lemma coe_inv (a : Exponent) : ((a⁻¹ : Exponent) : ℚ) = (a : ℚ)⁻¹ :=
  inv_equiv a

@[simp, norm_cast]
lemma coe_div (a b : Exponent) : ((a / b : Exponent) : ℚ) = (a : ℚ) / b :=
  div_equiv a b

instance : LinearOrder Exponent := equivRat.linearOrder

@[simp, norm_cast]
lemma coe_le_coe {a b : Exponent} : (a : ℚ) ≤ b ↔ a ≤ b := Iff.rfl

@[simp, norm_cast]
lemma coe_lt_coe {a b : Exponent} : (a : ℚ) < b ↔ a < b := Iff.rfl

instance : IsStrictOrderedRing Exponent :=
  Function.Injective.isStrictOrderedRing ringEquivRat
    (map_zero ringEquivRat) (map_one ringEquivRat) (map_add ringEquivRat) (map_mul ringEquivRat)
    coe_le_coe coe_lt_coe

instance : CharZero Exponent where
  cast_injective _ _ equality := Nat.cast_injective <| congrArg equivRat equality

-- These regressions pin the field structure to the reducible operations above.
lemma add_eq_instField_add : add = instField.add := rfl
lemma sub_eq_instField_sub : sub = instField.sub := rfl
lemma inv_eq_instField_inv : inv = instField.inv := rfl
lemma mul_eq_instField_mul : mul = instField.mul := rfl
lemma div_eq_instField_div : div = instField.div := rfl

/-!

## D. Definitional equality tests

-/

lemma tuple_arithmetic_defeq :
    let Length : Exponent × Exponent := (1, 0)
    let Time : Exponent × Exponent := (0, 1)
    let Speed := Length - Time
    Length = Time + Speed := rfl

lemma rational_arithmetic_defeq :
    ((2 / 3 + 5 / 7) * (11 / 13 - 1 / 2) : Exponent) = 87 / 182 := rfl

lemma inverse_arithmetic_defeq : ((-3 / 4 : Exponent)⁻¹ + 5 / 6) = -1 / 2 := rfl

end Dimension.Exponent

end
