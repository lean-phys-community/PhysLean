/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.QECC.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Stabilizer codes

This file develops the *stabilizer formalism* for quantum error-correcting codes, following the
standard symplectic (GF(2)) representation of the Pauli group.

An `n`-qubit Pauli operator, up to phase, is `X^x Z^z` for bit-strings `x, z : Fin n → ZMod 2`. So
the Pauli group modulo phase is the symplectic space `PauliSpace n = (Fin n → ZMod 2) × (Fin n →
ZMod 2)`, with Pauli multiplication corresponding to addition of these vectors. Two Paulis commute
iff their **symplectic form** vanishes. A *stabilizer group* is then an isotropic subspace (a
subspace on which the symplectic form vanishes identically): a set of mutually commuting Paulis.

A `Stabilizer n` bundles such a subspace together with its isotropy. Its `codeSpace` is (abstractly)
the joint `+1`-eigenspace of the stabilizer; the number of logical qubits is `n - dim S`, and the
`distance` is the minimum weight of a nontrivial logical operator (an element of the centralizer
that is not in the stabilizer).

This is the symplectic abstraction of a `QuantumLib.QECC` on qubits (`d2 = Fin 2`, `i = Fin n`): a
stabilizer determines a code subspace of `Fin n → Fin 2` and hence encoder/decoder channels. We work
at the level of the symplectic data, which is where the combinatorial content of stabilizer codes
lives.

## Main definitions

* `PauliSpace n` — the symplectic phase space of `n`-qubit Paulis (mod phase).
* `symplecticForm` — the GF(2) symplectic form; `Commute p q` means it vanishes.
* `Stabilizer n` — an isotropic subspace of `PauliSpace n`.
* `Stabilizer.centralizer` — the Paulis commuting with the whole stabilizer.
* `Stabilizer.weight`, `Stabilizer.distance`, `Stabilizer.numLogical`, `Stabilizer.numPhysical`.
-/

@[expose] public section

open scoped BigOperators

namespace QuantumLib

variable {n : ℕ}

/-- The symplectic phase space of `n`-qubit Pauli operators, modulo phase: an element `(x, z)`
represents the Pauli `X^x Z^z`. Pauli multiplication (mod phase) is addition here. -/
abbrev PauliSpace (n : ℕ) : Type := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- The symplectic form on Pauli phase space: `⟨(x,z), (x',z')⟩ = Σᵢ (xᵢ z'ᵢ + zᵢ x'ᵢ)`. Two Paulis
commute iff this is zero. -/
def symplecticForm (p q : PauliSpace n) : ZMod 2 :=
  ∑ i, (p.1 i * q.2 i + p.2 i * q.1 i)

/-- The symplectic form is symmetric (over GF(2)). -/
theorem symplecticForm_comm (p q : PauliSpace n) : symplecticForm p q = symplecticForm q p := by
  unfold symplecticForm
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Every Pauli commutes with itself: the symplectic form is alternating. -/
@[simp]
theorem symplecticForm_self (p : PauliSpace n) : symplecticForm p p = 0 := by
  unfold symplecticForm
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_comm (p.2 i)]
  exact CharTwo.add_self_eq_zero _

/-- The symplectic form is additive in its left argument. -/
theorem symplecticForm_add_left (p p' q : PauliSpace n) :
    symplecticForm (p + p') q = symplecticForm p q + symplecticForm p' q := by
  unfold symplecticForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Prod.add_def, Pi.add_apply]
  ring

/-- The symplectic form is additive in its right argument. -/
theorem symplecticForm_add_right (p q q' : PauliSpace n) :
    symplecticForm p (q + q') = symplecticForm p q + symplecticForm p q' := by
  rw [symplecticForm_comm, symplecticForm_add_left, symplecticForm_comm p q,
    symplecticForm_comm p q']

/-- Two Paulis *commute* iff their symplectic form vanishes. -/
def Commute (p q : PauliSpace n) : Prop := symplecticForm p q = 0

/-- Commutation is symmetric. -/
theorem Commute.symm {p q : PauliSpace n} (h : Commute p q) : Commute q p := by
  rwa [Commute, ← symplecticForm_comm]

@[simp]
theorem commute_self (p : PauliSpace n) : Commute p p := symplecticForm_self p

/-- A **stabilizer group** in symplectic form: an isotropic subspace of Pauli phase space, i.e. a
`ZMod 2`-subspace on which the symplectic form vanishes identically (all its Paulis commute, and it
does not contain a Pauli anticommuting with itself). -/
structure Stabilizer (n : ℕ) where
  /-- The underlying subspace of Pauli phase space. -/
  carrier : Submodule (ZMod 2) (PauliSpace n)
  /-- Isotropy: any two members commute. -/
  isotropic : ∀ p ∈ carrier, ∀ q ∈ carrier, symplecticForm p q = 0

namespace Stabilizer

/-- Members of a stabilizer pairwise commute. -/
theorem commute_of_mem (S : Stabilizer n) {p q : PauliSpace n}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) : Commute p q :=
  S.isotropic p hp q hq

/-- The *centralizer* (normalizer) of a stabilizer: all Paulis commuting with the whole group. Its
elements that lie outside the stabilizer are the nontrivial logical operators. -/
def centralizer (S : Stabilizer n) : Set (PauliSpace n) :=
  {p | ∀ q ∈ S.carrier, symplecticForm p q = 0}

/-- A stabilizer is contained in its own centralizer (this is exactly isotropy). -/
theorem subset_centralizer (S : Stabilizer n) : (S.carrier : Set (PauliSpace n)) ⊆ S.centralizer :=
  fun _ hp _ hq => S.isotropic _ hp _ hq

/-- The centralizer is closed under addition. -/
theorem centralizer_add_mem (S : Stabilizer n) {p p' : PauliSpace n}
    (hp : p ∈ S.centralizer) (hp' : p' ∈ S.centralizer) : p + p' ∈ S.centralizer := by
  intro q hq
  rw [symplecticForm_add_left, hp q hq, hp' q hq, add_zero]

/-- The centralizer contains `0`. -/
theorem zero_mem_centralizer (S : Stabilizer n) : (0 : PauliSpace n) ∈ S.centralizer := by
  intro q _
  simp [symplecticForm]

/-- The weight of a Pauli: the number of qubits on which it acts nontrivially. -/
def weight (p : PauliSpace n) : ℕ :=
  (Finset.univ.filter (fun i => p.1 i ≠ 0 ∨ p.2 i ≠ 0)).card

@[simp]
theorem weight_zero : weight (0 : PauliSpace n) = 0 := by
  simp [weight]

theorem weight_le (p : PauliSpace n) : weight p ≤ n := by
  unfold weight
  calc (Finset.univ.filter (fun i => p.1 i ≠ 0 ∨ p.2 i ≠ 0)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := by simp

/-- The number of physical qubits of a stabilizer code. -/
def numPhysical (_ : Stabilizer n) : ℕ := n

/-- The number of logical qubits `k = n - dim S` (the codespace has dimension `2^k`). -/
noncomputable def numLogical (S : Stabilizer n) : ℕ :=
  n - Module.finrank (ZMod 2) S.carrier

/-- The code distance: the minimum weight of a nontrivial logical operator, i.e. an element of the
centralizer that is not in the stabilizer. (By convention `0` if there are no logical operators.) -/
noncomputable def distance (S : Stabilizer n) : ℕ :=
  sInf {w | ∃ p ∈ S.centralizer, p ∉ S.carrier ∧ weight p = w}

/-- A code has parameters `⟦n, k, d⟧` if it has `n` physical qubits, `k` logical qubits, and
distance `d`. -/
def HasParams (S : Stabilizer n) (k d : ℕ) : Prop :=
  S.numLogical = k ∧ S.distance = d

end Stabilizer

/-! ### The trivial stabilizer

The `⊥` (zero) subspace is trivially isotropic: it is the "no stabilizer" code, which stores `n`
logical qubits with no protection (distance `1`). -/

/-- The trivial stabilizer (the zero subspace): `n` unprotected logical qubits. -/
def trivialStabilizer (n : ℕ) : Stabilizer n where
  carrier := ⊥
  isotropic := by
    intro p hp q _
    rw [Submodule.mem_bot] at hp
    subst hp
    rw [symplecticForm_comm]
    simp [symplecticForm]

@[simp]
theorem trivialStabilizer_numLogical (n : ℕ) : (trivialStabilizer n).numLogical = n := by
  rw [Stabilizer.numLogical]
  show n - Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) (PauliSpace n)) = n
  rw [finrank_bot, Nat.sub_zero]

/-! ### Pauli operators as complex matrices

The symplectic data of `PauliSpace n` is realized by honest unitary matrices on the `n`-qubit
Hilbert space `(Fin n → ZMod 2) → ℂ` (recall `ZMod 2 = Fin 2`). This is the bridge between the
combinatorial stabilizer formalism above and the operator-level content of a code: operator
commutation matches the symplectic form, and the code subspace is the joint `+1`-eigenspace. -/

/-- The `n`-qubit Pauli operator `X^x Z^z` for `p = (x, z)`, as a complex matrix on
`(Fin n → ZMod 2) → ℂ`. Its `(u, v)` entry is `(-1)^(z · v)` when `u = v + x`, and `0` otherwise. -/
def pauliOp (p : PauliSpace n) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  Matrix.of fun u v => if u = v + p.1 then ∏ i, (-1 : ℂ) ^ (p.2 i * v i).val else 0

/-- The identity Pauli is the identity matrix. -/
theorem pauliOp_zero : pauliOp (0 : PauliSpace n) = 1 := by
  ext u v
  simp only [pauliOp, Matrix.of_apply, Prod.fst_zero, add_zero, Prod.snd_zero, Pi.zero_apply,
    zero_mul, ZMod.val_zero, pow_zero, Finset.prod_const_one, Matrix.one_apply]

/-- A GF(2) sign identity: `(-1)^(a+b)` factors, since `ZMod 2` addition is parity addition. -/
theorem negOnePow_zmod2_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  generalize a.val + b.val = m
  conv_rhs => rw [← Nat.div_add_mod m 2, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- Pauli multiplication realizes addition in `PauliSpace n`, up to the sign `(-1)^(z_p · x_q)`. -/
theorem pauliOp_mul (p q : PauliSpace n) :
    pauliOp p * pauliOp q = (∏ i, (-1 : ℂ) ^ (p.2 i * q.1 i).val) • pauliOp (p + q) := by
  ext u w
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, pauliOp, Matrix.of_apply]
  rw [Finset.sum_eq_single (w + q.1)]
  · -- The unique surviving term, at `v = w + q.1`.
    have hpq1 : (p + q).1 = p.1 + q.1 := rfl
    have hpq2 : (p + q).2 = p.2 + q.2 := rfl
    by_cases huc : u = w + (p + q).1
    · have hcp : u = w + q.1 + p.1 := by rw [huc, hpq1]; abel
      rw [if_pos rfl, if_pos hcp, if_pos huc]
      have e1 : (∏ i, (-1 : ℂ) ^ (p.2 i * (w + q.1) i).val)
          = (∏ i, (-1 : ℂ) ^ (p.2 i * w i).val) * ∏ i, (-1 : ℂ) ^ (p.2 i * q.1 i).val := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, mul_add, negOnePow_zmod2_add]
      have e2 : (∏ i, (-1 : ℂ) ^ ((p + q).2 i * w i).val)
          = (∏ i, (-1 : ℂ) ^ (p.2 i * w i).val) * ∏ i, (-1 : ℂ) ^ (q.2 i * w i).val := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by
          rw [hpq2, Pi.add_apply, add_mul, negOnePow_zmod2_add]
      rw [e1, e2]; ring
    · have hcp : ¬ u = w + q.1 + p.1 := by rw [hpq1] at huc; rwa [show w + q.1 + p.1 = w + (p.1 + q.1) by abel]
      simp only [if_neg huc, if_neg hcp, zero_mul, mul_zero]
  · intro v _ hv
    rw [if_neg hv, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Pauli operators are unitary. -/
theorem pauliOp_mem_unitaryGroup (p : PauliSpace n) :
    pauliOp p ∈ Matrix.unitaryGroup (Fin n → ZMod 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext u w
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply, pauliOp, Matrix.of_apply]
  rw [Finset.sum_eq_single (u + p.1)]
  · rw [if_pos rfl]
    by_cases huw : u = w
    · subst huw
      rw [if_pos rfl, if_pos rfl]
      have hstar : star (∏ i, (-1 : ℂ) ^ (p.2 i * u i).val)
          = ∏ i, (-1 : ℂ) ^ (p.2 i * u i).val := by
        rw [star_prod]
        exact Finset.prod_congr rfl fun i _ => by rw [star_pow, star_neg, star_one]
      rw [hstar, ← Finset.prod_mul_distrib, Finset.prod_eq_one]
      intro i _
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    · rw [if_neg (mt add_right_cancel huw), mul_zero, if_neg huw]
  · intro v _ hv
    rw [if_neg hv, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The product `∏ (-1)^(f i)` collapses to `(-1)` raised to the GF(2) sum. -/
theorem negOnePow_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ZMod 2) :
    ∏ i ∈ s, (-1 : ℂ) ^ (f i).val = (-1) ^ (∑ i ∈ s, f i).val := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, ← negOnePow_zmod2_add, ← Finset.sum_insert ha]

/-- A Pauli operator is nonzero (being unitary). -/
private theorem pauliOp_ne_zero (r : PauliSpace n) : pauliOp r ≠ 0 := by
  intro h
  have hu := pauliOp_mem_unitaryGroup r
  rw [Matrix.mem_unitaryGroup_iff, h, zero_mul] at hu
  exact zero_ne_one hu

/-- `(-1)^(z.val) = 1` exactly when `z = 0` in `ZMod 2`. -/
private theorem negOnePow_val_eq_one {z : ZMod 2} : (-1 : ℂ) ^ z.val = 1 ↔ z = 0 := by
  rw [neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1), Nat.even_iff]
  have hlt : z.val < 2 := ZMod.val_lt z
  constructor
  · intro he
    have hz0 : z.val = 0 := by omega
    have : z.val = (0 : ZMod 2).val := by rw [hz0, ZMod.val_zero]
    exact ZMod.val_injective 2 this
  · rintro rfl; simp

/-- **Key bridge:** two Pauli operators commute (as matrices) iff their symplectic form vanishes,
i.e. iff they `Commute` in the symplectic sense. -/
theorem pauliOp_commute_iff (p q : PauliSpace n) :
    _root_.Commute (pauliOp p) (pauliOp q) ↔ symplecticForm p q = 0 := by
  rw [commute_iff_eq, pauliOp_mul, pauliOp_mul, add_comm q p, ← sub_eq_zero, ← sub_smul,
    smul_eq_zero, or_iff_left (pauliOp_ne_zero _), sub_eq_zero, negOnePow_sum, negOnePow_sum]
  -- `(-1)^(∑ p₂·q₁).val = (-1)^(∑ q₂·p₁).val ↔ symplecticForm p q = 0`
  have hsym : symplecticForm p q = (∑ i, p.2 i * q.1 i) + ∑ i, q.2 i * p.1 i := by
    unfold symplecticForm
    rw [Finset.sum_add_distrib, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsym, ← negOnePow_val_eq_one, negOnePow_zmod2_add]
  -- `c = d ↔ c * d = 1`, where `d = (-1)^(∑ q₂·p₁).val` is its own inverse
  have hdd : (-1 : ℂ) ^ (∑ i, q.2 i * p.1 i).val * (-1) ^ (∑ i, q.2 i * p.1 i).val = 1 := by
    rw [← negOnePow_zmod2_add, CharTwo.add_self_eq_zero, ZMod.val_zero, pow_zero]
  constructor
  · intro h; rw [h]; exact hdd
  · intro h
    exact mul_right_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) (h.trans hdd.symm)

end QuantumLib
