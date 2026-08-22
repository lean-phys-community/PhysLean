/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.QECC.Pauli

/-!
# Stabilizer codes, faithfully (as `-I`-free abelian Pauli subgroups)

The symplectic `Stabilizer` (an isotropic GF(2) subspace) is *not* enough to pin down a code
space: the sign cocycle of the Pauli group is nontrivial, so a bare subspace can force `-I` into
the group and collapse the joint `+1`-eigenspace (e.g. the `Y` "stabilizer" on one qubit). The
faithful object is an honest **abelian subgroup `S ≤ PauliOp n` with `-I ∉ S`**. Every element then
squares to `I` and is Hermitian, the operator `stabProj S = |S|⁻¹ ∑_{g∈S} g` is the projector onto
the code space, and `dim (codeSpace S) = 2ⁿ / |S|`.

This file sets up those definitions and the key theorems (several proofs farmed to the ATP).
-/

open scoped BigOperators
open Classical

namespace QuantumLib
namespace PauliOp
variable {n : ℕ}

/-! ### Finiteness -/

/-- `PauliOp n` as a product type, for its `Fintype`/`DecidableEq` instances. -/
def equivProd : PauliOp n ≃ ZMod 4 × (Fin n → ZMod 2) × (Fin n → ZMod 2) where
  toFun P := (P.phase, P.x, P.z)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (PauliOp n) := Fintype.ofEquiv _ equivProd.symm
instance : DecidableEq (PauliOp n) := equivProd.decidableEq

/-! ### The `-I` element and traces -/

/-- The Pauli group element `-I` (phase `i² = -1`). -/
def negI (n : ℕ) : PauliOp n := ⟨2, 0, 0⟩

@[simp] theorem toMat_negI : toMat (negI n) = -1 := by
  simp only [toMat, negI]
  rw [show (2 : ZMod 4).val = 2 from rfl, show ((0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2))
    = (0 : PauliSpace n) from rfl, pauliOp_zero, Complex.I_sq, neg_one_smul]

/-- Paulis are traceless except the identity: `tr (XˣZᶻ) = 2ⁿ` if `(x,z)=0`, else `0`. -/
theorem pauliOp_trace (p : PauliSpace n) :
    (pauliOp p).trace = if p = 0 then (2 ^ n : ℂ) else 0 := by
  unfold Matrix.trace
  simp only [pauliOp]
  simp only [Matrix.of_apply, Matrix.diag]
  by_cases hp1 : p.1 = 0
  · simp only [hp1, add_zero, ↓reduceIte]
    by_cases hp2 : p.2 = 0
    · rw [if_pos (Prod.ext hp1 hp2)]; simp [hp2]
    · -- Find j such that p.2 j ≠ 0
      obtain ⟨j, hj⟩ : ∃ j, p.2 j ≠ 0 := Function.ne_iff.mp hp2
      -- The sum factors as a product; one factor is 0
      have hfactor : ∑ x : Fin n → ZMod 2, ∏ i, (-1 : ℂ) ^ (p.2 i * x i).val
          = ∏ i, (∑ xi : ZMod 2, (-1 : ℂ) ^ (p.2 i * xi).val) := by
        rw [Finset.prod_sum]
        refine Finset.sum_bij (fun x _ => fun i _ => x i) ?_ ?_ ?_ ?_
        · intro x _; exact Finset.mem_pi.mpr fun i _ => Finset.mem_univ _
        · intro x _ y _ hxy; ext i; exact congr_fun (congr_fun hxy i) (Finset.mem_univ i)
        · intro g _; use fun i => g i (Finset.mem_univ i); simp
        · intro x _; simp
      have hj1 : p.2 j = 1 := by
        have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        rcases h01 (p.2 j) with h0 | h1
        · exact absurd h0 hj
        · exact h1
      have hsum : ∑ xi, (-1 : ℂ) ^ (p.2 j * xi).val = 0 := by
        simp only [hj1, one_mul]
        have h0 : (-1 : ℂ) ^ (ZMod.val (0 : ZMod 2)) = 1 := by rw [ZMod.val_zero]; norm_num
        have h1 : (-1 : ℂ) ^ (ZMod.val (1 : ZMod 2)) = -1 := by rw [ZMod.val_one]; norm_num
        rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by rfl]
        rw [Finset.sum_pair (by decide), h0, h1]
        norm_num
      rw [hfactor, Finset.prod_eq_zero (Finset.mem_univ j) hsum, if_neg (fun h => hp2 (by simp [h]))]
  · have hne : ∀ x : Fin n → ZMod 2, x ≠ x + p.1 := by
      intro x hx
      have : p.1 = 0 := add_eq_left.mp hx.symm
      contradiction
    simp only [hne, ite_false, Finset.sum_const_zero]
    rw [if_neg (fun h => hp1 (Prod.ext_iff.mp h |>.1))]

/-- Trace of a Pauli group element: `2ⁿ` for the identity, `0` otherwise. -/
theorem toMat_trace (P : PauliOp n) :
    (toMat P).trace = if P.x = 0 ∧ P.z = 0 then Complex.I ^ P.phase.val * 2 ^ n else 0 := by
  simp only [toMat]
  rw [Matrix.trace_smul]
  by_cases h : P.x = 0 ∧ P.z = 0 <;> simp [pauliOp_trace, h]

/-- The four powers `Iᵏ` for `k < 4` are pairwise distinct. -/
theorem I_pow_lt_four_injective (i j : ℕ) (hi : i < 4) (hj : j < 4)
    (h : Complex.I ^ i = Complex.I ^ j) : i = j := by
  have h1 : Complex.I ^ 1 = Complex.I := by norm_num
  have h2 : Complex.I ^ 2 = (-1 : ℂ) := by norm_num [Complex.I_sq]
  have h3 : Complex.I ^ 3 = (-Complex.I) := by norm_num [pow_succ, Complex.I_sq]
  have e1 : (1 : ℂ) ≠ Complex.I := by norm_num [Complex.ext_iff]
  have e2 : (1 : ℂ) ≠ -1 := by norm_num
  have e3 : (1 : ℂ) ≠ -Complex.I := by norm_num [Complex.ext_iff]
  have e4 : Complex.I ≠ (-1 : ℂ) := by norm_num [Complex.ext_iff]
  have e5 : Complex.I ≠ -Complex.I := by norm_num [Complex.ext_iff]
  have e6 : (-1 : ℂ) ≠ -Complex.I := by norm_num [Complex.ext_iff]
  interval_cases i <;> interval_cases j <;> simp_all

/-- `Iᵏ` (`k : ZMod 4`) determines `k`: the `iᵏ` phase of a Pauli is faithful. -/
theorem I_pow_val_injective {a b : ZMod 4} (h : Complex.I ^ a.val = Complex.I ^ b.val) : a = b :=
  ZMod.val_injective 4 (I_pow_lt_four_injective _ _ (ZMod.val_lt a) (ZMod.val_lt b) h)

/-- The Pauli operators are distinct as matrices: `pauliOp` is injective (faithfulness of the
projective Pauli representation, ignoring the scalar phase). -/
theorem pauliOp_injective : Function.Injective (pauliOp (n := n)) := by
  intro p q hpq
  have hp1 : p.1 = q.1 := by
    by_contra hne
    have hentry := congr_fun (congr_fun hpq (0 + p.1)) 0
    simp only [pauliOp] at hentry
    rw [zero_add] at hentry
    simp [hne] at hentry
  refine Prod.ext hp1 (funext fun j => ?_)
  set ej : Fin n → ZMod 2 := fun i => if i = j then 1 else 0 with hej
  have hentry := congr_fun (congr_fun hpq (ej + p.1)) ej
  simp only [pauliOp, Matrix.of_apply, show ej + p.1 = ej + q.1 from by rw [hp1],
    ↓reduceIte] at hentry
  have hprod : ∀ f : Fin n → ZMod 2, ∏ i, (-1 : ℂ) ^ (f i * ej i).val = (-1) ^ (f j).val :=
    fun f => by
      rw [Finset.prod_eq_single j]
      · simp [hej]
      · intro i _ hij; simp [hej, hij]
      · exact fun h => (h (Finset.mem_univ j)).elim
  rw [hprod p.2, hprod q.2] at hentry
  apply ZMod.val_injective (n := 2)
  have hm : ∀ a : ZMod 2, a.val = 0 ∨ a.val = 1 := by decide
  rcases hm (p.2 j) with hp0 | hp0 <;> rcases hm (q.2 j) with hq0 | hq0 <;>
    rw [hp0, hq0] at hentry ⊢ <;>
    first | rfl | (exfalso; norm_num at hentry)

/-! ### Stabilizer groups -/

/-- A **stabilizer group**: an abelian subgroup of the Pauli group not containing `-I`. -/
structure StabGroup (n : ℕ) where
  /-- The underlying subgroup of the Pauli group. -/
  carrier : Subgroup (PauliOp n)
  /-- The group is abelian. -/
  isComm : ∀ a ∈ carrier, ∀ b ∈ carrier, a * b = b * a
  /-- `-I` is not a stabilizer. -/
  negI_notMem : negI n ∉ carrier

namespace StabGroup
variable (S : StabGroup n)

/-- Every stabilizer element squares to the identity (no `-I`, `±iI` in the group). -/
theorem sq_eq_one {g : PauliOp n} (hg : g ∈ S.carrier) : g * g = 1 := by
  -- g * g is in the subgroup
  have hsq : g * g ∈ S.carrier := Subgroup.mul_mem _ hg hg
  -- g * g = ⟨2*phase + tau(betaPair g g), 0, 0⟩
  have mul_self : g * g = ⟨g.phase + g.phase + tau (betaPair g g), g.x + g.x, g.z + g.z⟩ := rfl
  have xx : g.x + g.x = 0 := by ext i; simp [CharTwo.add_self_eq_zero]
  have zz : g.z + g.z = 0 := by ext i; simp [CharTwo.add_self_eq_zero]
  -- The phase of g * g is 2*phase + tau(betaPair g g), which is 0 or 2 in ZMod 4
  -- So g * g is either 1 or -I. Since -I ∉ S, we have g * g = 1.
  have key : ∀ (p : ZMod 4) (bp : ZMod 2),
      (⟨p + p + tau bp, (0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2)⟩ : PauliOp n) = 1 ∨
      (⟨p + p + tau bp, (0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2)⟩ : PauliOp n) = negI n := by
    intro p bp
    fin_cases p <;> fin_cases bp <;>
      simp [negI] <;>
      (try left; rfl) <;> (try right; rfl)
  -- Rewrite g * g using mul_self, xx, zz
  rw [mul_self, xx, zz] at hsq ⊢
  -- Now hsq says g * g = ⟨phase + phase + tau betaPair, 0, 0⟩ ∈ S.carrier
  cases key g.phase (betaPair g g) with
  | inl h => exact h
  | inr h => exact absurd hsq (by rw [h]; exact S.negI_notMem)

/-- Every stabilizer element is represented by a Hermitian matrix. -/
theorem isHermitian_toMat {g : PauliOp n} (hg : g ∈ S.carrier) : (toMat g).IsHermitian := by
  -- Key fact: g² = 1, so (toMat g)² = 1
  have hsq : g * g = 1 := S.sq_eq_one hg
  have hsq' : toMat g * toMat g = 1 := by rw [← toMat_mul, hsq, toMat_one]
  -- toMat g is unitary
  have huntary : toMat g ∈ Matrix.unitaryGroup (Fin n → ZMod 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simp only [toMat]
    -- star (I^k • Pauli) * (I^k • Pauli) = conj(I^k) * I^k • star(Pauli) * Pauli = 1 • 1 = 1
    rw [star_smul, smul_mul_smul_comm]
    -- Use that pauliOp is unitary
    have hunit := pauliOp_mem_unitaryGroup (g.x, g.z)
    rw [Matrix.mem_unitaryGroup_iff'] at hunit
    -- conj(I^k) * I^k = |I^k|^2 = 1
    have hphase : star (Complex.I ^ g.phase.val : ℂ) * Complex.I ^ g.phase.val = 1 := by
      rw [star_pow, ← mul_pow]
      simp [Complex.I_mul_I]
    rw [hphase, one_smul, hunit]
  -- For unitary U with U² = 1: star U = U⁻¹ = U, so U is Hermitian
  let U : ↥(Matrix.unitaryGroup (Fin n → ZMod 2) ℂ) := ⟨toMat g, huntary⟩
  have hstar : star (U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) = (↑U)⁻¹ := by
    have h := Matrix.UnitaryGroup.star_mul_self U
    rw [mul_eq_one_comm] at h
    exact (Matrix.inv_eq_right_inv h).symm
  -- From U * U = 1, we have U⁻¹ = U
  have hinv : (↑U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)⁻¹ = ↑U := by
    exact Matrix.inv_eq_right_inv hsq'
  have : (↑U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) = g.toMat := rfl
  simp only [this] at hstar hinv
  unfold Matrix.IsHermitian
  exact hstar.trans hinv

/-- The identity is the only scalar Pauli in a stabilizer, so non-identity elements are
traceless. -/
theorem toMat_trace_of_mem {g : PauliOp n} (hg : g ∈ S.carrier) :
    (toMat g).trace = if g = 1 then (2 ^ n : ℂ) else 0 := by
  rw [toMat_trace]
  by_cases hg0 : g.x = 0 ∧ g.z = 0
  · -- case: g.x = 0 ∧ g.z = 0
    simp only [hg0, and_self, ↓reduceIte]
    by_cases hg1 : g = 1
    · simp [hg1]
    · -- g ≠ 1 but g.x = 0 ∧ g.z = 0, derive contradiction
      simp [hg1]
      -- Use sq_eq_one: g * g = 1
      have hsq := sq_eq_one S hg
      -- g = ⟨g.phase, 0, 0⟩, so g * g = ⟨2*g.phase, 0, 0⟩ = 1 means 2*g.phase = 0
      have hc : g = ⟨g.phase, g.x, g.z⟩ := rfl
      simp [hg0] at hc
      -- Compute g * g using the PauliOp multiplication rules
      have hmul : g * g = ⟨2 * g.phase, 0, 0⟩ := by
        conv_lhs => rw [hc]
        ext <;> simp [mul_phase, mul_x, mul_z, tau, betaPair]
        ring
      -- From hmul and hsq: ⟨2 * g.phase, 0, 0⟩ = 1
      have h2phase : 2 * g.phase = 0 := by
        have h := hmul ▸ hsq
        exact congrArg (fun p => p.phase) h
      -- g.phase ∈ {0, 2}
      have hcases : g.phase = 0 ∨ g.phase = 2 := by
        match hp : g.phase with
        | 0 => left; rfl
        | 1 => simp [hp] at h2phase; trivial
        | 2 => right; rfl
        | 3 => simp [hp] at h2phase; trivial
      rcases hcases with hp0 | hp2
      · -- g.phase = 0 means g = 1
        apply hg1
        rw [hc, hp0]
        rfl
      · -- g.phase = 2 means g = negI
        apply S.negI_notMem
        have : g = negI n := by rw [hc, hp2]; rfl
        rwa [this] at hg
  · -- case: ¬(g.x = 0 ∧ g.z = 0)
    simp [hg0]
    intro hg1
    simp [hg1] at hg0

/-! ### The code space and its projector -/

/-- The **code space**: the joint `+1`-eigenspace of every stabilizer element. -/
noncomputable def codeSpace : Submodule ℂ ((Fin n → ZMod 2) → ℂ) :=
  ⨅ g : S.carrier, LinearMap.ker (Matrix.toLin' (toMat (g : PauliOp n)) - LinearMap.id)

/-- The **stabilizer projector** `|S|⁻¹ ∑_{g∈S} g`. -/
noncomputable def stabProj : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  (Fintype.card S.carrier : ℂ)⁻¹ • ∑ g : S.carrier, toMat (g : PauliOp n)

/-- `stabProj` is idempotent: it is a genuine projector (uses the group structure). -/
theorem stabProj_idem : stabProj S * stabProj S = stabProj S := by
  simp [stabProj]
  -- Goal: (↑(Fintype.card ↥S.carrier))⁻¹ • ((∑ g, (↑g).toMat) * ∑ g, (↑g).toMat) = ∑ g, (↑g).toMat
  -- First expand the product of sums
  have h1 : (∑ g : S.carrier, (g : PauliOp n).toMat) * ∑ h : S.carrier, (h : PauliOp n).toMat =
            ∑ g : S.carrier, ∑ h : S.carrier, (g : PauliOp n).toMat * (h : PauliOp n).toMat := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.mul_sum]
  rw [h1]
  -- toMat is a representation, so toMat g * toMat h = toMat (g * h)
  have h2 : ∀ g h : S.carrier, (g : PauliOp n).toMat * (h : PauliOp n).toMat =
            ((g * h : S.carrier) : PauliOp n).toMat := by
    intro g h
    rw [← toMat_mul]
    rfl
  -- Replace with toMat (g * h)
  simp_rw [h2]
  -- For each g, inner sum ∑ h, toMat(g * h) = ∑ h, toMat(h) since left mult by g is a bijection
  have h3 : ∀ g : S.carrier, ∑ h : S.carrier, ((g * h : S.carrier) : PauliOp n).toMat =
            ∑ h : S.carrier, ((h : S.carrier) : PauliOp n).toMat := by
    intro g
    let f : S.carrier ≃ S.carrier := ⟨fun h => g * h, fun h => g⁻¹ * h,
      fun h => by simp, fun h => by simp⟩
    conv_rhs => rw [← Equiv.sum_comp f]
    rfl
  -- Inner sums are all equal
  simp_rw [h3]
  -- Now ∑ x, (∑ h, toMat h) = |S| • (∑ h, toMat h)
  simp [Finset.sum_const]
  have hcard : (Fintype.card S.carrier : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  -- Goal: (↑n)⁻¹ • (↑n * M) = M
  rw [Algebra.smul_def, ← mul_assoc]
  field_simp [hcard]
  conv_lhs => rw [show (↑(Fintype.card S.carrier) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) =
    algebraMap ℂ _ (↑(Fintype.card S.carrier)) by rfl]
  rw [← map_mul, div_mul_cancel₀ _ hcard, map_one, one_mul]

/-- The stabilizer projector projects exactly onto the code space. -/
theorem range_stabProj :
    LinearMap.range (Matrix.toLin' (stabProj S)) = codeSpace S := by
  have key : ∀ g : PauliOp n, g ∈ S.carrier → toMat g * stabProj S = stabProj S := by
    intro g hg
    simp only [stabProj]
    rw [Matrix.mul_smul]
    have h1 : g.toMat * ∑ h : S.carrier, (h : PauliOp n).toMat = ∑ h : S.carrier, (h : PauliOp n).toMat := by
      let equiv : S.carrier ≃ S.carrier := Equiv.mulLeft (Subtype.mk g hg)
      rw [Finset.mul_sum]
      rw [Fintype.sum_equiv equiv]
      intro h
      have heq : (equiv h : PauliOp n) = g * h := by
        simp [equiv, Equiv.coe_mulLeft]
      have heq2 : equiv h = Subtype.mk (g * h) (S.carrier.mul_mem hg h.prop) := Subtype.ext heq
      rw [heq2, ← toMat_mul]
    rw [h1]
  apply le_antisymm
  · -- range(stabProj S) ⊆ codeSpace S
    intro v hv
    rw [LinearMap.mem_range] at hv
    obtain ⟨w, hw⟩ := hv
    rw [codeSpace, Submodule.mem_iInf]
    intro i
    rw [LinearMap.mem_ker]
    rw [← hw]
    have h2 : (Matrix.toLin' (i.1.toMat)) (Matrix.toLin' (stabProj S) w) =
              Matrix.toLin' (stabProj S) w := by
      have h := key i.1 i.2
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h]
    rw [LinearMap.sub_apply, LinearMap.id_apply, h2, sub_self]
  · -- codeSpace S ⊆ range(stabProj S)
    intro v hv
    rw [LinearMap.mem_range]
    use v
    rw [codeSpace] at hv
    rw [Submodule.mem_iInf] at hv
    rw [Matrix.toLin'_apply]
    simp only [stabProj]
    simp only [Matrix.smul_mulVec, Matrix.sum_mulVec]
    have hsum' : ∑ i : S.carrier, (i.val.toMat).mulVec v = ∑ _ : S.carrier, v := by
      apply Finset.sum_congr rfl
      intro i _
      have h := (hv i).symm
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Matrix.toLin'_apply] at h
      exact eq_of_sub_eq_zero h.symm
    rw [hsum']
    have hcard : (Fintype.card S.carrier : ℂ) ≠ 0 := by
      simp [Fintype.card_ne_zero]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← smul_eq_mul]
    show ((Fintype.card S.carrier : ℂ)⁻¹) • (((Fintype.card S.carrier : ℂ) • v)) = v
    rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- **Dimension of the code space:** `|S| · dim (codeSpace S) = 2ⁿ`. Equivalently the code space
has dimension `2ⁿ / |S|`. -/
theorem card_mul_codeSpace_finrank :
    Fintype.card S.carrier * Module.finrank ℂ (codeSpace S) = 2 ^ n := by
  -- The trace of stabProj equals the dimension of codeSpace
  have h_idempotent : Matrix.toLin' (stabProj S) * Matrix.toLin' (stabProj S) = Matrix.toLin' (stabProj S) := by
    have := congr_arg Matrix.toLin' (stabProj_idem S)
    simp only [Matrix.toLin'_mul] at this ⊢
    exact this
  --stabProj defines a projection onto codeSpace
  have h_proj : LinearMap.IsProj (codeSpace S) (Matrix.toLin' (stabProj S)) := by
    have h := LinearMap.isProj_range_iff_isIdempotentElem (Matrix.toLin' (stabProj S)) |>.mpr h_idempotent
    rwa [range_stabProj] at h
  -- The trace of stabProj equals the finrank of codeSpace
  have h_trace_eq : Matrix.trace (stabProj S) = Module.finrank ℂ (codeSpace S) := by
    have := LinearMap.IsProj.trace h_proj
    rw [Matrix.trace_toLin'_eq] at this
    exact this
  -- Compute the trace: only identity contributes
  have h_trace_computed : Matrix.trace (stabProj S) = (Fintype.card S.carrier : ℂ)⁻¹ * (2 ^ n : ℂ) := by
    simp [stabProj, Matrix.trace_smul, Matrix.trace_sum]
    have h_sum : ∑ i : S.carrier, (i : PauliOp n).toMat.trace = ∑ i : S.carrier, if (i : PauliOp n) = 1 then (2 ^ n : ℂ) else 0 := by
      congr 1
      ext g
      exact toMat_trace_of_mem S g.prop
    rw [h_sum]
    have heq : ∀ i : S.carrier, (i : PauliOp n) = 1 ↔ i = ⟨1, S.carrier.one_mem⟩ := by
      intro i
      exact ⟨fun h => by ext1; exact h, fun h => by rw [h]⟩
    simp_rw [heq]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset ↑S.carrier) ⟨1, S.carrier.one_mem⟩]
    simp [Finset.mem_univ]
  -- Combine to get the result
  have h_card_pos : Fintype.card S.carrier > 0 := Fintype.card_pos_iff.mpr ⟨1, S.carrier.one_mem⟩
  have h_card_ne_zero : (Fintype.card S.carrier : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h_card_pos)
  rw [h_trace_eq] at h_trace_computed
  field_simp [h_card_ne_zero] at h_trace_computed
  rw [mul_comm] at h_trace_computed
  norm_cast at h_trace_computed

/-! ### Round 2: supporting lemmas -/

/-- Stabilizer operators commute (as matrices), since the group is abelian. -/
theorem toMat_commute_of_mem {g h : PauliOp n} (hg : g ∈ S.carrier) (hh : h ∈ S.carrier) :
    toMat g * toMat h = toMat h * toMat g := by
  have hcomm := S.isComm g hg h hh
  rw [← toMat_mul, hcomm, toMat_mul]

/-- Left-multiplying the projector by any stabilizer operator leaves it fixed (group
invariance) — the crux of idempotency. -/
theorem toMat_mem_mul_stabProj {g : PauliOp n} (hg : g ∈ S.carrier) :
    toMat g * stabProj S = stabProj S := by
  simp [stabProj, Finset.smul_sum]
  rw [Matrix.mul_sum]
  set equiv : S.carrier ≃ S.carrier := {
    toFun a := ⟨g * a, Subgroup.mul_mem _ hg a.2⟩
    invFun a := ⟨g⁻¹ * a, Subgroup.mul_mem _ (Subgroup.inv_mem S.carrier hg) a.2⟩
    left_inv a := by simp
    right_inv a := by simp
  } with hequiv
  conv_lhs => rw [show (∑ a : S.carrier, g.toMat * ((Fintype.card S.carrier : ℂ)⁻¹ • (↑a : PauliOp n).toMat)) 
    = ∑ a : S.carrier, ((Fintype.card S.carrier : ℂ)⁻¹ • (g * ↑a).toMat) by 
      apply Finset.sum_congr rfl; intro a _
      rw [Matrix.mul_smul, toMat_mul]]
  rw [Fintype.sum_equiv equiv]
  intro x
  congr 2

/-- The stabilizer projector is Hermitian. -/
theorem stabProj_isHermitian : (stabProj S).IsHermitian := by
  unfold stabProj
  refine IsSelfAdjoint.smul ?_
    (isSelfAdjoint_sum _ fun g _ => isHermitian_toMat S g.property)
  rw [isSelfAdjoint_iff]; simp

/-- Trace of the stabilizer projector: `2ⁿ / |S|`. -/
theorem stabProj_trace : (stabProj S).trace = (2 ^ n : ℂ) / Fintype.card S.carrier := by
  unfold stabProj
  rw [Matrix.trace_smul]
  simp only [Matrix.trace_sum]
  have h : ∀ x : ↥S.carrier, Matrix.trace (toMat (x : PauliOp n)) = ite (x = 1) (2 ^ n : ℂ) 0 := by
    intro ⟨g, hg⟩
    simp only [toMat_trace_of_mem (S := S) hg]
    congr 1
    simp
  simp_rw [h]
  -- The sum is 2^n since only identity contributes
  have hc : ∑ x : ↥S.carrier, (if x = 1 then (2 ^ n : ℂ) else 0) = 2 ^ n := by
    simp
  rw [hc]
  rw [div_eq_mul_inv, mul_comm]
  simp [smul_eq_mul]

end StabGroup

/-- Bridge to the symplectic form: two Pauli group operators commute iff the symplectic form of
their underlying labels vanishes. -/
theorem toMat_commute_iff (P Q : PauliOp n) :
    toMat P * toMat Q = toMat Q * toMat P
      ↔ symplecticForm (P.x, P.z) (Q.x, Q.z) = 0 := by
  simp only [toMat]
  rw [smul_mul_smul_comm, smul_mul_smul_comm]
  have hscalar_comm : Complex.I ^ P.phase.val * Complex.I ^ Q.phase.val =
      Complex.I ^ Q.phase.val * Complex.I ^ P.phase.val := mul_comm _ _
  rw [hscalar_comm]
  have hscalar_ne_zero : Complex.I ^ Q.phase.val * Complex.I ^ P.phase.val ≠ 0 := by
    apply mul_ne_zero <;> exact pow_ne_zero _ Complex.I_ne_zero
  let scalar := Complex.I ^ Q.phase.val * Complex.I ^ P.phase.val
  have hunit : IsUnit scalar := by
    rw [isUnit_iff_ne_zero]
    exact hscalar_ne_zero
  let A := Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ
  have hcancel : Function.Injective (fun A : A => scalar • A) := hunit.smul_bijective.injective
  show scalar • (pauliOp (P.x, P.z) * pauliOp (Q.x, Q.z)) =
    scalar • (pauliOp (Q.x, Q.z) * pauliOp (P.x, P.z)) ↔ _
  rw [hcancel.eq_iff]
  exact QuantumLib.pauliOp_commute_iff (P.x, P.z) (Q.x, Q.z)

/-! ### Round 3: weight, distance, and code-space corollaries -/

/-- The weight of a Pauli group element: the number of qubits it acts on nontrivially. -/
def weight (P : PauliOp n) : ℕ :=
  (Finset.univ.filter (fun i => P.x i ≠ 0 ∨ P.z i ≠ 0)).card

@[simp] theorem weight_one : weight (1 : PauliOp n) = 0 := by
  simp [weight]

theorem weight_le (P : PauliOp n) : weight P ≤ n := by
  simpa [weight] using Finset.card_filter_le Finset.univ (fun i => P.x i ≠ 0 ∨ P.z i ≠ 0)

theorem weight_eq_zero_iff (P : PauliOp n) : weight P = 0 ↔ P.x = 0 ∧ P.z = 0 := by
  simp [weight, funext_iff, forall_and]

@[simp] theorem weight_inv (P : PauliOp n) : weight P⁻¹ = weight P := rfl

theorem weight_mul_le (P Q : PauliOp n) : weight (P * Q) ≤ weight P + weight Q := by
  unfold weight
  simp only [mul_x, mul_z]
  have hpxq : ∀ a b : ZMod 2, a + b ≠ 0 → a ≠ 0 ∨ b ≠ 0 := by decide
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ] at hi ⊢
  rcases hi with ⟨_, hx | hz⟩
  · have := hpxq _ _ hx; tauto
  · have := hpxq _ _ hz; tauto

namespace StabGroup
variable (S : StabGroup n)

/-- The global-phase subgroup `{iᵏ·I} = ⟨iI⟩`. -/
def phaseSubgroup (n : ℕ) : Subgroup (PauliOp n) where
  carrier := {g | g.x = 0 ∧ g.z = 0}
  mul_mem' := by
    rintro a b ⟨hax, haz⟩ ⟨hbx, hbz⟩
    exact ⟨by simp [mul_x, hax, hbx], by simp [mul_z, haz, hbz]⟩
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' := by rintro a ⟨hax, haz⟩; exact ⟨hax, haz⟩

@[simp] theorem mem_phaseSubgroup {g : PauliOp n} :
    g ∈ phaseSubgroup n ↔ g.x = 0 ∧ g.z = 0 := Iff.rfl

/-- A weight-zero Pauli (a global phase) lies in the phase subgroup. -/
theorem mem_phaseSubgroup_of_weight_zero {g : PauliOp n} (h : weight g = 0) :
    g ∈ phaseSubgroup n := (weight_eq_zero_iff g).mp h

/-- A **logical operator**: commutes with the whole stabilizer but is not *trivial* — it lies
outside the subgroup generated by the stabilizer and the global phases. Excluding phases is
essential: otherwise `-I` (weight 0) would count as a logical and force `distance = 0`. -/
def IsLogical (g : PauliOp n) : Prop :=
  g ∈ Subgroup.centralizer (S.carrier : Set (PauliOp n)) ∧ g ∉ S.carrier ⊔ phaseSubgroup n

/-- The **code distance**: the minimum weight of a nontrivial logical operator. -/
noncomputable def distance : ℕ := sInf {w | ∃ g, S.IsLogical g ∧ weight g = w}

/-- A logical operator has positive weight (weight-zero Paulis are phases, hence trivial). -/
theorem isLogical_weight_pos {g : PauliOp n} (hg : S.IsLogical g) : 0 < weight g := by
  rcases Nat.eq_zero_or_pos (weight g) with h0 | h
  · exact absurd (Subgroup.mem_sup_right (mem_phaseSubgroup_of_weight_zero h0)) hg.2
  · exact h

/-- The stabilizer order divides `2ⁿ`. -/
theorem card_carrier_dvd : Fintype.card S.carrier ∣ 2 ^ n :=
  ⟨Module.finrank ℂ (codeSpace S), (card_mul_codeSpace_finrank S).symm⟩

/-- The code space has dimension `2ⁿ / |S|`. -/
theorem finrank_codeSpace :
    Module.finrank ℂ (codeSpace S) = 2 ^ n / Fintype.card S.carrier := by
  have h := card_mul_codeSpace_finrank S
  exact (Nat.div_eq_of_eq_mul_right (Fintype.card_pos_iff.mpr ⟨1, S.carrier.one_mem⟩) h.symm).symm

/-- The code space is nontrivial: it has positive dimension `2ⁿ/|S| ≥ 1`. -/
theorem codeSpace_ne_bot : codeSpace S ≠ ⊥ := by
  intro h
  have heq := card_mul_codeSpace_finrank S
  rw [h, finrank_bot, mul_zero] at heq
  exact absurd heq (Nat.two_pow_pos n).ne

/-! ### Round 4: error detection and correction -/

/-- An error `E` is **detectable** by `S` if it lies in the stabilizer (harmless) or anticommutes
with some stabilizer element (it flips a syndrome bit). -/
def Detectable (E : PauliOp n) : Prop :=
  E ∈ S.carrier ⊔ phaseSubgroup n ∨ ∃ g ∈ S.carrier, E * g ≠ g * E

/-- A logical operator has weight at least the code distance. -/
theorem distance_le_weight_of_logical {g : PauliOp n} (hg : S.IsLogical g) :
    S.distance ≤ weight g :=
  Nat.sInf_le ⟨g, hg, rfl⟩

/-- **Detection below the distance:** every Pauli error of weight `< distance` is detectable —
undetectable nontrivial errors are logical operators, which have weight `≥ distance`. -/
theorem detectable_of_weight_lt_distance {E : PauliOp n} (hw : weight E < S.distance) :
    S.Detectable E := by
  by_cases hE : E ∈ S.carrier ⊔ phaseSubgroup n
  · exact Or.inl hE
  · right
    by_contra h
    push_neg at h
    have hcomm : E ∈ Subgroup.centralizer (S.carrier : Set (PauliOp n)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (h g hg).symm
    have hlogical : S.IsLogical E := ⟨hcomm, hE⟩
    exact hw.not_ge (S.distance_le_weight_of_logical hlogical)

/-- **Correction below half the distance:** if `2·weight E < distance` for every error, then the
composite `E₁⁻¹E₂` of two such errors is detectable — the Knill–Laflamme condition for the
stabilizer code, so such an error set is correctable. -/
theorem detectable_mul_of_weight_lt {E₁ E₂ : PauliOp n}
    (h₁ : 2 * weight E₁ < S.distance) (h₂ : 2 * weight E₂ < S.distance) :
    S.Detectable (E₁⁻¹ * E₂) := by
  apply S.detectable_of_weight_lt_distance
  calc weight (E₁⁻¹ * E₂) ≤ weight E₁⁻¹ + weight E₂ := weight_mul_le _ _
    _ = weight E₁ + weight E₂ := by rw [weight_inv]
    _ < S.distance := by omega

/-! ### Round 5: a grab-bag of stated facts (sorrymaxxing) -/

/-- The stabilizer projector fixes every code state. -/
theorem stabProj_apply_of_mem {v : (Fin n → ZMod 2) → ℂ} (hv : v ∈ codeSpace S) :
    Matrix.toLin' (stabProj S) v = v := by
  rw [← range_stabProj] at hv
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv
  have hidem := stabProj_idem S
  have heq : Matrix.toLin' (stabProj S) ∘ₗ Matrix.toLin' (stabProj S) = Matrix.toLin' (stabProj S) := by
    rw [← Matrix.toLin'_mul]
    simp [hidem]
  rw [← hw]
  exact LinearMap.congr_fun heq w

/-- The stabilizer projector is a projection onto the code space. -/
theorem stabProj_isProj : LinearMap.IsProj (codeSpace S) (Matrix.toLin' (stabProj S)) := by
  have h_idempotent : Matrix.toLin' (stabProj S) * Matrix.toLin' (stabProj S) = Matrix.toLin' (stabProj S) := by
    have := congr_arg Matrix.toLin' (stabProj_idem S)
    simp only [Matrix.toLin'_mul] at this ⊢
    exact this
  rw [← range_stabProj]
  exact (LinearMap.isProj_range_iff_isIdempotentElem (Matrix.toLin' (stabProj S))).mpr h_idempotent

/-- The stabilizer order is a power of two. -/
theorem card_carrier_eq_two_pow : ∃ k, Fintype.card S.carrier = 2 ^ k := by
  -- Every element of S.carrier squares to 1, so it's an elementary abelian 2-group
  -- Hence its cardinality is a power of 2
  have h_exp_two : ∀ g : S.carrier, g.1 * g.1 = 1 := fun g => S.sq_eq_one g.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Show that S.carrier is a 2-group
  haveI : IsPGroup 2 (↥S.carrier) := fun g => ⟨1, by
    have h := h_exp_two g
    simp [pow_two] at h ⊢
    exact Subtype.ext h⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ‹IsPGroup 2 (↥S.carrier)›
  exact ⟨k, Fintype.card_eq_nat_card ▸ hk⟩

/-- **Quantum Singleton bound** for stabilizer codes: `dim (codeSpace) ≤ 2^(n - 2(d-1))`. -/
theorem singleton_bound :
    Module.finrank ℂ (codeSpace S) ≤ 2 ^ (n - 2 * (S.distance - 1)) := by
  -- The genuine quantum Singleton bound (previously proved only vacuously via distance = 0).
  sorry

/-- The code space is the whole space iff the stabilizer is trivial. -/
theorem codeSpace_eq_top_iff : codeSpace S = ⊤ ↔ S.carrier = ⊥ := by
  constructor
  · intro h
    -- If codeSpace = ⊤, then every g ∈ S.carrier acts as identity on all vectors
    -- So toMat g = I for all g ∈ S.carrier, hence g = 1
    ext g
    simp only [Subgroup.mem_bot]
    constructor
    · intro hg
      -- codeSpace = ⊤ means ker(toMat g - id) = ⊤ for all g ∈ S.carrier
      have hker : ∀ g' : S.carrier, (Matrix.toLin' (g'.1.toMat) - LinearMap.id).ker = ⊤ := by
        intro g'
        have hle : codeSpace S ≤ LinearMap.ker ((Matrix.toLin' (g'.1.toMat)) - LinearMap.id) :=
          iInf_le _ g'
        rw [h] at hle
        exact le_top.antisymm hle
      -- For our g, we have (toLin' (toMat g) - id).ker = ⊤
      have hgker := hker ⟨g, hg⟩
      -- This means toLin' (toMat g) - id = 0, so toLin' (toMat g) = id
      have heq : Matrix.toLin' (g.toMat) - LinearMap.id = 0 := by
        simpa using hgker
      have heqn : Matrix.toLin' g.toMat = LinearMap.id := sub_eq_zero.mp heq
      -- toLin' is injective, so g.toMat = 1
      have htoMat : g.toMat = 1 := by
        have h1 : Matrix.toLin' (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) = LinearMap.id := by
          ext; simp
        rw [← h1] at heqn
        exact Matrix.toLin'.injective heqn
      -- g.toMat = 1 implies g = 1 (follows from toMat being injective)
      -- We prove a local version of injectivity: if toMat g = 1, then g = 1
      have toMat_eq_one_iff : ∀ P : PauliOp n, P.toMat = 1 → P = 1 := by
        intro P hP
        -- Use trace: trace(P.toMat) = trace(1) = 2^n
        -- trace(P.toMat) = I^P.phase • trace(pauliOp(P.x, P.z))
        -- If (P.x, P.z) ≠ 0, trace = 0, contradiction
        have htrace := toMat_trace P
        rw [hP] at htrace
        simp at htrace
        -- From htrace: 2^n = if P.x = 0 ∧ P.z = 0 then I^P.phase * 2^n else 0
        -- This implies P.x = 0 ∧ P.z = 0 (else 2^n = 0)
        have hxz : P.x = 0 ∧ P.z = 0 := by
          by_contra h
          simp [h] at htrace
        -- From htrace with hxz: 2^n = I^P相位 * 2^n, so I^P相位 = 1, meaning P相位 = 0
        rw [hxz.1, hxz.2] at htrace
        simp at htrace
        -- htrace : Complex.I ^ P.phase.val = 1
        -- Complex.I ^ k = 1 iff k = 0 mod 4
        have hphase_zero : P.phase.val = 0 := by
          have : P.phase.val < 4 := ZMod.val_lt P.phase
          interval_cases P.phase.val <;> simp_all
          · have := Complex.I_re; simp_all [Complex.ext_iff]
          · norm_num at htrace
          · have := Complex.I_re; simp_all [Complex.ext_iff]
        have hphase : P.phase = 0 := by
          exact ZMod.natCast_zmod_val (P.phase) ▸ hphase_zero ▸ rfl
        -- P = 1 follows from P.phase = 0, P.x = 0, P.z = 0
        ext <;> simp [hphase, hxz]
      exact toMat_eq_one_iff g htoMat
    · intro h
      rw [h]
      exact S.carrier.one_mem
  · intro h
    -- When carrier = ⊥, the only element is 1
    simp only [codeSpace]
    -- The infimum over a singleton is just that subspace
    have hsub : Subsingleton S.carrier := by
      refine ⟨fun a b => ?_⟩
      have ha : (a : PauliOp n) = 1 := by simpa [h] using a.2
      have hb : (b : PauliOp n) = 1 := by simpa [h] using b.2
      exact Subtype.ext (ha.trans hb.symm)
    simp only [iInf_eq_top]
    intro a
    have ha : (a : PauliOp n) = 1 := by simpa [h] using a.2
    simp [ha]

/-- Stabilizer elements are (trivially) detectable errors. -/
theorem detectable_of_mem {E : PauliOp n} (hE : E ∈ S.carrier) : S.Detectable E :=
  Or.inl (Subgroup.mem_sup_left hE)

/-- A code with no weight-`≤ d` logical operator has distance `> d`. -/
theorem lt_distance_of_no_logical (d : ℕ) (hex : ∃ g, S.IsLogical g)
    (h : ∀ E : PauliOp n, weight E ≤ d → ¬ S.IsLogical E) : d < S.distance := by
  unfold StabGroup.distance
  obtain ⟨g0, hg0⟩ := hex
  have hne : {w | ∃ g, S.IsLogical g ∧ weight g = w}.Nonempty := ⟨weight g0, g0, hg0, rfl⟩
  obtain ⟨g, hlog, hwt⟩ := Nat.sInf_mem hne
  by_contra hd
  push_neg at hd
  exact h g (hwt.trans_le hd) hlog

/-- An error either commutes with the whole stabilizer or is detectable. -/
theorem detectable_or_mem_centralizer (E : PauliOp n) :
    S.Detectable E ∨ E ∈ Subgroup.centralizer (S.carrier : Set (PauliOp n)) := by
  by_cases h : ∀ g ∈ S.carrier, E * g = g * E
  · -- E commutes with all stabilizer elements, so E is in the centralizer
    right
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (h g hg).symm
  · -- E anticommutes with some stabilizer element, so E is detectable
    left
    simp only [StabGroup.Detectable]
    push_neg at h
    obtain ⟨g, hg, hneq⟩ := h
    right
    exact ⟨g, hg, hneq⟩

end StabGroup

/-! #### Faithfulness of the Pauli representation -/

/-- The matrix representation of the Pauli group is faithful. -/
theorem toMat_injective : Function.Injective (toMat (n := n)) := by
  intro P Q h
  -- toMat P = toMat Q, so their traces match
  simp only [toMat] at h
  have htrace := congrArg Matrix.trace h
  simp [Matrix.trace_smul] at htrace
  -- The trace of pauliOp is 2^n when pauli = 0, else 0
  by_cases hP0 : (P.x, P.z) = 0
  · by_cases hQ0 : (Q.x, Q.z) = 0
    · -- Both are zero paulis, so traces give phase equality
      have htrace' : Complex.I ^ P.phase.val = Complex.I ^ Q.phase.val := by
        simp [pauliOp_trace, hP0, hQ0] at htrace
        exact htrace
      have hphase_eq : P.phase = Q.phase := by
        have hP : P.phase.val < 4 := ZMod.val_lt P.phase
        have hQ : Q.phase.val < 4 := ZMod.val_lt Q.phase
        exact ZMod.val_injective 4 (I_pow_lt_four_injective _ _ hP hQ htrace')
      rw [Prod.mk_eq_zero] at hP0 hQ0
      obtain ⟨hPx, hPz⟩ := hP0
      obtain ⟨hQx, hQz⟩ := hQ0
      exact PauliOp.ext_iff.mpr ⟨hphase_eq, hPx.trans hQx.symm, hPz.trans hQz.symm⟩
    · simp [pauliOp_trace, hP0, hQ0] at htrace
  · by_cases hQ0 : (Q.x, Q.z) = 0
    · simp [pauliOp_trace, hP0, hQ0] at htrace
    · simp [pauliOp_trace, hP0, hQ0] at htrace
      -- htrace : 0 = 0 (True), both non-zero
      -- Now we know both are 0 or both are non-zero
      by_cases hP0' : (P.x, P.z) = (Q.x, Q.z)
      · -- Same pauliOp, need to show same phase
        -- Use original hypothesis h: I^P.phase • pauliOp(P.x,P.z) = I^Q.phase • pauliOp(Q.x,Q.z)
        -- Since (P.x,P.z) = (Q.x,Q.z), pauliOps are equal, so phases must be equal
        have hpauli_eq : pauliOp (P.x, P.z) = pauliOp (Q.x, Q.z) := by rw [hP0']
        rw [hpauli_eq] at h
        have hphase : P.phase = Q.phase := by
          have hP : P.phase.val < 4 := ZMod.val_lt P.phase
          have hQ : Q.phase.val < 4 := ZMod.val_lt Q.phase
          -- The 4 powers of I are distinct
          -- Pick an entry where pauliOp is nonzero: u = Q.x, v = 0
          -- Then u = v + Q.x is satisfied (0 + Q.x = Q.x)
          let u : Fin n → ZMod 2 := Q.x
          let v : Fin n → ZMod 2 := 0
          have huv : u = v + Q.x := by ext i; simp [u, v]
          have hentry := congr_fun (congr_fun h u) v
          simp [pauliOp, huv] at hentry
          have hprod : ∏ x, (-1 : ℂ) ^ (Q.z x * v x).val = 1 := by
            simp [v]
          rw [hprod] at hentry
          rcases hentry with heq | hzero
          · exact ZMod.val_injective 4 (I_pow_lt_four_injective _ _ hP hQ heq)
          · norm_num at hzero
        have hx : P.x = Q.x := Prod.ext_iff.mp hP0' |>.1
        have hz : P.z = Q.z := Prod.ext_iff.mp hP0' |>.2
        exact PauliOp.ext_iff.mpr ⟨hphase, hx, hz⟩
      · -- Different paulis: use inner product with A = pauliOp(P.x, P.z)
        let A := pauliOp (P.x, P.z)
        let B := pauliOp (Q.x, Q.z)
        have hPadd : (P.x, P.z) ≠ (Q.x, Q.z) := hP0'
        have hBA_eq : Q.x + P.x = 0 ∧ Q.z + P.z = 0 → False := by
          intro ⟨hqx, hqz⟩
          apply hPadd
          simp only [Prod.mk.injEq]
          refine ⟨funext fun i => ?_, funext fun i => ?_⟩
          · have := congr_fun hqx i; simp only [Pi.add_apply, Pi.zero_apply] at this; rw [add_eq_zero_iff_eq_neg] at this; simp at this; exact this.symm
          · have := congr_fun hqz i; simp only [Pi.add_apply, Pi.zero_apply] at this; rw [add_eq_zero_iff_eq_neg] at this; simp at this; exact this.symm
        have inner := congrArg Matrix.trace (congrArg (· * A) h)
        simp only [Matrix.smul_mul] at inner
        have hAA : A * A = 1 ∨ A * A = -1 := by
          have hsum : (P.x, P.z) + (P.x, P.z) = 0 := by
            have h1 : P.x + P.x = 0 := by
              ext i
              simp [CharTwo.add_self_eq_zero]
            have h2 : P.z + P.z = 0 := by
              ext i
              simp [CharTwo.add_self_eq_zero]
            simp [h1, h2]
          have hmul := pauliOp_mul (P.x, P.z) (P.x, P.z)
          rw [hsum, pauliOp_zero] at hmul
          -- hmul : A * A = scalar • 1 where scalar = ±1
          have hscalar : (∏ i, (-1 : ℂ) ^ ((P.x, P.z).2 i * (P.x, P.z).1 i).val) = 1 ∨
                         (∏ i, (-1 : ℂ) ^ ((P.x, P.z).2 i * (P.x, P.z).1 i).val) = -1 := by
            have heach : ∀ i, (-1 : ℂ) ^ ((P.x, P.z).2 i * (P.x, P.z).1 i).val = 1 ∨
                            (-1 : ℂ) ^ ((P.x, P.z).2 i * (P.x, P.z).1 i).val = -1 := by
              intro i
              have hmem : ((P.x, P.z).2 i * (P.x, P.z).1 i : ZMod 2).val = 0 ∨
                         ((P.x, P.z).2 i * (P.x, P.z).1 i : ZMod 2).val = 1 := by
                have := ZMod.val_lt ((P.x, P.z).2 i * (P.x, P.z).1 i)
                omega
              rcases hmem with h0 | h1
              · simp [h0]
              · simp [h1]
            have hlist : ∀ (l : List ℂ), (∀ x ∈ l, x = 1 ∨ x = -1) → l.prod = 1 ∨ l.prod = -1 := by
              intro l hl
              induction l with
              | nil => left; rfl
              | cons x xs ih =>
                have hx := hl x (List.Mem.head _)
                have hxs := fun y hy => hl y (List.Mem.tail _ hy)
                rcases hx with rfl | rfl <;> rcases ih hxs with h1 | h1 <;> simp [h1]
            exact hlist _ (by simpa using heach)
          rw [hmul] at ⊢
          rcases hscalar with hscalar | hscalar <;> simp [hscalar]
        have hBA : B * A = (∏ i, (-1 : ℂ) ^ ((Q.x, Q.z).2 i * (P.x, P.z).1 i).val) •
            pauliOp (Q.x + P.x, Q.z + P.z) := by
          exact pauliOp_mul (Q.x, Q.z) (P.x, P.z)
        have hinner : Complex.I ^ P.phase.val • (A * A).trace = Complex.I ^ Q.phase.val • (B * A).trace := by
          simp only [Matrix.trace_smul, smul_eq_mul] at inner ⊢
          exact inner
        rcases hAA with hAA | hAA
        · rw [hAA] at hinner; simp at hinner
          by_cases hsum : (Q.x + P.x, Q.z + P.z) = 0
          · exact False.elim (hBA_eq ⟨by simpa using congr_arg Prod.fst hsum, by simpa using congr_arg Prod.snd hsum⟩)
          · have htrace_BA : (pauliOp (Q.x + P.x, Q.z + P.z)).trace = 0 := by
              simp [pauliOp_trace, hsum]
            have hBA_trace : (B * A).trace = 0 := by
              rw [hBA, Matrix.trace_smul, htrace_BA, smul_zero]
            rw [hBA_trace] at hinner
            simp only [mul_zero] at hinner
            have : (2 : ℂ) ^ n ≠ 0 := by norm_num
            have : Complex.I ^ P.phase.val ≠ 0 := by
              have : Complex.I ≠ 0 := by norm_num
              simp [pow_eq_zero_iff', this]
            exact absurd hinner (mul_ne_zero this ‹(2 : ℂ) ^ n ≠ 0›)
        · rw [hAA] at hinner; simp at hinner
          by_cases hsum : (Q.x + P.x, Q.z + P.z) = 0
          · exact False.elim (hBA_eq ⟨by simpa using congr_arg Prod.fst hsum, by simpa using congr_arg Prod.snd hsum⟩)
          · have htrace_BA : (pauliOp (Q.x + P.x, Q.z + P.z)).trace = 0 := by
              simp [pauliOp_trace, hsum]
            have hBA_trace : (B * A).trace = 0 := by
              rw [hBA, Matrix.trace_smul, htrace_BA, smul_zero]
            rw [hBA_trace] at hinner
            simp only [mul_zero, neg_eq_zero] at hinner
            have : (2 : ℂ) ^ n ≠ 0 := by norm_num
            have : Complex.I ^ P.phase.val ≠ 0 := by
              have : Complex.I ≠ 0 := by norm_num
              simp [pow_eq_zero_iff', this]
            exact absurd hinner (mul_ne_zero this ‹(2 : ℂ) ^ n ≠ 0›)

/-- Every Pauli group element is unitary. -/
theorem toMat_mem_unitaryGroup (P : PauliOp n) :
    toMat P ∈ Matrix.unitaryGroup (Fin n → ZMod 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simp only [toMat]
    rw [star_smul, smul_mul_smul_comm]
    have hunit := pauliOp_mem_unitaryGroup (P.x, P.z)
    rw [Matrix.mem_unitaryGroup_iff'] at hunit
    have hphase : star (Complex.I ^ P.phase.val : ℂ) * Complex.I ^ P.phase.val = 1 := by
      rw [star_pow, ← mul_pow]
      simp [Complex.I_mul_I]
    rw [hphase, one_smul, hunit]

/-- The representation of the inverse is the conjugate-transpose (unitary inverse). -/
theorem toMat_inv (P : PauliOp n) : toMat P⁻¹ = star (toMat P) := by
  have hmul : toMat P * toMat P⁻¹ = 1 := by rw [← toMat_mul]; simp
  rw [← Matrix.inv_eq_right_inv hmul,
    Matrix.inv_eq_left_inv (mul_eq_one_comm.mp (toMat_mem_unitaryGroup P).2)]

end PauliOp

/-! #### General QECC bounds -/

variable {d1 i d2 : Type*} [Fintype i] [DecidableEq i] [Fintype d1] [DecidableEq d1]
  [Fintype d2] [DecidableEq d2]

/-- **Quantum Singleton bound** for a general QECC that corrects `d` errors:
`|d1| · |d2|^(2d) ≤ |d2|^|i|`. -/
theorem QECC.singleton_bound [Nontrivial d1] {C : QECC d1 i d2} {d : ℕ}
    (h : C.CorrectsErrors d) :
    Fintype.card d1 * Fintype.card d2 ^ (2 * d) ≤ Fintype.card d2 ^ Fintype.card i := by
  sorry

/-! ### Round 6: Pauli group structure, trivial code, and the realization bridge -/

namespace PauliOp
variable {m : ℕ}

/-- The `n`-qubit Pauli group has order `4^(n+1)`. -/
theorem card_pauliOp : Fintype.card (PauliOp m) = 4 ^ (m + 1) := by
  rw [Fintype.card_congr equivProd]
  simp [Fintype.card_prod, pow_succ, mul_comm 4]
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, ← pow_add, ← two_mul]

/-- The Pauli representation separates elements. -/
theorem toMat_inj_iff (P Q : PauliOp m) : toMat P = toMat Q ↔ P = Q :=
  ⟨fun h_eq => toMat_injective h_eq, fun h_eq => by rw [h_eq]⟩

/-- Any two Pauli operators either commute or anticommute. -/
theorem toMat_commute_or_anticommute (P Q : PauliOp m) :
    toMat P * toMat Q = toMat Q * toMat P ∨ toMat P * toMat Q = -(toMat Q * toMat P) := by
  simp only [toMat]
  simp only [smul_mul_smul_comm]
  -- The I^phase factors commute
  have hI : Complex.I ^ P.phase.val * Complex.I ^ Q.phase.val = Complex.I ^ Q.phase.val * Complex.I ^ P.phase.val := by
    ring
  rw [hI]
  -- ThePauli matrices multiply to ± the same pauliOp due to betaPair
  -- We use: pauliOp p * pauliOp q = (-1)^(betaPair p q) • pauliOp (p + q)
  rw [pauliOp_mul, pauliOp_mul]
  -- pauliOp (P+Q) = pauliOp (Q+P) since addition is commutative
  have hpq : (P.x, P.z) + (Q.x, Q.z) = (Q.x, Q.z) + (P.x, P.z) := by ext <;> simp [add_comm]
  rw [hpq]
  -- Now compare the scalars. They differ by (-1)^(betaPair P Q - betaPair Q P)
  -- Since betaPair values are in ZMod 2, either they're equal (commute) or different (anticommute)
  by_cases h : (∏ i, (-1 : ℂ) ^ ((P.x, P.z).2 i * (Q.x, Q.z).1 i).val) =
               (∏ i, (-1 : ℂ) ^ ((Q.x, Q.z).2 i * (P.x, P.z).1 i).val)
  · left
    rw [h]
  · right
    -- The products are ±1, so if not equal, they're negatives
    have hprod : (∏ i, (-1 : ℂ) ^ ((P.x, P.z).2 i * (Q.x, Q.z).1 i).val) =
                 (-1 : ℂ) ^ ((betaPair P Q).val) := prod_negOnePow_betaPair P Q
    have hprod2 : (∏ i, (-1 : ℂ) ^ ((Q.x, Q.z).2 i * (P.x, P.z).1 i).val) =
                  (-1 : ℂ) ^ ((betaPair Q P).val) := prod_negOnePow_betaPair Q P
    rw [hprod, hprod2]
    have : (betaPair P Q).val = 0 ∨ (betaPair P Q).val = 1 := by
      have := ZMod.val_lt (betaPair P Q); omega
    have : (betaPair Q P).val = 0 ∨ (betaPair Q P).val = 1 := by
      have := ZMod.val_lt (betaPair Q P); omega
    rcases this with h | h <;> rcases this with h' | h' <;> simp_all

/-- The center of the Pauli group is the scalars `{iᵏ · I}`. -/
theorem mem_center_iff (P : PauliOp m) :
    P ∈ Subgroup.center (PauliOp m) ↔ P.x = 0 ∧ P.z = 0 := by
  constructor
  · intro hP
    -- P ∈ center means P commutes with all Q
    -- Take Q = X_j (x = e_j, z = 0) to get P.z_j = 0
    -- Take Q = Z_j (x = 0, z = e_j) to get P.x_j = 0
    have h_comm := fun Q => Subgroup.mem_center_iff.mp hP Q
    -- Define basis Paulis
    let X : (i : Fin m) → PauliOp m := fun i => ⟨0, fun j => if j = i then 1 else 0, 0⟩
    let Z : (i : Fin m) → PauliOp m := fun i => ⟨0, 0, fun j => if j = i then 1 else 0⟩
    have hx : P.x = 0 := by
      ext j
      -- Use P.commutes_with (Z j) to derive P.x j = 0
      have h := h_comm (Z j)
      -- Extract constraints from Z j * P = P * Z j
      have heq := congrArg PauliOp.x h
      -- This doesn't help; it's trivially true
      -- Instead, use the phase component
      have hphase := congrArg PauliOp.phase h
      simp [Z, mul_phase, betaPair] at hphase
      -- hphase : tau (P.x j) = 0
      -- tau(s) = 2 * s.val, so 2 * (P.x j).val = 0 in ZMod 4
      -- Since P.x j ∈ ZMod 2, its value is 0 or 1
      -- 2 * 0 = 0, 2 * 1 = 2 ≠ 0, so P.x j = 0
      have hcases : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
      rcases hcases (P.x j) with h0 | h1 <;> simp_all [tau]
      have hcast : ZMod.cast (1 : ZMod 2) = (1 : ZMod 4) := rfl
      rw [hcast] at hphase
      exact absurd hphase (by decide)
    have hz : P.z = 0 := by
      ext j
      have h := h_comm (X j)
      have hphase := congrArg PauliOp.phase h
      simp [X, mul_phase, betaPair] at hphase
      -- hphase : tau (P.z j) = 0
      have hcases : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
      rcases hcases (P.z j) with h0 | h1 <;> simp_all [tau]
      have hcast : ZMod.cast (1 : ZMod 2) = (1 : ZMod 4) := rfl
      rw [hcast] at hphase
      exact absurd hphase (by decide)
    exact ⟨hx, hz⟩
  · intro ⟨hx, hz⟩
    rw [Subgroup.mem_center_iff]
    intro Q
    ext
    · simp_all [betaPair]
      ring
    all_goals simp [hx, hz]

namespace StabGroup

/-- The **trivial stabilizer** (only the identity): it protects nothing. -/
def trivial (m : ℕ) : StabGroup m where
  carrier := ⊥
  isComm a ha b hb := by
    obtain rfl := Subgroup.mem_bot.mp ha
    obtain rfl := Subgroup.mem_bot.mp hb
    rfl
  negI_notMem hmem := by
    have h : negI m = 1 := Subgroup.mem_bot.mp hmem
    have h2 : (2 : ZMod 4) = 0 := congrArg PauliOp.phase h
    exact absurd h2 (by decide)

/-- The trivial stabilizer's code space is the whole space. -/
theorem codeSpace_trivial : codeSpace (trivial m) = ⊤ := by
  simp [codeSpace, trivial]
  have h : (default : (⊥ : Subgroup (PauliOp m))) = ⟨1, Subgroup.one_mem _⟩ := rfl
  simp [h, toMat_one, Matrix.toLin'_one]

/-- **Realization bridge:** a stabilizer code correcting `d` errors is realized by a `QECC` on
qubits that corrects `d` errors. -/
theorem exists_qecc_correcting (S : StabGroup m) (k d : ℕ)
    (hk : Fintype.card S.carrier = 2 ^ (m - k)) (hd : 2 * d < S.distance) :
    ∃ C : QECC (Fin k → ZMod 2) (Fin m) (ZMod 2), C.CorrectsErrors d := by sorry

/-! ### Round 8: code parameters `⟦n,k,d⟧` and membership -/

/-- The number of physical qubits `n`. -/
def numPhysical (_ : StabGroup m) : ℕ := m

/-- The number of logical qubits `k = n - log₂|S|`. -/
noncomputable def numLogical (S : StabGroup m) : ℕ := m - Nat.log 2 (Fintype.card S.carrier)

/-- Membership in the code space: a state is in it iff fixed by every stabilizer operator. -/
theorem mem_codeSpace_iff (S : StabGroup m) (v : (Fin m → ZMod 2) → ℂ) :
    v ∈ codeSpace S ↔ ∀ g ∈ S.carrier, Matrix.toLin' (toMat g) v = v := by
  rw [codeSpace]
  rw [Submodule.mem_iInf]
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, sub_eq_zero, LinearMap.id_apply]
  constructor
  · intro h g hg
    exact h ⟨g, hg⟩
  · intro h g
    exact h g g.2

/-- The code space has dimension `2^k` where `k = numLogical` — the `⟦n,k,d⟧` dimension. -/
theorem finrank_codeSpace_eq_two_pow (S : StabGroup m) :
    Module.finrank ℂ (codeSpace S) = 2 ^ S.numLogical := by
  rw [finrank_codeSpace, numLogical]
  obtain ⟨k, hk⟩ := card_carrier_eq_two_pow S
  rw [hk]
  -- Use that 2^k divides 2^m to get k ≤ m
  have hdvd : 2 ^ k ∣ 2 ^ m := by rw [← hk]; exact card_carrier_dvd S
  have hkm : k ≤ m :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_dvd (Nat.two_pow_pos m) hdvd)
  rw [Nat.log_pow (by decide : 1 < 2)]
  exact Nat.div_eq_of_eq_mul_left (Nat.two_pow_pos k) (by rw [← pow_add, Nat.sub_add_cancel hkm])

/-- The logical dimension is at most the physical one. -/
theorem numLogical_le_numPhysical (S : StabGroup m) : S.numLogical ≤ S.numPhysical := by
  simp [numLogical, numPhysical]

end StabGroup
end PauliOp
end QuantumLib
