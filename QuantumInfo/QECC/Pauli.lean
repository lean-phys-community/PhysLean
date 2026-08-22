import QuantumInfo.QECC.Stabilizer

/-!
# The n-qubit Pauli group (faithful model)

`PauliOp n` is `iᵏ XˣZᶻ`; it forms a group and represents faithfully as unitary matrices via
`pauliOp` (reusing `pauliOp_mul`). A stabilizer is then an honest `-I`-free abelian subgroup.
-/

open scoped BigOperators
namespace QuantumLib
variable {n : ℕ}

/-- An element of the `n`-qubit Pauli group: `iᵏ XˣZᶻ`. -/
@[ext]
structure PauliOp (n : ℕ) where
  phase : ZMod 4
  x : Fin n → ZMod 2
  z : Fin n → ZMod 2

namespace PauliOp

/-- The GF(2) symplectic pairing `β(P,Q) = ∑ z_P · x_Q` governing the Pauli cocycle. -/
def betaPair (P Q : PauliOp n) : ZMod 2 := ∑ i, P.z i * Q.x i

/-- The additive map `ZMod 2 → ZMod 4`, `s ↦ 2·s`, lifting a sign into a `ZMod 4` phase. -/
def tau (s : ZMod 2) : ZMod 4 := 2 * (s.val : ZMod 4)

theorem tau_add (s t : ZMod 2) : tau (s + t) = tau s + tau t := by
  fin_cases s <;> fin_cases t <;> decide

instance : One (PauliOp n) := ⟨⟨0, 0, 0⟩⟩
instance : Mul (PauliOp n) :=
  ⟨fun P Q => ⟨P.phase + Q.phase + tau (betaPair P Q), P.x + Q.x, P.z + Q.z⟩⟩
instance : Inv (PauliOp n) :=
  ⟨fun P => ⟨-P.phase - tau (betaPair P P), P.x, P.z⟩⟩

@[simp] theorem one_phase : (1 : PauliOp n).phase = 0 := rfl
@[simp] theorem one_x : (1 : PauliOp n).x = 0 := rfl
@[simp] theorem one_z : (1 : PauliOp n).z = 0 := rfl
@[simp] theorem mul_phase (P Q : PauliOp n) :
    (P * Q).phase = P.phase + Q.phase + tau (betaPair P Q) := rfl
@[simp] theorem mul_x (P Q : PauliOp n) : (P * Q).x = P.x + Q.x := rfl
@[simp] theorem mul_z (P Q : PauliOp n) : (P * Q).z = P.z + Q.z := rfl

@[simp] theorem tau_zero : tau (0 : ZMod 2) = 0 := by decide

@[simp] theorem betaPair_one_left (P : PauliOp n) : betaPair 1 P = 0 := by simp [betaPair]

@[simp] theorem betaPair_one_right (P : PauliOp n) : betaPair P 1 = 0 := by simp [betaPair]

theorem betaPair_mul_left (P Q R : PauliOp n) :
    betaPair (P * Q) R = betaPair P R + betaPair Q R := by
  simp only [betaPair, mul_z, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring

theorem betaPair_mul_right (P Q R : PauliOp n) :
    betaPair P (Q * R) = betaPair P Q + betaPair P R := by
  simp only [betaPair, mul_x, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring

/-- The Pauli cocycle sign as a collapsed product: `∏ (-1)^(z_P·x_Q) = (-1)^β(P,Q)`. -/
theorem prod_negOnePow_betaPair (P Q : PauliOp n) :
    ∏ i, (-1 : ℂ) ^ (P.z i * Q.x i).val = (-1) ^ (betaPair P Q).val :=
  negOnePow_sum _ _

instance : Group (PauliOp n) where
  mul_assoc a b c := by
    refine PauliOp.ext ?_ (add_assoc a.x b.x c.x) (add_assoc a.z b.z c.z)
    simp only [mul_phase, betaPair_mul_left, betaPair_mul_right, tau_add]; ring
  one_mul a := PauliOp.ext (by simp [mul_phase]) (zero_add a.x) (zero_add a.z)
  mul_one a := PauliOp.ext (by simp [mul_phase]) (add_zero a.x) (add_zero a.z)
  inv_mul_cancel a := by
    apply PauliOp.ext
    · show -a.phase - tau (betaPair a a) + a.phase + tau (betaPair ⟨_, a.x, a.z⟩ a) = 0
      rw [show betaPair (⟨-a.phase - tau (betaPair a a), a.x, a.z⟩ : PauliOp n) a
        = betaPair a a from rfl]
      ring
    · show a.x + a.x = (0 : Fin n → ZMod 2); ext i; simp [CharTwo.add_self_eq_zero]
    · show a.z + a.z = (0 : Fin n → ZMod 2); ext i; simp [CharTwo.add_self_eq_zero]

/-! ### The faithful matrix representation -/

/-- The unitary matrix of a Pauli group element: `iᵏ • XˣZᶻ`. -/
noncomputable def toMat (P : PauliOp n) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  Complex.I ^ P.phase.val • pauliOp (P.x, P.z)

/-- `iᵏ` phases compose additively mod 4 (as `i⁴ = 1`). -/
private theorem I_pow_zmod4_add (a b : ZMod 4) :
    Complex.I ^ (a + b).val = Complex.I ^ a.val * Complex.I ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  generalize a.val + b.val = m
  conv_rhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul,
    show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq, neg_one_sq],
    one_pow, one_mul]

/-- The `τ`-phase realizes the `(-1)` sign of the Pauli cocycle. -/
private theorem I_pow_tau (s : ZMod 2) : Complex.I ^ (tau s).val = (-1) ^ s.val := by
  have h : (tau s).val = 2 * s.val := by fin_cases s <;> decide
  rw [h, pow_mul, Complex.I_sq]

@[simp] theorem toMat_one : toMat (1 : PauliOp n) = 1 := by
  simp only [toMat, one_phase, one_x, one_z, ZMod.val_zero, pow_zero, one_smul]
  exact pauliOp_zero

theorem toMat_mul (P Q : PauliOp n) : toMat (P * Q) = toMat P * toMat Q := by
  simp only [toMat, mul_phase, mul_x, mul_z]
  rw [smul_mul_smul, pauliOp_mul, smul_smul]
  congr 1
  -- scalar: iᵏ phases compose additively; the `(-1)` cocycle sign is realized by `τ`.
  rw [show (∏ i, (-1 : ℂ) ^ (((P.x, P.z) : PauliSpace n).2 i * ((Q.x, Q.z) : PauliSpace n).1 i).val)
        = (-1 : ℂ) ^ (betaPair P Q).val from negOnePow_sum _ _,
    I_pow_zmod4_add, I_pow_zmod4_add, I_pow_tau, mul_assoc]

/-- The faithful representation of the Pauli group as a monoid homomorphism into matrices. -/
noncomputable def toMatHom : PauliOp n →* Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ where
  toFun := toMat
  map_one' := toMat_one
  map_mul' := toMat_mul

end PauliOp
end QuantumLib
