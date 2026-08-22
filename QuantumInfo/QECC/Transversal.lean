/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.QECC.StabilizerFacts
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Transversal gates and the Eastin–Knill theorem

A **transversal** unitary is a tensor product of single-qubit unitaries. Such gates are the
"cheap" fault-tolerant operations. The **Eastin–Knill theorem** says no nontrivial code admits a
*universal* set of transversal logical gates. Stated here for the ATP.
-/

open scoped BigOperators
namespace QuantumLib
namespace PauliOp
variable {n : ℕ}

/-- A unitary is **transversal** if it factors as a tensor product `⨂ᵢ uᵢ` of single-qubit
unitaries, i.e. its matrix entries are products of single-qubit entries. -/
def IsTransversal (U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) : Prop :=
  ∃ u : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ,
    (∀ i, u i ∈ Matrix.unitaryGroup (ZMod 2) ℂ) ∧
    ∀ f g, U f g = ∏ i, u i (f i) (g i)

/-- The identity is transversal. -/
theorem isTransversal_one : IsTransversal (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) := by
  use fun _ => 1
  constructor
  · intro i
    simp
  · intro f g
    by_cases hfg : f = g
    · simp [hfg, Matrix.one_apply]
    · rw [Matrix.one_apply, if_neg hfg]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hfg
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [hi]

/-- Transversal unitaries are closed under multiplication. -/
theorem IsTransversal.mul {U V : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hU : IsTransversal U) (hV : IsTransversal V) : IsTransversal (U * V) := by
  obtain ⟨u₁, hu₁_unit, hu₁⟩ := hU
  obtain ⟨u₂, hu₂_unit, hu₂⟩ := hV
  use fun i => u₁ i * u₂ i
  constructor
  · intro i
    exact MulMemClass.mul_mem (hu₁_unit i) (hu₂_unit i)
  · intro f g
    rw [Matrix.mul_apply]
    have h1 : ∀ j : Fin n → ZMod 2, U f j * V j g = ∏ i, (u₁ i (f i) (j i) * u₂ i (j i) (g i)) := by
      intro j
      rw [hu₁ f j, hu₂ j g]
      simp [Finset.prod_mul_distrib]
    simp_rw [h1]
    simp only [Matrix.mul_apply]
    rw [Fintype.prod_sum]

/-- A transversal unitary is unitary. -/
theorem IsTransversal.mem_unitaryGroup {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hU : IsTransversal U) : U ∈ Matrix.unitaryGroup (Fin n → ZMod 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  -- U * star U = 1
  obtain ⟨u, hu_unitary, hu_prod⟩ := hU
  ext f g
  simp only [Matrix.mul_apply, Matrix.star_apply]
  -- Goal: ∑ x, U f x * conj(U g x) = (1 : Matrix ...) f g
  rw [Matrix.one_apply]
  simp_rw [hu_prod]
  -- Rewrite star of product
  simp_rw [star_prod]
  -- Combine products
  have combine_prod : ∀ x : Fin n → ZMod 2,
      (∏ i, u i (f i) (x i)) * ∏ i, star (u i (g i) (x i)) = ∏ i, (u i (f i) (x i) * star (u i (g i) (x i))) := by
    simp [Finset.prod_mul_distrib]
  simp_rw [combine_prod]
  show ∑ x : (Fin n → ZMod 2), ∏ i : Fin n, u i (f i) (x i) * star (u i (g i) (x i)) = _
  let f' : (i : Fin n) → ZMod 2 → ℂ := fun i j => u i (f i) j * star (u i (g i) j)
  show ∑ x : (Fin n → ZMod 2), ∏ i : Fin n, f' i (x i) = _
  rw [← Fintype.prod_sum]
  -- Each factor is a Kronecker delta because u i is unitary
  have unitary_row_orthogonal : ∀ i : Fin n, ∀ x y : ZMod 2, ∑ j, u i x j * star (u i y j) = if x = y then 1 else 0 := by
    intro i x y
    have hui := hu_unitary i
    rw [Matrix.mem_unitaryGroup_iff] at hui
    exact congr_fun (congr_fun hui x) y
  have : ∀ i : Fin n, ∑ j, f' i j = if f i = g i then 1 else 0 := by
    intro i
    show ∑ j, u i (f i) j * star (u i (g i) j) = _
    exact unitary_row_orthogonal i (f i) (g i)
  simp_rw [this]
  -- The product is 1 iff for all i, f i = g i, i.e., f = g
  by_cases hfg : f = g
  · simp [hfg]
  · rw [if_neg hfg]
    -- f ≠ g means there exists i with f i ≠ g i
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ g i := Function.ne_iff.mp hfg
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    simp [hi]

/-- A single-qubit Pauli, tensored across qubits, is transversal. -/
theorem isTransversal_toMat_of_weight_le_one [NeZero n] {P : PauliOp n} (hP : weight P ≤ 1) :
    IsTransversal (toMat P) := by
  -- Weight ≤ 1 means either P is a scalar (weight 0) or P acts on exactly one qubit (weight 1)
  by_cases h0 : P.x = 0 ∧ P.z = 0
  · -- Weight 0 case: P is a scalar multiple of identity
    -- P = ⟨P.phase, 0, 0⟩, so toMat P = Complex.I ^ P.phase.val • 1
    have hP_eq : P = ⟨P.phase, 0, 0⟩ := by
      ext <;> simp [h0]
    rw [hP_eq, StabGroup.toMat_phase]
    -- A scalar multiple of identity: use u i = c^(1/n) • 1 for each i
    let c := Complex.I ^ P.phase.val
    let d := c ^ (1 / (n : ℂ))
    use fun _ => d • 1
    constructor
    · intro i
      simp [Matrix.mem_unitaryGroup_iff]
      -- Need: star d * d = 1, where d = c^(1/n) and |c| = 1
      have hc : (starRingEnd ℂ) c * c = 1 := by
        simp [c]
        have : P.phase.val < 4 := ZMod.val_lt P.phase
        interval_cases P.phase.val <;> norm_num [Complex.I_sq, pow_succ]
      -- Now show star d * d = 1 for d = c^(1/n)
      -- Simplify: star d • d • 1 = (star d * d) • 1
      simp [smul_smul]
      have hd : (starRingEnd ℂ) d * d = 1 := by
        have h1 : (starRingEnd ℂ) d * d = Complex.normSq d := by
          simp [Complex.normSq_eq_conj_mul_self]
        rw [h1, Complex.normSq_eq_norm_sq]
        suffices ‖d‖ = 1 by rw [this]; norm_num
        -- We have c * conj c = 1, so ‖c‖ = 1
        have hc_norm : ‖c‖ = 1 := by
          have h1 : (starRingEnd ℂ) c = star c := by simp
          have : ‖c‖^2 = 1 := by
            rw [sq]
            calc ‖c‖ * ‖c‖ = ‖c‖ * ‖star c‖ := by rw [norm_star]
              _ = ‖c * star c‖ := by rw [norm_mul]
              _ = ‖(starRingEnd ℂ) c * c‖ := by rw [h1, mul_comm]
              _ = ‖(1 : ℂ)‖ := by rw [hc]
              _ = 1 := by norm_num
          nlinarith [sq_nonneg ‖c‖, norm_nonneg c]
        -- d = c^(1/n), so ‖d‖ = ‖c‖^(1/n) = 1
        have hc_ne : c ≠ 0 := by
          intro hc0
          rw [hc0] at hc
          simp at hc
        -- d = c^(1/n) where 1/n is real, so ‖d‖ = ‖c‖^(1/n)
        have exp_eq : (1 / (n : ℂ)) = ((1 / (n : ℝ)) : ℝ) := by simp
        show ‖c ^ (1 / (n : ℂ))‖ = 1
        rw [exp_eq, Complex.norm_cpow_real]
        rw [hc_norm]
        norm_num
      simp [hd]
    · intro f g
      simp only [Matrix.smul_apply, Matrix.one_apply]
      by_cases hfg : f = g
      · simp [hfg]
        -- Need: c = d^n
        -- d = c^(1/n), so d^n = c^(1/n * n) = c
        rw [← Complex.cpow_nat_mul c n (1 / (n : ℂ))]
        have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
        rw [mul_div_cancel₀ _ hn, Complex.cpow_one]
      · -- f ≠ g means there exists i with f i ≠ g i
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hfg
        have : (d • (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) (f i) (g i) = 0 := by simp [hi]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) this]
        simp [hfg]
  · -- Weight 1 case: P acts on exactly one qubit
    -- Since ¬(P.x = 0 ∧ P.z = 0), P has weight exactly 1
    -- We'll use u on the support of P, identity elsewhere
    -- First, establish that weight P = 1
    have hweight : weight P = 1 := by
      have h0 : weight P ≠ 0 := by
        simp [weight_eq_zero_iff, h0]
      have hle : weight P ≤ 1 := hP
      omega
    -- There exists a unique qubit j where P acts
    rw [weight_eq_card_support] at hweight
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hweight
    -- P.x and P.z are zero except at j
    have hx_zero : ∀ i ≠ j, P.x i = 0 := by
      intro i hi
      have : i ∉ Finset.univ.filter (fun i => P.x i ≠ 0 ∨ P.z i ≠ 0) := by
        rw [hj]
        simp [hi]
      simp [Finset.mem_filter] at this
      tauto
    have hz_zero : ∀ i ≠ j, P.z i = 0 := by
      intro i hi
      have : i ∉ Finset.univ.filter (fun i => P.x i ≠ 0 ∨ P.z i ≠ 0) := by
        rw [hj]
        simp [hi]
      simp [Finset.mem_filter] at this
      tauto
    -- At j, either P.x j ≠ 0 or P.z j ≠ 0
    have hj_mem : j ∈ Finset.univ.filter (fun i => P.x i ≠ 0 ∨ P.z i ≠ 0) := by rw [hj]; simp
    simp [Finset.mem_filter] at hj_mem
    -- Define the scalar d = c (the full phase is at position j)
    let c := Complex.I ^ P.phase.val
    let d := c
    -- Define u: at j use d • single-qubit Pauli, elsewhere use 1
    let p : PauliSpace 1 := ((fun _ : Fin 1 => P.x j), (fun _ : Fin 1 => P.z j))
    -- Convert pauliOp on Fin 1 → ZMod 2 to matrix on ZMod 2 via equivalence
    let equiv : (Fin 1 → ZMod 2) ≃ ZMod 2 := Equiv.funUnique (Fin 1) (ZMod 2)
    let upauli : Matrix (ZMod 2) (ZMod 2) ℂ := Matrix.reindex equiv equiv (pauliOp p)
    use fun i => if i = j then d • upauli else 1
    constructor
    · intro i
      by_cases hij : i = j
      · subst hij
        simp [Matrix.mem_unitaryGroup_iff]
        have hpauli_u := pauliOp_mem_unitaryGroup p
        -- upauli is also unitary since reindex preserves unitarity
        have hupauli_u : upauli ∈ Matrix.unitaryGroup (ZMod 2) ℂ := by
          simp only [upauli]
          -- reindexing preserves unitarity
          have hpauli_u := pauliOp_mem_unitaryGroup p
          rw [Matrix.mem_unitaryGroup_iff] at hpauli_u ⊢
          -- hpauli_u : pauliOp p * star (pauliOp p) = 1
          -- Convert to conjTranspose form
          simp_rw [Matrix.star_eq_conjTranspose] at hpauli_u ⊢
          -- A * Aᴴ = 1 => reindex(A) * reindex(Aᴴ) = 1
          have h_equiv : ((Matrix.reindex equiv equiv) (pauliOp p)).conjTranspose =
                         (Matrix.reindex equiv equiv) (pauliOp p).conjTranspose :=
            Matrix.conjTranspose_reindex equiv equiv _
          have reindex_mul : (Matrix.reindex equiv equiv) (pauliOp p) *
               (Matrix.reindex equiv equiv) ((pauliOp p).conjTranspose) =
               (Matrix.reindex equiv equiv) ((pauliOp p) * (pauliOp p).conjTranspose) := by
            ext a b
            simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
            rw [← Fintype.sum_equiv equiv.symm]
            intro x
            rfl
          calc (Matrix.reindex equiv equiv) (pauliOp p) *
               (Matrix.reindex equiv equiv) (pauliOp p).conjTranspose
             = (Matrix.reindex equiv equiv) (pauliOp p) *
               ((Matrix.reindex equiv equiv) (pauliOp p)).conjTranspose := by rw [h_equiv]
           _ = (Matrix.reindex equiv equiv) ((pauliOp p) * (pauliOp p).conjTranspose) := reindex_mul
           _ = (Matrix.reindex equiv equiv) 1 := by rw [hpauli_u]
           _ = 1 := by simp
        -- Need: (star d) * d = 1 (since |d| = 1)
        rw [Matrix.mem_unitaryGroup_iff] at hupauli_u
        rw [hupauli_u]
        simp [smul_smul]
        have hd : (starRingEnd ℂ) d * d = 1 := by
          -- We have c * conj c = 1, so ‖c‖ = 1
          have hc : (starRingEnd ℂ) c * c = 1 := by
            simp [c]
            have : P.phase.val < 4 := ZMod.val_lt P.phase
            interval_cases P.phase.val <;> norm_num [Complex.I_sq, pow_succ]
          have h1 : (starRingEnd ℂ) d * d = Complex.normSq d := by
            simp [Complex.normSq_eq_conj_mul_self]
          rw [h1, Complex.normSq_eq_norm_sq]
          suffices ‖d‖ = 1 by rw [this]; norm_num
          -- d = c, so ‖d‖ = ‖c‖ = 1
          have hc_norm : ‖c‖ = 1 := by
            have h1 : (starRingEnd ℂ) c = star c := by simp
            have : ‖c‖^2 = 1 := by
              rw [sq]
              calc ‖c‖ * ‖c‖ = ‖c‖ * ‖star c‖ := by rw [norm_star]
                _ = ‖c * star c‖ := by rw [norm_mul]
                _ = ‖(starRingEnd ℂ) c * c‖ := by rw [h1, mul_comm]
                _ = ‖(1 : ℂ)‖ := by rw [hc]
                _ = 1 := by norm_num
            nlinarith [sq_nonneg ‖c‖, norm_nonneg c]
          rw [hc_norm]
        simp [hd]
      · simp [hij]
    · intro f g
      -- The RHS simplifies: for i ≠ j we get (1 : Matrix _ _ _) (f i) (g i) = if f i = g i then 1 else 0
      -- For i = j we get d • upauli (f j) (g j) = d * upauli (f j) (g j)
      have rhs_eq : ∏ i, (if i = j then d • upauli else 1) (f i) (g i) =
          (if ∀ i ≠ j, f i = g i then d * upauli (f j) (g j) else 0) := by
        by_cases hall : ∀ i ≠ j, f i = g i
        · -- All f i = g i for i ≠ j
          have h1 : (if ∀ i ≠ j, f i = g i then d * upauli (f j) (g j) else 0) = d * upauli (f j) (g j) := by
            simp only [if_pos hall]
          rw [h1]
          -- For i ≠ j, f i = g i, so (1 : Matrix ..) (f i) (g i) = 1
          -- For i = j, we get (d • upauli) (f j) (g j) = d * upauli (f j) (g j)
          have heq : ∀ i, (if i = j then d • upauli else 1) (f i) (g i) =
            if i = j then d * upauli (f j) (g j) else 1 := by
            intro i
            by_cases hij : i = j
            · simp [hij]
            · simp [hij, Matrix.one_apply, hall i hij]
          simp_rw [heq]
          simp [Finset.prod_ite_eq']
        · -- There exists i ≠ j with f i ≠ g i
          have h2 : (if ∀ i ≠ j, f i = g i then d * upauli (f j) (g j) else 0) = 0 := by
            simp [hall]
          rw [h2]
          push_neg at hall
          obtain ⟨i, hi_nej, hi_fne⟩ := hall
          rw [Finset.prod_eq_zero (Finset.mem_univ i)]
          rw [if_neg hi_nej, Matrix.one_apply]
          simp [hi_fne]
      rw [rhs_eq]
      -- Now we need to show: (if ∀ i ≠ j, f i = g i then d * upauli (f j) (g j) else 0) = toMat P f g
      -- toMat P = c • pauliOp (P.x, P.z), and upauli is the single-qubit pauliOp at j
      -- We need to relate pauliOp (P.x, P.z) f g to upauli (f j) (g j)
      by_cases hall : ∀ i ≠ j, f i = g i
      · -- All f i = g i for i ≠ j
        rw [if_pos hall]
        -- Need: c • pauliOp (P.x, P.z) f g = d * upauli (f j) (g j)
        -- Since d = c, we need: pauliOp (P.x, P.z) f g = upauli (f j) (g j)
        have hc : d = c := rfl
        rw [hc]
        -- Simplify both sides
        show c * (pauliOp (P.x, P.z) f g) = c * upauli (f j) (g j)
        congr 1
        -- Now show pauliOp (P.x, P.z) f g = upauli (f j) (g j)
        -- Both reduce to: if f j = g j + P.x j then (-1)^(P.z j * g j).val else 0
        simp only [pauliOp, Matrix.of_apply]
        -- Key: f = g + P.x iff f j = g j + P.x j (since f i = g i and P.x i = 0 for i ≠ j)
        have hfeq : f = g + P.x ↔ f j = g j + P.x j := by
          constructor
          · intro heq
            exact congr_fun heq j
          · intro hj
            ext i
            by_cases hij : i = j
            · subst hij; simp [hj]
            · rw [Pi.add_apply, hx_zero i hij, add_zero]
              exact hall i hij
        simp only [hfeq]
        -- Also simplify the product: all terms except i = j are 1
        have hprod : ∏ i : Fin n, (-1 : ℂ) ^ (P.z i * g i).val = (-1 : ℂ) ^ (P.z j * g j).val := by
          apply Finset.prod_eq_single j
          · intro i _ hi_nej
            rw [hz_zero i hi_nej, zero_mul, ZMod.val_zero, pow_zero]
          · intro hx
            exact absurd (Finset.mem_univ j) hx
        rw [hprod]
        -- Now simplify upauli (f j) (g j)
        simp only [upauli, Matrix.reindex_apply, pauliOp]
        -- Simplify equiv.symm
        have hem : ∀ a : ZMod 2, equiv.symm a = fun _ : Fin 1 => a := fun a => rfl
        simp [hem]
        -- Show the conditions and values match
        have hcond : (fun _ : Fin 1 => f j) = (fun _ : Fin 1 => g j) + p.1 ↔ f j = (g + P.x) j := by
          simp only [show p.1 = fun _ => P.x j from rfl, Pi.add_apply]
          exact ⟨fun h => by simpa using congr_fun h 0, fun h => funext fun _ => h⟩
        have hpz : p.2 0 = P.z j := rfl
        simp [hcond, hpz]
      · -- There exists i ≠ j with f i ≠ g i
        rw [if_neg hall]
        -- P.toMat = c • pauliOp (P.x, P.z), and pauliOp returns 0 when f ≠ g + P.x
        simp [toMat, Matrix.smul_apply]
        -- Need to show pauliOp (P.x, P.z) f g = 0, which happens when f ≠ g + P.x
        simp [pauliOp, Matrix.of_apply]
        -- Need: ¬(f = g + P.x)
        have hne : ¬(f = g + P.x) := by
          push_neg at hall
          obtain ⟨i, hi_nej, hi_fne⟩ := hall
          intro heq
          have := congr_fun heq i
          rw [Pi.add_apply] at this
          rw [hx_zero i hi_nej] at this
          simp at this
          exact hi_fne this
        simp [hne]

namespace StabGroup
variable (S : StabGroup n)

/-- `U` **implements** the logical unitary `V` if there is an encoding isometry `W` onto the code
space intertwining them: `star W * W = 1`, `Π·W = W`, and `U·W = W·V`. -/
def ImplementsLogical (U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) : Prop :=
  ∃ W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ,
    W.conjTranspose * W = 1 ∧ stabProj S * W = W ∧ U * W = W * V

/-- A transversal gate that preserves the code space implements *some* logical unitary. -/
theorem exists_logical_of_transversal_preserving
    {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hU : IsTransversal U) (hpres : stabProj S * U * stabProj S = U * stabProj S) :
    ∃ V, S.ImplementsLogical U V := by sorry

/-- The set of logical unitaries implementable by *some* transversal gate. -/
def transversalLogicals :
    Set (Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) :=
  {V | ∃ U, IsTransversal U ∧ S.ImplementsLogical U V}

/-- **Eastin–Knill reduction step (fully proved).** If only finitely many logical unitaries are
transversally implementable, then transversal gates cannot be universal — because the logical
unitary group is infinite, so it cannot be contained in a finite set. This is the clean logical
core of the theorem; the hard remaining input is the *finiteness* of `transversalLogicals`. -/
theorem not_universal_of_transversalLogicals_finite
    (hfin : S.transversalLogicals.Finite)
    (hinf : {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ |
        V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ}.Infinite) :
    ¬ ∀ V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ,
        ∃ U, IsTransversal U ∧ S.ImplementsLogical U V := by
  intro hall
  exact hinf (hfin.subset (fun V hV => hall V hV))

open scoped Matrix.Norms.L2Operator

/-- **General topology:** a set sitting inside a compact set whose distinct points are uniformly
`ε`-separated is finite. -/
theorem finite_of_separated {X : Type*} [PseudoMetricSpace X] {K G : Set X}
    (hK : IsCompact K) (hGK : G ⊆ K) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ x ∈ G, ∀ y ∈ G, x ≠ y → ε ≤ dist x y) : G.Finite := by
  -- Use ε/3-balls to cover K (so two points in same ball have dist < ε)
  let ε' : NNReal := ⟨ε / 3, by linarith⟩
  have hε' : ε' ≠ 0 := by
    have hpos : (0 : ℝ) < (ε' : ℝ) := by show (0 : ℝ) < ε / 3; linarith
    exact_mod_cast hpos.ne'
  obtain ⟨N, hNád, hNfin, hNcover⟩ := Metric.exists_finite_isCover_of_isCompact hε' hK
  -- Each point of G is covered by some ball centered at a point of N
  -- Metric.IsCover ε' K N means ∀ x ∈ K, ∃ y ∈ N, edist x y ≤ ε'
  have hNcover_G : ∀ g ∈ G, ∃ n ∈ N, edist g n ≤ ε' := fun g hg => hNcover (hGK hg)
  -- Define a choice function from G to N
  choose f hf using hNcover_G
  -- Show that f is injective on G
  have hf_inj : ∀ g₁ (hg₁ : g₁ ∈ G), ∀ g₂ (hg₂ : g₂ ∈ G), f g₁ hg₁ = f g₂ hg₂ → g₁ = g₂ := by
    intro g₁ hg₁ g₂ hg₂ hfg
    by_contra hne
    have hf1 : edist g₁ (f g₁ hg₁) ≤ ε' := (hf g₁ hg₁).2
    have hf2 : edist g₂ (f g₂ hg₂) ≤ ε' := (hf g₂ hg₂).2
    have hf2' : edist g₂ (f g₁ hg₁) ≤ ε' := by rwa [← hfg] at hf2
    have hdist : edist g₁ g₂ ≤ ↑ε' + ↑ε' := by
      calc edist g₁ g₂ ≤ edist g₁ (f g₁ hg₁) + edist (f g₁ hg₁) g₂ := edist_triangle _ _ _
        _ = edist g₁ (f g₁ hg₁) + edist g₂ (f g₁ hg₁) := by rw [edist_comm (f g₁ hg₁) g₂]
        _ ≤ ↑ε' + ↑ε' := add_le_add hf1 hf2'
    -- But dist g₁ g₂ ≥ ε by separation, and dist ≤ edist, and ε' + ε' = ε
    have hsep' : dist g₁ g₂ ≥ ε := hsep g₁ hg₁ g₂ hg₂ hne
    have hle : ENNReal.ofReal (dist g₁ g₂) = edist g₁ g₂ := (edist_dist g₁ g₂).symm
    have hcoerce : ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) = ENNReal.ofReal (2 * ε / 3) := by
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ ε / 3) (by linarith : 0 ≤ ε / 3)]
      congr 1
      ring
    have hε'_eq : ↑ε' = ENNReal.ofReal (ε / 3) := by
      exact ENNReal.coe_nnreal_eq ε'
    have hdist' : edist g₁ g₂ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
      simpa only [hε'_eq] using hdist
    have hfinal : edist g₁ g₂ ≤ ENNReal.ofReal (2 * ε / 3) := le_trans hdist' hcoerce.le
    have hdist_le : dist g₁ g₂ ≤ 2 * ε / 3 := by
      have h : ENNReal.ofReal (dist g₁ g₂) ≤ ENNReal.ofReal (2 * ε / 3) := hle.le.trans hfinal
      rw [ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ 2 * ε / 3)] at h
      exact h
    linarith [hsep', hdist_le, hε]
  -- G injects into N, so G is finite since N is finite
  set I : G → N := fun g => ⟨f g g.2, (hf g g.2).1⟩ with hI_def
  have hI_inj : Function.Injective I := by
    intro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ hIeq
    have : f g₁ hg₁ = f g₂ hg₂ := Subtype.ext_iff.mp hIeq
    have heq : g₁ = g₂ := hf_inj g₁ hg₁ g₂ hg₂ this
    exact Subtype.ext heq
  haveI : Finite N := Set.Finite.to_subtype hNfin
  have : Finite G := Finite.of_injective I hI_inj
  exact Set.finite_coe_iff.mpr this

/-- The unitary group of the logical space is compact. -/
theorem unitaryGroup_isCompact :
    IsCompact {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ |
      V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h : {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ |
        V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ} = {V | V * star V = 1} := by
      ext V
      simp only [Set.mem_setOf_eq]
      exact Matrix.mem_unitaryGroup_iff
    rw [h]
    set m := Fin S.numLogical → ZMod 2 with hm
    have : {V : Matrix m m ℂ | V * star V = 1} = (fun V : Matrix m m ℂ => V * star V) ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage (by fun_prop)
  · set m := Fin S.numLogical → ZMod 2 with hm
    -- Entries of unitary matrices are bounded by 1
    have hc : Bornology.IsBounded (Metric.closedBall (0 : Matrix m m ℂ) 1) := Metric.isBounded_closedBall
    exact hc.subset (fun V hV => by
      rw [Metric.mem_closedBall, dist_zero_right]
      -- Use that unitary matrices have norm exactly 1 in a C* algebra
      have hV_unitary : V ∈ unitary (Matrix m m ℂ) := by
        rw [Unitary.mem_iff]
        exact ⟨Matrix.mem_unitaryGroup_iff'.mp hV, Matrix.mem_unitaryGroup_iff.mp hV⟩
      exact (CStarRing.norm_of_mem_unitary hV_unitary).le)

/-- Every transversally-implemented logical unitary is unitary (so lands in the compact group). -/
theorem transversalLogicals_subset_unitary :
    S.transversalLogicals ⊆
      {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ |
        V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ} := by
  intro V hV
  obtain ⟨U, hU_trans, W, hW_unit, _, hUV⟩ := hV
  simp only [Set.mem_setOf_eq]
  rw [Matrix.mem_unitaryGroup_iff']
  have hun : U.conjTranspose * U = 1 := by
    have hu := IsTransversal.mem_unitaryGroup hU_trans
    exact Matrix.UnitaryGroup.star_mul_self ⟨U, hu⟩
  have eq1 : V.conjTranspose * W.conjTranspose = W.conjTranspose * U.conjTranspose := by
    have : (W * V).conjTranspose = (U * W).conjTranspose := by rw [hUV]
    simp only [Matrix.conjTranspose_mul] at this
    exact this
  have hstar : star V = W.conjTranspose * U.conjTranspose * W := by
    simp only [Matrix.star_eq_conjTranspose]
    calc V.conjTranspose = V.conjTranspose * 1 := by rw [mul_one]
      _ = V.conjTranspose * (W.conjTranspose * W) := by rw [hW_unit]
      _ = (V.conjTranspose * W.conjTranspose) * W := by exact (Matrix.mul_assoc V.conjTranspose W.conjTranspose W).symm
      _ = W.conjTranspose * U.conjTranspose * W := by rw [eq1]
  have haux : star V * V = W.conjTranspose * W := by
    rw [hstar]
    have h1 : W.conjTranspose * U.conjTranspose * W * V =
              W.conjTranspose * U.conjTranspose * (W * V) := by exact Matrix.mul_assoc _ _ _
    rw [h1, ← hUV]
    have h2 : W.conjTranspose * U.conjTranspose * (U * W) = W.conjTranspose * (U.conjTranspose * U) * W := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [h2, hun]
    simp
  rw [haux, hW_unit]

/-- **Heart of Eastin–Knill (no Lie derivatives).** A transversal, code-preserving gate whose
logical action `V` is within `1` of the identity implements only a global phase.

Route: `V` near `1` ⟹ `V = exp (i • H)` (matrix `log`); the transversal factors act on distinct
qubits, so commute, giving `U = exp (i • ∑ᵢ H̃ᵢ)` with each `H̃ᵢ` of weight `≤ 1` (`Matrix.exp_add_of_commute`);
code-preservation ⟹ `H` commutes with `Π`; `compress_scalar_of_weight_lt` ⟹ `Π H Π = λ Π`; hence
`H` acts on the code as `λ • 1` and `V = exp (i·λ) • 1`. -/
theorem transversal_logical_near_one_isPhase (hd : 2 ≤ S.distance)
    {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ} (hU : IsTransversal U)
    (hpres : stabProj S * U * stabProj S = U * stabProj S)
    {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hV : S.ImplementsLogical U V) (hclose : ‖V - 1‖ < 1) :
    ∃ c : ℂ, V = c • 1 := by
  sorry

/-- **Discreteness up to phase.** There is a uniform `ε > 0` such that any two *non-proportional*
transversal logicals are at least `ε` apart. (If two were closer, their group difference would be a
code-preserving transversal gate within `1` of the identity, hence a phase by
`transversal_logical_near_one_isPhase`, making them proportional.) -/
theorem transversalLogicals_separated (hd : 2 ≤ S.distance) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ V ∈ S.transversalLogicals, ∀ V' ∈ S.transversalLogicals,
      (∀ c : ℂ, V ≠ c • V') → ε ≤ ‖V - V'‖ := by
  sorry

/-- The transversal logical gates are finite *up to global phase* — the sharp form of Eastin–Knill.
Proof (no Lie derivatives): the transversal logicals are discrete up to phase
(`transversalLogicals_separated`) and live in the compact unitary group, so any pairwise
non-proportional family is `ε`-separated inside a compact set, hence finite. -/
theorem transversal_logical_finite (hd : 2 ≤ S.distance)
    (T : Set (Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ))
    (hT : T ⊆ S.transversalLogicals)
    (hpair : ∀ V ∈ T, ∀ V' ∈ T, V ≠ V' → ∀ c : ℂ, V ≠ c • V') :
    T.Finite := by
  obtain ⟨ε, hε, hsep⟩ := S.transversalLogicals_separated hd
  refine finite_of_separated S.unitaryGroup_isCompact
    (fun V hV => S.transversalLogicals_subset_unitary (hT hV)) hε ?_
  intro V hV V' hV' hne
  rw [dist_eq_norm]
  exact hsep V (hT hV) V' (hT hV') (hpair V hV V' hV' hne)

/-- The logical unitary group (dimension `2^k ≥ 2` when `k ≥ 1`) contains an infinite family of
*pairwise non-proportional* unitaries — e.g. the diagonals `diag(1,…,e^{iθ},…,1)`, which agree at
one basis vector and differ at another, so no scalar relates two of them. -/
theorem exists_infinite_nonproportional_unitary (hk : 1 ≤ S.numLogical) :
    ∃ T : Set (Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ),
      (∀ V ∈ T, V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ) ∧
      (∀ V ∈ T, ∀ V' ∈ T, V ≠ V' → ∀ c : ℂ, V ≠ c • V') ∧ T.Infinite := by
  classical
  -- The index type is nontrivial (dimension `2^k ≥ 2`).
  have hnt : Nontrivial (Fin S.numLogical → ZMod 2) := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    have hc : Fintype.card (Fin S.numLogical → ZMod 2) = 2 ^ S.numLogical := by
      simp [Fintype.card_pi, ZMod.card, Finset.prod_const]
    rw [hc]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ S.numLogical := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Fin S.numLogical → ZMod 2)
  -- Distinct unit-modulus complex numbers `z m` (Cayley transform), with injective real part.
  have hpos : ∀ m : ℕ, (0 : ℝ) < 1 + (m : ℝ) ^ 2 := fun m => by positivity
  set z : ℕ → ℂ := fun m => ⟨(1 - (m : ℝ) ^ 2) / (1 + (m : ℝ) ^ 2),
                             (2 * (m : ℝ)) / (1 + (m : ℝ) ^ 2)⟩ with hz
  have hnorm : ∀ m, Complex.normSq (z m) = 1 := by
    intro m
    have h := (hpos m).ne'
    rw [hz, Complex.normSq_mk]
    field_simp
    ring
  have hstar : ∀ m, star (z m) * z m = 1 := by
    intro m
    rw [mul_comm, show star (z m) = (starRingEnd ℂ) (z m) from rfl, Complex.mul_conj, hnorm,
      Complex.ofReal_one]
  have hzinj : Function.Injective z := by
    intro m m' h
    have hre : (z m).re = (z m').re := congrArg Complex.re h
    simp only [hz] at hre
    rw [div_eq_div_iff (hpos m).ne' (hpos m').ne'] at hre
    have hmm : (m : ℝ) ^ 2 = (m' : ℝ) ^ 2 := by nlinarith [hre]
    have : (m : ℝ) = (m' : ℝ) := by nlinarith [sq_nonneg ((m : ℝ) - m'), sq_nonneg ((m : ℝ) + m'), hmm]
    exact_mod_cast this
  -- The diagonal family `D m = diag(1,…,z m,…,1)` (entry `z m` at index `b`).
  set d : ℕ → (Fin S.numLogical → ZMod 2) → ℂ := fun m i => if i = b then z m else 1 with hd
  set D : ℕ → Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ :=
    fun m => Matrix.diagonal (d m) with hD
  have hUnit : ∀ m, D m ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ := by
    intro m
    rw [Matrix.mem_unitaryGroup_iff', hD, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, hd]
    by_cases hi : i = b
    · simp only [hi, if_true]; exact hstar m
    · simp only [hi, if_false, star_one, mul_one]
  have hDbb : ∀ m, D m b b = z m := by
    intro m; simp only [hD, Matrix.diagonal_apply_eq, hd, if_pos]
  have hDaa : ∀ m, D m a a = 1 := by
    intro m; simp only [hD, Matrix.diagonal_apply_eq, hd, if_neg hab]
  refine ⟨Set.range D, ?_, ?_, ?_⟩
  · rintro V ⟨m, rfl⟩; exact hUnit m
  · rintro V ⟨m, rfl⟩ V' ⟨m', rfl⟩ hne c hc
    have ha : D m a a = c * D m' a a := by rw [hc, Matrix.smul_apply, smul_eq_mul]
    rw [hDaa, hDaa, mul_one] at ha            -- ha : 1 = c
    have hb : D m b b = c * D m' b b := by rw [hc, Matrix.smul_apply, smul_eq_mul]
    rw [hDbb, hDbb, ← ha, one_mul] at hb      -- hb : z m = z m'
    exact hne (by rw [hzinj hb])
  · apply Set.infinite_range_of_injective
    intro m m' h
    have hb : D m b b = D m' b b := by rw [h]
    rw [hDbb, hDbb] at hb
    exact hzinj hb

/-- **Eastin–Knill theorem** (reduced to the finiteness of the transversal logical group). For a
code that detects at least one error (`distance ≥ 2`) and encodes at least one logical qubit, the
transversal gates are *not universal*: some logical unitary cannot be implemented transversally.

Proof: the logical unitary group contains an infinite pairwise-non-proportional family
(`exists_infinite_nonproportional_unitary`); if transversal gates were universal, that whole family
would be transversally implementable, contradicting `transversal_logical_finite` (transversal
logicals are finite up to global phase). The algebraic engine behind the finiteness is
`StabGroup.compress_scalar_of_weight_lt`. -/
theorem eastin_knill (hd : 2 ≤ S.distance) (hk : 1 ≤ S.numLogical) :
    ¬ ∀ V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ,
        ∃ U, IsTransversal U ∧ S.ImplementsLogical U V := by
  intro hall
  obtain ⟨T, hTunit, hTpair, hTinf⟩ := S.exists_infinite_nonproportional_unitary hk
  exact hTinf (S.transversal_logical_finite hd T (fun V hV => hall V (hTunit V hV)) hTpair)
end StabGroup
end PauliOp
end QuantumLib
