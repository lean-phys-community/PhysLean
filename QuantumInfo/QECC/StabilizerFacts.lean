/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.QECC.PauliFacts

/-!
# Error-correction theory of stabilizer codes

Detection, correction, distance, degeneracy, syndromes, and the Knill–Laflamme conditions,
stated on the faithful `StabGroup` model. Most proofs are left to the ATP.
-/

@[expose] public section

open scoped BigOperators
namespace QuantumLib
namespace PauliOp
namespace StabGroup
variable {n : ℕ} (S : StabGroup n)

/-! ### Elementary consequences of the group axioms -/

/-- Any two stabilizer elements commute. -/
theorem mem_commute {g h : PauliOp n} (hg : g ∈ S.carrier) (hh : h ∈ S.carrier) :
    g * h = h * g := S.isComm _ hg _ hh

/-- A stabilizer element commutes with an error iff their symplectic form vanishes;
detectability is exactly the failure of this for *some* generator. -/
theorem detectable_iff_not_mem_centralizer (E : PauliOp n) :
    S.Detectable E ↔
      E ∈ S.carrier ⊔ phaseSubgroup n ∨ E ∉ Subgroup.centralizer (S.carrier : Set (PauliOp n)) := by
  simp [Detectable, Subgroup.mem_centralizer_iff, ne_comm]

/-! ### Distance -/

/-- The code distance is positive whenever a logical operator exists (nontrivial code). -/
theorem one_le_distance (h : ∃ g, S.IsLogical g) : 1 ≤ S.distance := by
  obtain ⟨g0, hg0⟩ := h
  have hne : {w | ∃ g, S.IsLogical g ∧ weight g = w}.Nonempty := ⟨weight g0, g0, hg0, rfl⟩
  have hmem : S.distance ∈ {w | ∃ g, S.IsLogical g ∧ weight g = w} := Nat.sInf_mem hne
  obtain ⟨g, hg, hw⟩ := hmem
  have hpos := S.isLogical_weight_pos hg
  omega

/-- The distance is realized: some logical operator has weight equal to the distance. -/
theorem exists_logical_weight_eq_distance (h : ∃ g, S.IsLogical g) :
    ∃ g, S.IsLogical g ∧ weight g = S.distance := by
  obtain ⟨g, hg⟩ := h
  exact Nat.sInf_mem (⟨weight g, g, hg, rfl⟩ : {w | ∃ g, S.IsLogical g ∧ weight g = w}.Nonempty)

/-- **Correction below half the distance:** any two errors of weight `≤ t` with `distance ≥ 2t+1`
have a detectable "difference" `E⁻¹F`, hence are jointly correctable. -/
theorem detectable_of_le_half_distance {t : ℕ} {E F : PauliOp n}
    (hE : weight E ≤ t) (hF : weight F ≤ t) (hd : 2 * t < S.distance) :
    S.Detectable (E⁻¹ * F) := by
  apply S.detectable_of_weight_lt_distance
  calc weight (E⁻¹ * F) ≤ weight E⁻¹ + weight F := weight_mul_le _ _
    _ = weight E + weight F := by rw [weight_inv]
    _ ≤ t + t := by omega
    _ = 2 * t := by ring
    _ < S.distance := hd

/-- A code of distance `d` corrects all errors of weight `≤ ⌊(d-1)/2⌋`. -/
theorem corrects_of_two_mul_lt_distance {E F : PauliOp n}
    (hE : 2 * weight E < S.distance) (hF : 2 * weight F < S.distance) :
    S.Detectable (E⁻¹ * F) := by
      exact StabGroup.detectable_mul_of_weight_lt S hE hF

/-! ### Syndromes and degeneracy -/

/-- Two Paulis are **syndrome-equivalent** for `S` if they commute with exactly the same
stabilizer elements (equivalently, differ by an element of the centralizer). -/
def SyndromeEq (E F : PauliOp n) : Prop :=
  ∀ g ∈ S.carrier, (E * g = g * E ↔ F * g = g * F)

/-- Syndrome-equivalence is an equivalence relation. -/
theorem syndromeEq_equivalence : Equivalence S.SyndromeEq := by
  exact ⟨fun _ _ _ => Iff.rfl, fun h g hg => (h g hg).symm,
    fun hxy hyz g hg => (hxy g hg).trans (hyz g hg)⟩

/-- An error and any stabilizer multiple share the same syndrome. -/
theorem syndromeEq_mul_mem {E g : PauliOp n} (hg : g ∈ S.carrier) :
    S.SyndromeEq E (E * g) := by
  intro h hh
  constructor
  · intro hc
    calc (E * g) * h = E * (g * h) := by rw [mul_assoc]
      _ = E * (h * g) := by rw [S.mem_commute hg hh]
      _ = (E * h) * g := by rw [mul_assoc]
      _ = (h * E) * g := by rw [hc]
      _ = h * (E * g) := by rw [mul_assoc]
  · intro hc
    have hgh : g * h = h * g := S.mem_commute hg hh
    have : E * h * g = h * E * g := by
      calc E * h * g = E * (h * g) := by rw [mul_assoc]
        _ = E * (g * h) := by rw [hgh]
        _ = (E * g) * h := by rw [mul_assoc]
        _ = h * (E * g) := hc
        _ = h * E * g := by rw [mul_assoc]
    exact mul_right_cancel this

/-- A stabilizer code is **degenerate** if two distinct logical-inequivalent errors of weight
below the distance act identically on the code space. -/
def IsDegenerate : Prop :=
  ∃ E F : PauliOp n, E ≠ F ∧ E * F⁻¹ ∈ S.carrier ∧ weight E < S.distance ∧ weight F < S.distance

/-- On a nondegenerate code, low-weight errors with the same syndrome are equal. -/
theorem eq_of_syndromeEq_of_nondegenerate (hnd : ¬ S.IsDegenerate)
    {E F : PauliOp n} (_hsyn : S.SyndromeEq E F)
    (hE : weight E < S.distance) (hF : weight F < S.distance) :
    E * F⁻¹ ∈ S.carrier → E = F := by
  intro hEF
  by_contra hne
  exact hnd ⟨E, F, hne, hEF, hE, hF⟩

/-! ### Knill–Laflamme (stabilizer form) -/

/-- **Knill–Laflamme for stabilizer codes:** an error `D` is detectable iff its compression to the
code space is a scalar multiple of the projector, `Π D Π = c Π`. -/
theorem knill_laflamme (D : PauliOp n) :
    S.Detectable D ↔
      ∃ c : ℂ, stabProj S * toMat D * stabProj S = c • stabProj S := by
  rw [S.detectable_iff_not_mem_centralizer]
  let : DecidablePred (· ∈ S.carrier) := fun x => Classical.propDecidable (x ∈ S.carrier)
  constructor
  · -- Forward: (D ∈ sup ∨ D ∉ centralizer) → ∃ c, Compression = c • stabProj
    intro h
    rcases h with hmem | hnot_center
    · -- D ∈ sup implies scalar compression
      -- phaseSubgroup n is normal since its elements are central
      have phase_normal : (phaseSubgroup n).Normal := by
        constructor
        intro g hg x
        simp only [mem_phaseSubgroup] at hg ⊢
        have hweight : weight g = 0 := (weight_eq_zero_iff g).mpr hg
        have hcomm : g * x = x * g := central_of_weight_zero hweight x
        have hconj : x * g * x⁻¹ = g := by
          rw [hcomm.symm]
          simp [mul_assoc]
        simp [hconj, hg]
      rw [Subgroup.mem_sup_of_normal_right (t := phaseSubgroup n)] at hmem
      obtain ⟨g, hg, f, hf, rfl⟩ := hmem
      -- f ∈ phaseSubgroup means f = ⟨f.phase, 0, 0⟩
      have hf0 : f = ⟨f.phase, 0, 0⟩ := by
        have ⟨hfx, hfz⟩ := mem_phaseSubgroup.mp hf
        ext i <;> simp [hfx, hfz]
      -- toMat f is a scalar by toMat_phase
      have hmat_f : toMat f = Complex.I ^ f.phase.val • (1 : Matrix _ _ ℂ) := by
        rw [hf0]
        have h0 : ((0, 0) : PauliSpace n) = 0 := rfl
        simp only [toMat, h0, pauliOp_zero]
      -- toMat (g * f) = toMat g * toMat f = toMat g * (scalar • 1) = scalar • toMat g
      rw [toMat_mul, hmat_f]
      simp only [mul_smul_comm, mul_one]
      -- Use compress_of_mem: stabProj * toMat g * stabProj = stabProj
      use Complex.I ^ f.phase.val
      rw [smul_mul_assoc]
      -- Inline compress_of_mem
      have h1 : toMat g * stabProj S = stabProj S := @toMat_mem_mul_stabProj n S g hg
      have h2 : (toMat g).IsHermitian := @isHermitian_toMat n S g hg
      have h3 : (stabProj S).IsHermitian := @stabProj_isHermitian n S
      have h4 : stabProj S * toMat g = stabProj S := by
        simpa [Matrix.conjTranspose_mul, h2.eq, h3.eq] using congr_arg Matrix.conjTranspose h1
      rw [mul_assoc, h1, stabProj_idem]
    · -- D ∉ centralizer means D anticommutes with some stabilizer, so compression = 0
      simp only [Subgroup.mem_centralizer_iff] at hnot_center
      push Not at hnot_center
      obtain ⟨g, hg, hanti⟩ := hnot_center
      -- We have g * D ≠ D * g, so D * g ≠ g * D
      have hanti' : D * g ≠ g * D := fun h => hanti h.symm
      -- Inline compress_eq_zero_of_anticommutes
      use 0
      rw [zero_smul]
      -- From anticommutation, D * g = negI n * g * D
      have hphase : D * g = negI n * (g * D) := by
        rcases mul_comm_eq_phase D g with hc | hc
        · exact absurd (by rwa [mul_inv_eq_one] at hc) hanti'
        · rwa [mul_inv_eq_iff_eq_mul] at hc
      -- Matrix version: toMat D * toMat g = -toMat g * toMat D
      have hmat : toMat D * toMat g = -toMat g * toMat D := by
        have h1 : toMat (D * g) = toMat (negI n * (g * D)) := by rw [hphase]
        simpa [toMat_mul, toMat_negI, neg_mul, neg_one_mul] using h1
      -- Right multiplication version: stabProj * toMat g = stabProj
      have hstab_right : stabProj S * toMat g = stabProj S := by
        have hg' : star (toMat g) = toMat g := (isHermitian_toMat S hg).isSelfAdjoint
        have hs' : star (stabProj S) = stabProj S := (stabProj_isHermitian S).isSelfAdjoint
        have := congrArg star (toMat_mem_mul_stabProj S hg)
        rwa [star_mul, hg', hs'] at this
      -- Set P = stabProj S * toMat D * stabProj S
      set P := stabProj S * toMat D * stabProj S with hP
      -- Show P = -P using the anticommutation relation
      have hstab_left : toMat g * stabProj S = stabProj S := toMat_mem_mul_stabProj S hg
      have hP_neg : P = -P := by
        have step1 : P = stabProj S * toMat D * toMat g * stabProj S := by
          rw [hP, mul_assoc (stabProj S * toMat D), hstab_left]
        have step2 : P = stabProj S * (-toMat g * toMat D) * stabProj S := by
          rw [step1, mul_assoc (stabProj S) (toMat D) (toMat g), hmat]
        have step3 : P = -(stabProj S * toMat g * toMat D * stabProj S) := by
          rw [step2]; simp [mul_assoc, neg_mul, mul_neg]
        rw [hstab_right, ← hP] at step3
        exact step3
      -- P = -P implies P = 0
      have h1 : P + P = 0 := by nth_rewrite 2 [hP_neg]; exact add_neg_cancel P
      have h2P : (2 : ℂ) • P = 0 := by simp [two_smul] at h1 ⊢; convert h1 using 1
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      exact smul_eq_zero.mp h2P |>.resolve_left h2
  · -- Reverse: ∃ c, Compression = c • stabProj → (D ∈ sup ∨ D ∉ centralizer)
    intro ⟨c, hc⟩
    by_contra h
    push Not at h
    obtain ⟨hnsup, hncent⟩ := h
    -- The compression being scalar means D acts as scalar on code space
    -- But logical operators act non-trivially, contradiction
    by_cases hc0 : c = 0
    · -- If c = 0, then stabProj * toMat D * stabProj = 0
      -- But D is a Pauli (invertible) and commutes with stabilizer, so it preserves codeSpace
      -- Acting as 0 on codeSpace contradicts invertibility
      rw [hc0, zero_smul] at hc
      -- D ∈ centralizer means D commutes with all stabilizers, so D preserves codeSpace
      -- We'll show codeSpace = 0, contradicting codeSpace_ne_bot
      have hD_preserves : ∀ v ∈ codeSpace S, D.toMat.mulVec v ∈ codeSpace S := by
        intro v hv
        rw [codeSpace, Submodule.mem_iInf] at hv ⊢
        intro i
        simp only [LinearMap.mem_ker, Matrix.toLin'_apply, LinearMap.sub_apply, LinearMap.id_apply] at hv ⊢
        -- Need to show: i.val.toMat * (D.toMat * v) = D.toMat * v
        -- Use that i.val and D commute: i.val.toMat * D.toMat = D.toMat * i.val.toMat
        have hDg_comm : D.toMat * i.val.toMat = i.val.toMat * D.toMat := by
          rw [← toMat_mul, ← toMat_mul]
          exact congrArg toMat (Subgroup.mem_centralizer_iff.mp hncent i.val i.prop).symm
        -- codeSpace membership: (i.val.toMat - 1) * v = 0 means i.val.toMat * v = v
        have hvindi : ((↑i : PauliOp n).toMat).mulVec (D.toMat.mulVec v) = D.toMat.mulVec v := by
          have hvi_eq : ((↑i : PauliOp n).toMat).mulVec v = v := sub_eq_zero.mp (hv i)
          rw [Matrix.mulVec_mulVec v i.val.toMat D.toMat]
          rw [hDg_comm.symm]
          rw [(Matrix.mulVec_mulVec v D.toMat i.val.toMat).symm, hvi_eq]
        exact sub_eq_zero.mpr hvindi
      -- From hc : stabProj * D.toMat * stabProj = 0, for v in codeSpace, D.toMat.mulVec v = 0
      -- First, stabProj.mulVec v = v for v in codeSpace
      have h_proj_idem : ∀ v ∈ codeSpace S, Matrix.mulVec (stabProj S) v = v := by
        intro v hv
        have hv_range := (range_stabProj S).symm ▸ hv
        rw [LinearMap.mem_range] at hv_range
        obtain ⟨w, hw⟩ := hv_range
        have hw' : Matrix.toLin' (stabProj S) w = Matrix.mulVec (stabProj S) w := rfl
        calc Matrix.mulVec (stabProj S) v
            = Matrix.mulVec (stabProj S) (Matrix.mulVec (stabProj S) w) := by rw [hw.symm, hw']
          _ = Matrix.mulVec (stabProj S * stabProj S) w := by rw [Matrix.mulVec_mulVec]
          _ = Matrix.mulVec (stabProj S) w := by rw [stabProj_idem]
          _ = v := hw
      -- From hc: stabProj * D.toMat * stabProj = 0
      -- For any v in codeSpace: stabProj.mulVec (D.toMat.mulVec v) = 0
      have h_D_zero : ∀ v ∈ codeSpace S, Matrix.mulVec D.toMat v = 0 := by
        intro v hv
        have h1 : Matrix.mulVec (stabProj S) (Matrix.mulVec D.toMat v) = 0 := by
          have h2 : (stabProj S * D.toMat * stabProj S).mulVec v = 0 := by rw [hc]; simp
          have h2' : (stabProj S * (D.toMat * stabProj S)).mulVec v = 0 := by
            rw [mul_assoc] at h2; exact h2
          rw [← Matrix.mulVec_mulVec v (stabProj S) (D.toMat * stabProj S)] at h2'
          rw [← Matrix.mulVec_mulVec v (D.toMat) (stabProj S)] at h2'
          -- Now h2' : stabProj S.mulVec (D.toMat.mulVec (stabProj S.mulVec v)) = 0
          have hvstabil : Matrix.mulVec (stabProj S) v = v := h_proj_idem v hv
          simp only [hvstabil] at h2'
          exact h2'
        -- Since Matrix.mulVec D.toMat v ∈ codeSpace (by hD_preserves), and stabProj.mulVec = id on codeSpace
        have hv2 := hD_preserves v hv
        rw [h_proj_idem (Matrix.mulVec D.toMat v) hv2] at h1
        exact h1
      -- But D is invertible, so v = 0 for all v in codeSpace
      -- Hence codeSpace = ⊥, contradicting codeSpace_ne_bot
      have hcodeSpace_zero : codeSpace S = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro v hv
        have := h_D_zero v hv
        -- D.toMat is invertible since D is a Pauli
        have hinv : Function.Injective (Matrix.mulVec D.toMat) := by
          have hunit := toMat_mem_unitaryGroup D
          have hmul : D.toMat * star D.toMat = 1 := hunit.2
          intro x y hxy
          -- For unitary matrices, star D.toMat is both left and right inverse
          have hmul' : star D.toMat * D.toMat = 1 := hunit.1
          calc x
              = (star D.toMat * D.toMat).mulVec x := by rw [hmul', Matrix.one_mulVec]
            _ = Matrix.mulVec (star D.toMat) (Matrix.mulVec D.toMat x) := by rw [← Matrix.mulVec_mulVec]
            _ = Matrix.mulVec (star D.toMat) (Matrix.mulVec D.toMat y) := by rw [hxy]
            _ = (star D.toMat * D.toMat).mulVec y := by rw [Matrix.mulVec_mulVec]
            _ = y := by rw [hmul', Matrix.one_mulVec]
        exact hinv (by rw [this]; simp)
      exact codeSpace_ne_bot S hcodeSpace_zero
    · -- c ≠ 0 case: D acts as nonzero scalar on codeSpace
      -- D must be in sup, contradicting hnsup
      -- First show that D acts as scalar c on codeSpace
      have hD_preserves : ∀ v ∈ codeSpace S, D.toMat.mulVec v ∈ codeSpace S := by
        intro v hv
        rw [codeSpace, Submodule.mem_iInf] at hv ⊢
        intro i
        simp only [LinearMap.mem_ker, Matrix.toLin'_apply, LinearMap.sub_apply, LinearMap.id_apply] at hv ⊢
        have hDg_comm : D.toMat * i.val.toMat = i.val.toMat * D.toMat := by
          rw [← toMat_mul, ← toMat_mul]
          exact congrArg toMat (Subgroup.mem_centralizer_iff.mp hncent i.val i.prop).symm
        have hvindi : ((↑i : PauliOp n).toMat).mulVec (D.toMat.mulVec v) = D.toMat.mulVec v := by
          have hvi_eq : ((↑i : PauliOp n).toMat).mulVec v = v := sub_eq_zero.mp (hv i)
          rw [Matrix.mulVec_mulVec v i.val.toMat D.toMat]
          rw [hDg_comm.symm]
          rw [(Matrix.mulVec_mulVec v D.toMat i.val.toMat).symm, hvi_eq]
        exact sub_eq_zero.mpr hvindi
      have h_proj_idem : ∀ v ∈ codeSpace S, Matrix.mulVec (stabProj S) v = v := by
        intro v hv
        have hv_range := (range_stabProj S).symm ▸ hv
        rw [LinearMap.mem_range] at hv_range
        obtain ⟨w, hw⟩ := hv_range
        have hw' : Matrix.toLin' (stabProj S) w = Matrix.mulVec (stabProj S) w := rfl
        calc Matrix.mulVec (stabProj S) v
            = Matrix.mulVec (stabProj S) (Matrix.mulVec (stabProj S) w) := by rw [hw.symm, hw']
          _ = Matrix.mulVec (stabProj S * stabProj S) w := by rw [Matrix.mulVec_mulVec]
          _ = Matrix.mulVec (stabProj S) w := by rw [stabProj_idem]
          _ = v := hw
      have h_D_scalar : ∀ v ∈ codeSpace S, Matrix.mulVec D.toMat v = c • v := by
        intro v hv
        have h1 : Matrix.mulVec (stabProj S) (Matrix.mulVec D.toMat v) = c • v := by
          have h2 : Matrix.mulVec (stabProj S * D.toMat * stabProj S) v = c • Matrix.mulVec (stabProj S) v := by
            rw [hc]
            rw [Matrix.smul_mulVec]
          -- Rewrite LHS using associativity
          have hlhs : Matrix.mulVec (stabProj S * D.toMat * stabProj S) v =
                       Matrix.mulVec (stabProj S) (Matrix.mulVec (D.toMat) (Matrix.mulVec (stabProj S) v)) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
          have hvstabil : Matrix.mulVec (stabProj S) v = v := h_proj_idem v hv
          rw [hlhs, hvstabil] at h2
          exact h2
        have hv2 := hD_preserves v hv
        rw [h_proj_idem (Matrix.mulVec D.toMat v) hv2] at h1
        exact h1
      -- Use hc to show contradiction with hnsup
      -- D acts as scalar c on codeSpace, so D ∈ S.carrier ⊔ phaseSubgroup n
      -- We have hlogic : S.IsLogical D and h_D_scalar : D acts as scalar c ≠ 0 on codeSpace
      -- This is a contradiction because logical operators act nontrivially on codeSpace
      -- D commutes with stabilizer, so D commutes with stabProj
      have hD_comm_stabProj : D.toMat * stabProj S = stabProj S * D.toMat := by
        have : ∀ g ∈ S.carrier, D.toMat * (g.toMat : Matrix _ _ ℂ) = g.toMat * D.toMat := by
          intro g hg
          have := Subgroup.mem_centralizer_iff.mp hncent g hg
          rw [← toMat_mul, ← toMat_mul] at *
          exact congrArg toMat this.symm
        simp only [stabProj]
        rw [Matrix.smul_mul, Matrix.mul_smul]
        congr 1
        rw [Matrix.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        rw [this g.1 g.2]

      -- D commutes with stabProj, so stabProj * D * stabProj = D * stabProj
      have htr_comm : S.stabProj * D.toMat * S.stabProj = D.toMat * S.stabProj := by
        rw [mul_assoc, hD_comm_stabProj, ← mul_assoc, stabProj_idem]
      -- trace(stabProj * D * stabProj) = trace(D * stabProj)
      have htr_simplified : Matrix.trace (S.stabProj * D.toMat * S.stabProj) = Matrix.trace (D.toMat * S.stabProj) := by
        rw [htr_comm]
      -- Final piece: D ∉ sup means for all g ∈ S.carrier, D * g ∉ phaseSubgroup, so trace(D * g) = 0
      have htr_prod_zero : Matrix.trace (D.toMat * S.stabProj) = 0 := by
        simp only [stabProj]
        -- D * stabProj = (1/|S|) * ∑ g, D * g.toMat
        have hD_mul_smul : D.toMat * (↑(Fintype.card ↥S.carrier) : ℂ)⁻¹ • ∑ g : ↥S.carrier, (g.1).toMat =
               (↑(Fintype.card ↥S.carrier) : ℂ)⁻¹ • ∑ g : ↥S.carrier, (D * g.1).toMat := by
          rw [mul_smul_comm]
          simp_rw [Matrix.mul_sum, toMat_mul]
        conv_lhs => arg 1; rw [hD_mul_smul]
        rw [Matrix.trace_smul]
        have hcard_ne : ((Fintype.card S.carrier) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        have hcard_inv_ne : ((Fintype.card S.carrier) : ℂ)⁻¹ ≠ 0 := inv_ne_zero hcard_ne
        simp [hcard_inv_ne]
        apply Finset.sum_eq_zero
        intro g _
        simp [toMat_trace]
        -- For g ∈ S.carrier, need: D * g ∉ phaseSubgroup
        by_contra hDg_list
        push Not at hDg_list
        -- D * g has x=0 and z=0 means D * g ∈ phaseSubgroup
        have hDg_mem : D * g.1 ∈ phaseSubgroup n := mem_phaseSubgroup.mpr hDg_list
        -- So D = (D * g) * g⁻¹ ∈ phaseSubgroup * carrier ⊆ sup
        have hg_inv : (g.1)⁻¹ ∈ S.carrier := Subgroup.inv_mem _ g.2
        have hD_eq : D = (D * g.1) * g.1⁻¹ := by rw [mul_inv_cancel_right]
        have hD_in_sup : D ∈ S.carrier ⊔ phaseSubgroup n := by
          rw [hD_eq]
          rw [sup_comm]
          exact Subgroup.mul_mem_sup hDg_mem hg_inv
        exact hnsup hD_in_sup
      -- Now we have trace(stabProj * D * stabProj) = 0
      -- But also trace(stabProj * D * stabProj) = c * dim(codeSpace) from hc
      -- So c * dim(codeSpace) = 0, and since codeSpace ≠ ⊥, we get c = 0, contradiction
      have htr_eq : Matrix.trace (S.stabProj * D.toMat * S.stabProj) = c * Module.finrank ℂ (S.codeSpace) := by
        rw [hc]
        rw [Matrix.trace_smul, StabGroup.stabProj_trace, finrank_codeSpace]
        have hdiv : Fintype.card S.carrier ∣ 2 ^ n := Dvd.intro _ (card_mul_codeSpace_finrank S)
        have hdiv_cast : (2 ^ n : ℂ) / (Fintype.card S.carrier : ℂ) = ↑(2 ^ n / Fintype.card S.carrier) := by
          rw [Nat.cast_div hdiv (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))]
          simp
        rw [smul_eq_mul, hdiv_cast]
      rw [htr_simplified, htr_prod_zero] at htr_eq
      -- htr_eq : 0 = c * Module.finrank ℂ (S.codeSpace)
      have hfinrank_pos : 0 < Module.finrank ℂ (S.codeSpace) :=
        Nat.zero_lt_of_lt (by exact_mod_cast Submodule.one_le_finrank_iff.mpr (codeSpace_ne_bot S))
      have hc_zero : c = 0 :=
        (mul_eq_zero.mp htr_eq.symm).resolve_right (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hfinrank_pos))
      exact hc0 hc_zero

/-- The compression of a *stabilizer* element to the code space is the projector itself. -/
theorem compress_of_mem {g : PauliOp n} (hg : g ∈ S.carrier) :
    stabProj S * toMat g * stabProj S = stabProj S := by
  have h1 : toMat g * stabProj S = stabProj S := @toMat_mem_mul_stabProj n S g hg
  have h2 : (toMat g).IsHermitian := @isHermitian_toMat n S g hg
  have h3 : (stabProj S).IsHermitian := @stabProj_isHermitian n S
  have h4 : stabProj S * toMat g = stabProj S := by
    simpa [Matrix.conjTranspose_mul, h2.eq, h3.eq] using congr_arg Matrix.conjTranspose h1
  rw [mul_assoc, h1, stabProj_idem]

/-- The compression of an *anticommuting* error vanishes on the code space. -/
theorem compress_eq_zero_of_anticommutes {D g : PauliOp n} (hg : g ∈ S.carrier)
    (h : D * g ≠ g * D) :
    stabProj S * toMat D * stabProj S = 0 := by
  -- From anticommutation, D * g = negI n * g * D
  have hphase : D * g = negI n * (g * D) := by
    rcases mul_comm_eq_phase D g with hc | hc
    · exact absurd (by rwa [mul_inv_eq_one] at hc) h
    · rwa [mul_inv_eq_iff_eq_mul] at hc
  -- Matrix version: toMat D * toMat g = -toMat g * toMat D
  have hmat : toMat D * toMat g = -toMat g * toMat D := by
    have h1 : toMat (D * g) = toMat (negI n * (g * D)) := by rw [hphase]
    simpa [toMat_mul, toMat_negI, neg_mul, neg_one_mul] using h1
  -- Right multiplication version: stabProj * toMat g = stabProj (from Hermitian)
  have hstab_right : stabProj S * toMat g = stabProj S := by
    have hg' : star (toMat g) = toMat g := (isHermitian_toMat S hg).isSelfAdjoint
    have hs' : star (stabProj S) = stabProj S := (stabProj_isHermitian S).isSelfAdjoint
    have := congrArg star (toMat_mem_mul_stabProj S hg)
    rwa [star_mul, hg', hs'] at this
  -- Set P = stabProj S * toMat D * stabProj S
  set P := stabProj S * toMat D * stabProj S with hP
  -- Show P = -P using the anticommutation relation
  have hP_neg : P = -P := by
    -- Use toMat_mem_mul_stabProj: toMat g * stabProj S = stabProj S
    have hstab_left : toMat g * stabProj S = stabProj S := toMat_mem_mul_stabProj S hg
    -- P = S * D * S = S * D * S * 1 = S * D * (g * S) = S * D * g * S
    have step1 : P = stabProj S * toMat D * toMat g * stabProj S := by
      rw [hP, mul_assoc (stabProj S * toMat D), hstab_left]
    have step2 : P = stabProj S * (-toMat g * toMat D) * stabProj S := by
      rw [step1, mul_assoc (stabProj S) (toMat D) (toMat g), hmat]
    -- Pull out the negative and use hstab_right: stabProj S * toMat g = stabProj S
    have step3 : P = -(stabProj S * toMat g * toMat D * stabProj S) := by
      rw [step2]; simp [mul_assoc, neg_mul, mul_neg]
    rw [hstab_right, ← hP] at step3
    exact step3
  -- P = -P implies P = 0
  have h1 : P + P = 0 := by nth_rewrite 2 [hP_neg]; exact add_neg_cancel P
  have h2P : (2 : ℂ) • P = 0 := by simp [two_smul] at h1 ⊢; convert h1 using 1
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  exact smul_eq_zero.mp h2P |>.resolve_left h2

/-! ### Knill–Laflamme compression (the algebraic heart of Eastin–Knill) -/

/-- A global phase `iᵏ·I` has scalar matrix `iᵏ • 1`. -/
theorem toMat_phase (k : ZMod 4) :
    toMat (⟨k, 0, 0⟩ : PauliOp n) =
      Complex.I ^ k.val • (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) := by
  have hxz : ((⟨k, 0, 0⟩ : PauliOp n).x, (⟨k, 0, 0⟩ : PauliOp n).z) = (0 : PauliSpace n) := rfl
  simp only [toMat, hxz, pauliOp_zero]

/-- A stabilizer-times-phase element compresses to a scalar multiple of the code projector. -/
theorem compress_scalar_of_mem_sup {D : PauliOp n} (hD : D ∈ S.carrier ⊔ phaseSubgroup n) :
    ∃ c : ℂ, stabProj S * toMat D * stabProj S = c • stabProj S := by
  -- The phase subgroup is central (phases commute with everything), hence normal
  have hcentral : ∀ (k : ZMod 4) (g : PauliOp n), ⟨k, 0, 0⟩ * g = g * ⟨k, 0, 0⟩ := by
    intro k g
    ext <;> simp [mul_x, mul_z, mul_phase, betaPair, add_comm]
  have hnormal : (phaseSubgroup n).Normal := by
    constructor
    intro p hp g
    simp only [mem_phaseSubgroup] at hp
    have hp_eq : p = ⟨p.phase, 0, 0⟩ := by ext <;> simp [hp]
    rw [hp_eq]
    have : g * ⟨p.phase, 0, 0⟩ * g⁻¹ = ⟨p.phase, 0, 0⟩ := by
      rw [(hcentral p.phase g).symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    simp [mem_phaseSubgroup]
  -- Extract g ∈ S.carrier and p ∈ phaseSubgroup n with D = g * p
  rw [Subgroup.mem_sup_of_normal_right] at hD
  obtain ⟨g, hg, p, hp, rfl⟩ := hD
  -- p ∈ phaseSubgroup n means p.x = 0 ∧ p.z = 0
  simp only [mem_phaseSubgroup] at hp
  -- Write p using its phase
  have hp_eq : p = ⟨p.phase, 0, 0⟩ := by ext <;> simp [hp]
  -- Use toMat_mul and toMat_phase
  rw [toMat_mul, hp_eq, toMat_phase]
  -- Factor out the scalar
  use Complex.I ^ p.phase.val
  have h1 : toMat g * stabProj S = stabProj S := toMat_mem_mul_stabProj S hg
  have h4 : stabProj S * toMat g = stabProj S := by
    have h1' : (toMat g * stabProj S).conjTranspose = (stabProj S).conjTranspose :=
      congr_arg Matrix.conjTranspose h1
    simp only [Matrix.conjTranspose_mul] at h1'
    rw [isHermitian_toMat S hg, stabProj_isHermitian S] at h1'
    exact h1'
  simp [h4, stabProj_idem]

/-- **Knill–Laflamme (forward direction):** every *detectable* error compresses to a scalar
multiple of the code projector `Π D Π = c Π` — either it is a stabilizer-times-phase (scalar `c`)
or it anticommutes with a stabilizer generator (`c = 0`). -/
theorem compress_scalar_of_detectable {D : PauliOp n} (hD : S.Detectable D) :
    ∃ c : ℂ, stabProj S * toMat D * stabProj S = c • stabProj S := by
  rcases hD with hmem | ⟨g, hg, hanti⟩
  · exact S.compress_scalar_of_mem_sup hmem
  · exact ⟨0, by rw [zero_smul]; exact S.compress_eq_zero_of_anticommutes hg hanti⟩

/-- **The algebraic heart of Eastin–Knill:** any Pauli error of weight below the code distance
compresses to a scalar on the code space. In particular a *weight-one* error (present in the Pauli
expansion of any single-qubit gate) acts as a scalar whenever the code detects single errors
(`distance ≥ 2`). -/
theorem compress_scalar_of_weight_lt {D : PauliOp n} (hw : weight D < S.distance) :
    ∃ c : ℂ, stabProj S * toMat D * stabProj S = c • stabProj S :=
  S.compress_scalar_of_detectable (S.detectable_of_weight_lt_distance hw)

end StabGroup
end PauliOp
end QuantumLib
