/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.QECC.StabilizerFacts

/-!
# CSS codes

Calderbank–Shor–Steane codes: build a stabilizer group from two classical binary codes with a
dual-containment condition. The `X`-type generators come from one parity-check matrix, the `Z`-type
from the other; commutation is exactly dual containment.
-/

@[expose] public section

open scoped BigOperators
namespace QuantumLib
namespace PauliOp
variable {n : ℕ}

/-- A **CSS stabilizer group** from `r` `X`-checks and `s` `Z`-checks satisfying the dual-containment
(orthogonality) condition `∑ₖ (hx i)ₖ (hz j)ₖ = 0`. -/
def cssCode {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2)) (hz : Fin s → (Fin n → ZMod 2))
    (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) : StabGroup n where
  carrier := Subgroup.closure
    ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
     (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n)))
  isComm := by
    -- tau is injective
    have tau_inj : ∀ s t : ZMod 2, tau s = tau t → s = t := by decide
    -- First, prove a helper: P * Q = Q * P ↔ betaPair P Q = betaPair Q P
    have commute_iff : ∀ P Q : PauliOp n, P * Q = Q * P ↔ betaPair P Q = betaPair Q P := by
      intro P Q
      constructor
      · intro h
        have h1 := congrArg PauliOp.phase h
        simp only [mul_phase] at h1
        exact tau_inj _ _ (by simpa [add_comm P.phase Q.phase] using h1)
      · intro h
        exact PauliOp.ext (by simp [mul_phase, h]; ring) (by simp [mul_x]; ring) (by simp [mul_z]; ring)
    -- Now show generators pairwise commute
    have gen_comm : ∀ x ∈ ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))),
        ∀ y ∈ ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))), betaPair x y = betaPair y x := by
      intro x hx y hy
      rcases hx with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rcases hy with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · simp [betaPair]
      · simp [betaPair, mul_comm, hdual i j']
      · simp [betaPair, mul_comm, hdual i' j]
      · simp [betaPair]
    -- Use subgroup closure induction
    let S := Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n)))
    have goal : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
      apply Subgroup.closure_induction
      · -- generators
        intro x hx
        apply Subgroup.closure_induction
        · -- b is a generator: use gen_comm and commute_iff
          intro y hy
          exact (commute_iff x y).mpr (gen_comm x hx y hy)
        · -- b = 1
          simp
        · -- b = y * z
          intro y z hy hz hy' hz'
          exact Commute.mul_right hy' hz'
        · -- b = y⁻¹
          intro y hy hy'
          exact Commute.inv_right hy'
      · -- identity
        intro b hb
        simp
      · -- multiplication
        intro x y hx hy hx' hy' b hb
        exact Commute.mul_left (hx' b hb) (hy' b hb)
      · -- inverse
        intro x hx hx' b hb
        exact Commute.inv_left (hx' b hb)
    exact goal
  negI_notMem := by
    -- All generators have phase 0 and pairwise betaPair = 0,
    -- so all elements in the closure have phase 0.
    -- negI has phase 2, so it's not in the subgroup.
    have hclosure : ∀ g ∈ Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))), g.phase = 0 := by
      -- Stronger: all elements have the form ⟨0, x, z⟩
      have hstrong : ∀ g ∈ Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))),
        ∃ x' z' : Fin n → ZMod 2, g = ⟨0, x', z'⟩ := by
        -- Stronger invariant: all elements have phase 0 and pairwise betaPair = 0
        let H : Subgroup (PauliOp n) := Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
            (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n)))
        have hX_gen : ∀ i, (⟨0, hx i, 0⟩ : PauliOp n) ∈ H := fun i =>
            Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
        have hZ_gen : ∀ j, (⟨0, 0, hz j⟩ : PauliOp n) ∈ H := fun j =>
            Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
        -- Key: generators commute so betaPair = 0
        have betaPair_X_X : ∀ i i', betaPair (⟨0, hx i, 0⟩ : PauliOp n) (⟨0, hx i', 0⟩) = 0 := by
            intro i i'
            simp [betaPair]
        have betaPair_Z_Z : ∀ j j', betaPair (⟨0, 0, hz j⟩ : PauliOp n) (⟨0, 0, hz j'⟩) = 0 := by
            intro j j'
            simp [betaPair]
        have betaPair_Z_X : ∀ j i, betaPair (⟨0, 0, hz j⟩ : PauliOp n) (⟨0, hx i, 0⟩) = 0 := by
            intro j i
            simp [betaPair, mul_comm, hdual i j]
        have betaPair_X_Z : ∀ i j, betaPair (⟨0, hx i, 0⟩ : PauliOp n) (⟨0, 0, hz j⟩) = 0 := by
            intro i j
            simp [betaPair]
        -- First prove generators commute with all elements of H
        have hX_check : ∀ i, ∀ g' ∈ H, betaPair (⟨0, hx i, 0⟩ : PauliOp n) g' = 0 := by
            intro i g' hg'
            unfold H at hg'
            apply Subgroup.closure_induction
              (k := ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
                (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))))
              (p := fun g _ => betaPair (⟨0, hx i, 0⟩ : PauliOp n) g = 0)
            · -- generators
              intro g hg'
              rcases hg' with ⟨i', rfl⟩ | ⟨j', rfl⟩ <;> [exact betaPair_X_X i i'; exact betaPair_X_Z i j']
            · -- identity
              exact betaPair_one_left _
            · -- mul
              intro g₁ g₂ _ _ h₁ h₂
              rw [betaPair_mul_right, h₁, h₂, add_zero]
            · -- inv
              intro g _ hg'
              exact hg'
            exact hg'
        have hZ_check : ∀ j, ∀ g' ∈ H, betaPair (⟨0, 0, hz j⟩ : PauliOp n) g' = 0 := by
            intro j g' hg'
            unfold H at hg'
            apply Subgroup.closure_induction
              (k := ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
                (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))))
              (p := fun g _ => betaPair (⟨0, 0, hz j⟩ : PauliOp n) g = 0)
            · -- generators
              intro g hg'
              rcases hg' with ⟨i', rfl⟩ | ⟨j', rfl⟩ <;> [exact betaPair_Z_X j i'; exact betaPair_Z_Z j j']
            · -- identity
              exact betaPair_one_right _
            · -- mul
              intro g₁ g₂ _ _ h₁ h₂
              rw [betaPair_mul_right, h₁, h₂, add_zero]
            · -- inv
              intro g _ hg'
              exact hg'
            exact hg'
        -- Now prove the main invariant by closure induction
        have hbase : ∀ g ∈ (Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
            (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n)), g.phase = 0 ∧
            ∀ g' ∈ H, betaPair g g' = 0 := by
            rintro g (hr | hr)
            · rcases hr with ⟨i, rfl⟩
              exact ⟨by simp, hX_check i⟩
            · rcases hr with ⟨j, rfl⟩
              exact ⟨by simp, hZ_check j⟩
        have inlinev : ∀ g ∈ Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
              (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))), g.phase = 0 ∧
            ∀ g' ∈ Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
              (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))), betaPair g g' = 0 := by
            intro g hg
            apply Subgroup.closure_induction
              (k := ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
                (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))))
              (p := fun g _ => g.phase = 0 ∧ ∀ g' ∈ H, betaPair g g' = 0)
            · -- generators
              intro g hg
              exact hbase g hg
            · -- identity
              simp
            · -- mul
              intro g₁ g₂ _ _ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
              constructor
              · simp [mul_phase, h₁, h₂, h₁' g₂ (by assumption)]
              · intro g' hg'
                simp [betaPair_mul_left, h₁' g' hg', h₂' g' hg']
            · -- inv
              intro g _ ⟨hg, hinv⟩
              refine ⟨?_, ?_⟩
              · simp [show (g⁻¹ : PauliOp n).phase = -g.phase - tau (betaPair g g) from rfl,
                  hg, hinv g (by assumption)]
              · intro g' hg'
                exact hinv g' hg'
            exact hg
        intro g hg
        have hphase := (inlinev g hg).1
        exact ⟨g.x, g.z, by ext <;> simp [hphase]⟩
      intro g hg
      rcases hstrong g hg with ⟨x', z', hg'⟩
      simp [hg']
    intro h
    have hg := hclosure (negI n) h
    simp [negI] at hg
    have : (2 : ZMod 4) ≠ 0 := by decide
    exact this hg

namespace StabGroup

/-- The `X`-type generators of a CSS code are members of its stabilizer group. -/
theorem cssCode_xcheck_mem {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2))
    (hz : Fin s → (Fin n → ZMod 2)) (hdual) (i : Fin r) :
    (⟨0, hx i, 0⟩ : PauliOp n) ∈ (cssCode hx hz hdual).carrier :=
  Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

/-- The `Z`-type generators of a CSS code are members of its stabilizer group. -/
theorem cssCode_zcheck_mem {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2))
    (hz : Fin s → (Fin n → ZMod 2)) (hdual) (j : Fin s) :
    (⟨0, 0, hz j⟩ : PauliOp n) ∈ (cssCode hx hz hdual).carrier :=
  Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)

/-- **CSS logical count:** `k = n − rank(Hₓ) − rank(H_z)`. -/
theorem cssCode_numLogical_le {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2))
    (hz : Fin s → (Fin n → ZMod 2)) (hdual) :
    (cssCode hx hz hdual).numLogical ≤ n := numLogical_le_numPhysical _

/-- **CSS distance:** at least the minimum distance of the two underlying classical codes.
Stated as: a low-weight logical forces a low-weight nonzero vector orthogonal to the checks. -/
theorem cssCode_distance_ge {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2))
    (hz : Fin s → (Fin n → ZMod 2)) (hdual) (d : ℕ)
    (hX : ∀ v : Fin n → ZMod 2, (∀ j, ∑ k, v k * hz j k = 0) → (∃ i, v = hx i) ∨
        d ≤ (Finset.univ.filter (fun k => v k ≠ 0)).card)
    (hZ : ∀ v : Fin n → ZMod 2, (∀ i, ∑ k, hx i k * v k = 0) → (∃ j, v = hz j) ∨
        d ≤ (Finset.univ.filter (fun k => v k ≠ 0)).card) :
    d ≤ (cssCode hx hz hdual).distance := by sorry

/-- A CSS code built from a single self-orthogonal code (`H·Hᵀ = 0`) is self-dual. -/
theorem cssCode_selfDual_isComm {r : ℕ} (h : Fin r → (Fin n → ZMod 2))
    (hself : ∀ i j, ∑ k, h i k * h j k = 0) :
    ∀ a ∈ (cssCode h h hself).carrier, ∀ b ∈ (cssCode h h hself).carrier, a * b = b * a :=
  (cssCode h h hself).isComm

end StabGroup
end PauliOp
end QuantumLib
