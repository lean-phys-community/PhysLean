/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.QECC.CSS

/-!
# A zoo of stabilizer codes

Concrete stabilizer groups and their `⟦n,k,d⟧` parameters: the repetition code, the perfect
`⟦5,1,3⟧` code, Shor's `⟦9,1,3⟧` code, and the Steane `⟦7,1,3⟧` code.
-/

open scoped BigOperators
namespace QuantumLib
namespace PauliOp

/-! ### Bit-flip repetition code `⟦n,1,n⟧` -/

/-- The cyclic bit-flip repetition code: `Z`-type stabilizers `ZᵢZᵢ₊₁`. -/
def repetitionCode (n : ℕ) [NeZero n] : StabGroup n :=
  cssCode Fin.elim0 (fun i : Fin n => Pi.single i 1 + Pi.single (i + 1) 1)
    (by intro i; exact Fin.elim0 i)

@[simp] theorem repetitionCode_numPhysical (n : ℕ) [NeZero n] :
    (repetitionCode n).numPhysical = n := rfl

/-- The repetition code encodes one logical qubit. -/
theorem repetitionCode_numLogical {n : ℕ} [NeZero n] : (repetitionCode n).numLogical = 1 := by sorry  -- v4.28 ATP proof does not port to v4.31 (fin_cases typeclass); needs portable proof
/-! ### The perfect five-qubit code `⟦5,1,3⟧` -/

/-- The five-qubit code, from the cyclic generator `XZZXI`. -/
def fiveQubitCode : StabGroup 5 :=
  { carrier := Subgroup.closure {
      (⟨0, ![1,0,0,1,0], ![0,1,1,0,0]⟩ : PauliOp 5),
      (⟨0, ![0,1,0,0,1], ![0,0,1,1,0]⟩ : PauliOp 5),
      (⟨0, ![1,0,1,0,0], ![0,0,0,1,1]⟩ : PauliOp 5),
      (⟨0, ![0,1,0,1,0], ![1,0,0,0,1]⟩ : PauliOp 5) }
    isComm := by sorry
    negI_notMem := by sorry }

@[simp] theorem fiveQubitCode_numPhysical : fiveQubitCode.numPhysical = 5 := rfl

theorem fiveQubitCode_numLogical : fiveQubitCode.numLogical = 1 := by
  letI : DecidablePred (fun x => x ∈ fiveQubitCode.carrier) := @fun a => Classical.propDecidable (a ∈ fiveQubitCode.carrier)
  have hcard : Fintype.card fiveQubitCode.carrier = 16 := by
    -- Define the four generators
    let g0 : PauliOp 5 := ⟨0, ![1,0,0,1,0], ![0,1,1,0,0]⟩
    let g1 : PauliOp 5 := ⟨0, ![0,1,0,0,1], ![0,0,1,1,0]⟩
    let g2 : PauliOp 5 := ⟨0, ![1,0,1,0,0], ![0,0,0,1,1]⟩
    let g3 : PauliOp 5 := ⟨0, ![0,1,0,1,0], ![1,0,0,0,1]⟩
    -- Verify membership
    have hg0 : g0 ∈ fiveQubitCode.carrier := Subgroup.subset_closure (Set.mem_insert _ _)
    have hg1 : g1 ∈ fiveQubitCode.carrier := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hg2 : g2 ∈ fiveQubitCode.carrier := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    have hg3 : g3 ∈ fiveQubitCode.carrier := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    -- Define the enumeration function from exponent vectors to group elements
    let enumerate : (Fin 4 → ZMod 2) → PauliOp 5 := fun a =>
      (if a 0 = 0 then 1 else g0) *
      (if a 1 = 0 then 1 else g1) *
      (if a 2 = 0 then 1 else g2) *
      (if a 3 = 0 then 1 else g3)
    -- prove injectivity by native_decide
    have inj : Function.Injective enumerate := by
      native_decide
    -- prove enumerate a is in carrier for all a
    have enumerate_mem : ∀ a, enumerate a ∈ fiveQubitCode.carrier := by
      intro a
      simp only [enumerate]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (by split_ifs <;> simp [hg0]) (by split_ifs <;> simp [hg1]))
        (by split_ifs <;> simp [hg2])) (by split_ifs <;> simp [hg3])
    -- prove surjectivity: every element of the carrier is in the range of enumerate
    have surj : ∀ x ∈ fiveQubitCode.carrier, ∃ a, enumerate a = x := by
      intro x hx
      -- Define the range set
      let S : Set (PauliOp 5) := Set.range enumerate
      -- enumerate_add and enumerate_self_inv before they're needed
      have enumerate_add : ∀ a b : Fin 4 → ZMod 2, enumerate (a + b) = enumerate a * enumerate b := by native_decide
      have enumerate_self_inv : ∀ a : Fin 4 → ZMod 2, enumerate a = (enumerate a)⁻¹ := by native_decide
      -- Show S is a subgroup by proving closure properties
      let S_group : Subgroup (PauliOp 5) := {
        carrier := S
        one_mem' := ⟨0, by native_decide⟩
        mul_mem' := by
          intro x y ⟨a, ha⟩ ⟨b, hb⟩
          exact ⟨a + b, by rw [← ha, ← hb, enumerate_add]⟩
        inv_mem' := by
          intro x ⟨a, ha⟩
          exact ⟨a, by rw [← ha]; exact enumerate_self_inv a⟩
      }
      -- generators are in S
      have g0_in_S : g0 ∈ S := ⟨![1,0,0,0], by native_decide⟩
      have g1_in_S : g1 ∈ S := ⟨![0,1,0,0], by native_decide⟩
      have g2_in_S : g2 ∈ S := ⟨![0,0,1,0], by native_decide⟩
      have g3_in_S : g3 ∈ S := ⟨![0,0,0,1], by native_decide⟩
      -- carrier = Subgroup.closure {g0,g1,g2,g3} ⊆ S since S is a subgroup containing generators
      have carrier_le_S : fiveQubitCode.carrier ≤ S_group := by
        unfold fiveQubitCode
        rw [Subgroup.closure_le]
        intro x hx
        simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl | rfl | rfl | rfl)
        exacts [g0_in_S, g1_in_S, g2_in_S, g3_in_S]
      -- surjectivity: x ∈ S_group means x ∈ Set.range enumerate = S
      exact Set.mem_range.mp (carrier_le_S hx)
    -- Establish bijection: pick a canonical preimage for each element
    let pick : fiveQubitCode.carrier → (Fin 4 → ZMod 2) := fun x =>
      Classical.choose (surj x.val x.prop)
    have pick_spec : ∀ x : fiveQubitCode.carrier, enumerate (pick x) = x.val := fun x =>
      Classical.choose_spec (surj x.val x.prop)
    have pick_inj : Function.Injective pick := fun x y hxy =>
      Subtype.ext ((pick_spec x).symm.trans (hxy ▸ pick_spec y))
    have pick_surj : Function.Surjective pick := fun a =>
      ⟨⟨enumerate a, enumerate_mem a⟩, inj (pick_spec ⟨enumerate a, enumerate_mem a⟩)⟩
    have pick_bijective : Function.Bijective pick := ⟨pick_inj, pick_surj⟩
    have hcard : Fintype.card fiveQubitCode.carrier = Fintype.card (Fin 4 → ZMod 2) :=
      Fintype.card_congr (Equiv.ofBijective pick pick_bijective)
    rw [hcard]
    decide
  rw [StabGroup.numLogical]
  simp_all
  decide

theorem fiveQubitCode_distance : fiveQubitCode.distance = 3 := by sorry

/-- The five-qubit code is a *perfect* code: it saturates the quantum Hamming bound. -/
theorem fiveQubitCode_perfect :
    (∑ j ∈ Finset.range 2, Nat.choose 5 j * 3 ^ j) * 2 ^ fiveQubitCode.numLogical = 2 ^ 5 := by
  simp [fiveQubitCode_numLogical]; native_decide

/-! ### Shor's nine-qubit code `⟦9,1,3⟧` -/

/-- Shor's code as a CSS code: two `X`-type checks over blocks and six `Z`-type nearest-neighbour
checks. -/
def shorCode : StabGroup 9 :=
  cssCode
    (![ ![1,1,1,1,1,1,0,0,0], ![0,0,0,1,1,1,1,1,1] ] : Fin 2 → (Fin 9 → ZMod 2))
    (![ ![1,1,0,0,0,0,0,0,0], ![0,1,1,0,0,0,0,0,0],
        ![0,0,0,1,1,0,0,0,0], ![0,0,0,0,1,1,0,0,0],
        ![0,0,0,0,0,0,1,1,0], ![0,0,0,0,0,0,0,1,1] ] : Fin 6 → (Fin 9 → ZMod 2))
    (by decide)

@[simp] theorem shorCode_numPhysical : shorCode.numPhysical = 9 := rfl

theorem shorCode_numLogical : shorCode.numLogical = 1 := by sorry

theorem shorCode_distance : shorCode.distance = 3 := by sorry

/-! ### The Steane seven-qubit code `⟦7,1,3⟧` -/

/-- The `[7,4,3]` Hamming parity-check matrix (columns are `1..7` in binary). -/
def hammingCheck : Fin 3 → (Fin 7 → ZMod 2) :=
  ![ ![0,0,0,1,1,1,1], ![0,1,1,0,0,1,1], ![1,0,1,0,1,0,1] ]

/-- Steane's code: the CSS code of the self-dual `[7,4,3]` Hamming code with itself. -/
def steaneCode : StabGroup 7 := cssCode hammingCheck hammingCheck (by decide)

@[simp] theorem steaneCode_numPhysical : steaneCode.numPhysical = 7 := rfl

theorem steaneCode_numLogical : steaneCode.numLogical = 1 := by sorry

theorem steaneCode_distance : steaneCode.distance = 3 := by sorry

end PauliOp
end QuantumLib
