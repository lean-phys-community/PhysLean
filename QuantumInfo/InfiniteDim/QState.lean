--Copyright 2024: https://github.com/dupuisf/LFTCM2024TraceClass
-- import Mathlib
-- -- import QuantumInfo.InfiniteDim.TraceClass

-- variable (H : Type*)
-- variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- namespace Quantum

-- local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

-- open InnerProduct

-- /-- Ket in a Hilbert space H, defined as a vector of unit norm. -/
-- structure Ket :=
--   vec : H
--   normalized : ‖vec‖=1

-- /-- An operator on a Hilbert space H is a mixed state iff it's a PSD operator with trace 1.-/
-- structure IsMixedState (op : H →L[ℂ] H) : Prop :=
--   /-- The operator of a mixed state is Hermitian -/
--   herm : IsSelfAdjoint op
--   /-- The operator of a mixed state is Positive Semidefinite -/
--   posSemiDef : ∀ (x : H), 0 ≤ ⟪x, op x⟫.re
--   /-- The operator is traceclass. -/
--   traceClass : IsTraceClass op
--   /-- The trace of a mixed state is 1. -/
--   traceOne : TraceClass.trace op = 1

-- /-- Mixed state in a Hilbert space H, defined as a PSD operator with trace 1. -/
-- structure MState :=
--   /-- The underlying operator of a state -/
--   op : H →L[ℂ] H
--   /-- The operator is a valid mixed state. -/
--   prop : IsMixedState H op

-- /-- The stateSpace of a Hilbert space H is the set of all mixed states in H. -/
-- def stateSpace : Set (H →L[ℂ] H) := { ρ | IsMixedState H ρ }

-- set_option pp.analyze true

-- theorem stateSpace_convex : Convex ℝ (stateSpace H) := by
--   rw [convex_iff_pointwise_add_subset]
--   intros x y xpos ypos xy1 z hz
--   rw [stateSpace] at hz ⊢
--   rw [Set.mem_setOf_eq]
--   obtain ⟨x₁', hx₁', y₁', hy₁', hρ₁ρ₂⟩ := Set.mem_add.1 hz
--   obtain ⟨ρ₁, hρ₁, dx₁'⟩ := Set.mem_smul_set.1 hx₁'
--   obtain ⟨ρ₂, hρ₂, dy₁'⟩ := Set.mem_smul_set.1 hy₁'
--   clear hz hx₁' hy₁'
--   subst dx₁'
--   subst dy₁'
--   subst z
--   rw [Set.mem_setOf_eq] at hρ₁ hρ₂
--   constructor
--   · have h₁ := hρ₁.1
--     have h₂ := hρ₂.1
--     apply IsSelfAdjoint.add
--     <;> apply IsSelfAdjoint.smul (by rfl) ‹_›
--   · intro v
--     simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
--       Pi.smul_apply, inner_add_right, Complex.add_re]
--     change 0 ≤ (⟪v, (x:ℂ) • ρ₁ v⟫_ℂ).re + (⟪v, (y:ℂ) • ρ₂ v⟫_ℂ).re
--     simp only [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
--       zero_mul, sub_zero, ge_iff_le]
--     have h₁ := hρ₁.2 v
--     have h₂ := hρ₂.2 v
--     positivity
--   ·
--   -- · obtain ⟨ι, _⟩ := hρ₁.3
--   --   apply TraceClass.mk_of_exists
--   --   sorry
--     sorry
--   · sorry
module

