module
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-

TODO: Remove this file after the next mathlib bump

-/


variable {N M 𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [TopologicalSpace H]
variable [TopologicalSpace N] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
variable [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M]


variable {M' : Type*} [TopologicalSpace M']
variable (H) in
/-- Given a homeomorphism `f : M ≃ₜ M'`, endow `M'` with a `ChartedSpace` structure by pushing
forward the `ChartedSpace` structure from `M`. -/
@[implicit_reducible]
public noncomputable def Homeomorph.chartedSpace (f : M ≃ₜ M') : ChartedSpace H M' :=
  f.isLocalHomeomorph.chartedSpace f.surjective

variable (H) in
public lemma Homeomorph.chartedSpace_chart_eqOn (f : M ≃ₜ M') (x : M') :
    letI := f.chartedSpace H
    Set.EqOn (chartAt H x) (f.symm.transOpenPartialHomeomorph (chartAt H (f.symm x))) (chartAt H x).source := by
  intro y hy
  rw [Homeomorph.chartedSpace, IsLocalHomeomorph.chartedSpace, IsLocalHomeomorph.chartedSpaceOfRightInverse]
  simp [chartAt]
  congr 1
  · sorry -- stimmt
  · sorry -- stimmt


open OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
@[simp]
lemma toOpenPartialHomeomorph_symm_trans_self (e : X ≃ₜ Y) :
    e.toOpenPartialHomeomorph.symm.trans  e.toOpenPartialHomeomorph = .refl Y := by
  ext _ <;> simp

@[simp]
lemma toOpenPartialHomeomorph_trans_symm_self (e : X ≃ₜ Y) :
    e.toOpenPartialHomeomorph.trans  e.toOpenPartialHomeomorph.symm = .refl X := by
  ext _ <;> simp


namespace Homeomorph

lemma toOpenPartialHomeomorph_trans_localInverseAt (φ : X ≃ₜ Y) (m : X) :
    (φ.toOpenPartialHomeomorph.trans  (φ.isLocalHomeomorph.localInverseAt m)).EqOnSource
      <| .ofSet (φ ⁻¹' (φ.isLocalHomeomorph.localInverseAt m).source)
        <| by simpa using OpenPartialHomeomorph.open_source _ := by
  simpa [OpenPartialHomeomorph.EqOnSource, Set.EqOn, OpenPartialHomeomorph.open_source]
    using fun _ hx ↦ φ.bijective.injective <| IsLocalHomeomorph.apply_localInverseAt_of_mem _ hx

end Homeomorph


namespace Homeomorph

open IsManifold in public lemma chartedSpace_trans_mem_maximalAtlas (φ : M ≃ₜ N) :
    letI := φ.chartedSpace H
    ∀ e ∈ atlas H N, φ.toOpenPartialHomeomorph.trans e ∈ maximalAtlas I n M := fun e he ↦ by
  simp only [atlas, ChartedSpace.atlas, Set.mem_setOf_eq] at he
  rcases he with ⟨q, he⟩
  rw [← he, ← OpenPartialHomeomorph.trans_assoc]
  exact StructureGroupoid.mem_maximalAtlas_of_eqOnSource
    (Setoid.trans (OpenPartialHomeomorph.EqOnSource.trans'
      (φ.toOpenPartialHomeomorph_trans_localInverseAt _)
      (OpenPartialHomeomorph.eqOnSource_refl _)) (by rw [OpenPartialHomeomorph.ofSet_trans]))
    <| restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas _)
      <| by simpa using OpenPartialHomeomorph.open_source _



end Homeomorph

/--
The push-forward of a `ChartedSpace` along a homeomorphism `f : M ≃ₜ N` is a manifold, if `M`
is a manifold.
-/
@[implicit_reducible]
public def Homeomorph.isManifold [IsManifold I n M] (φ : M ≃ₜ N) :
  letI := φ.chartedSpace H;
  IsManifold I n N  where
    __ := φ.chartedSpace H
    compatible {e e'} he he' := by
      have : _ ∈ contDiffGroupoid n I := IsManifold.compatible_of_mem_maximalAtlas
        (φ.chartedSpace_trans_mem_maximalAtlas e he) (φ.chartedSpace_trans_mem_maximalAtlas e' he')
      convert this
      simp [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
        ← OpenPartialHomeomorph.trans_assoc φ.toOpenPartialHomeomorph.symm]
