/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Div
public import Physlib.Mathematics.Calculus.AdjFDeriv
/-!

# Localized function transforms

In this module we define a locality property for function transforms, `F : (X → U) → (Y → V)`.
The locality property `IsLocalizedFunctionTransform`, says that for every compact
set `K` in `Y` there exists a compact set `L` of `X`, such that if `φ` and `φ'` are equal on `L`,
then `F φ` and `F φ'` are equal on `K`.

-/

@[expose] public section
open InnerProductSpace MeasureTheory ContDiff

section

variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y]
  {Z} [NormedAddCommGroup Z]
  {U}
  {V}
  {W}

/-- Function transformation `F` is localizable if the values of the transformed function `F φ` on
some compact set `K` can depend only on the values of `φ` on some another compact set `L`. -/
def IsLocalizedFunctionTransform (F : (X → U) → (Y → V)) : Prop :=
  ∀ (K : Set Y) (_ : IsCompact K), ∃ L : Set X,
    IsCompact L ∧ ∀ (φ φ' : X → U), (∀ x ∈ L, φ x = φ' x) → ∀ x ∈ K, F φ x = F φ' x
end
namespace IsLocalizedFunctionTransform

section
variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y]
  {Z} [NormedAddCommGroup Z]
  {U}
  {V}
  {W}
lemma comp {F : (Y → V) → (Z → W)} {G : (X → U) → (Y → V)}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (F ∘ G) := by
  intro K cK
  obtain ⟨K', cK', h'⟩ := hF K cK
  obtain ⟨K'', cK'', h''⟩ := hG K' cK'
  use K''
  constructor
  · exact cK''
  · intro φ φ' hφ
    apply h' _ _ (fun _ hx' => h'' _ _ hφ _ hx')

lemma fun_comp {F : (Y → V) → (Z → W)} {G : (X → U) → (Y → V)}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (fun x => F (G x)) := by
  apply comp hF hG

@[simp]
lemma id : IsLocalizedFunctionTransform (id : (Y → V) → (Y → V)) := by
  intro K cK
  use K
  constructor
  · exact cK
  · intro φ φ' hφ x hx
    simp only [id_eq]
    rw [hφ x hx]

lemma neg {V} [NormedAddCommGroup V]
    {F : (X → U) → (Y → V)} (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ => - F φ) := by
  intro K cK
  obtain ⟨L,cL,h⟩ := hF K cK
  exact ⟨L,cL,by intro _ _ _ _ _; dsimp; congr 1; apply h <;> simp_all⟩

lemma add {V} [NormedAddCommGroup V] {F G : (X → U) → (Y → V)}
    (hF : IsLocalizedFunctionTransform F) (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (fun φ => F φ + G φ) := by
  intro K cK
  obtain ⟨L,cL,h⟩ := hF K cK
  obtain ⟨L',cL',h'⟩ := hG K cK
  use L ∪ L'
  constructor
  · exact cL.union cL'
  · intro φ φ' hφ
    have hL : ∀ x ∈ L, φ x = φ' x := by
      intro x hx; apply hφ; simp_all
    have hL' : ∀ x ∈ L', φ x = φ' x := by
      intro x hx; apply hφ; simp_all
    simp +contextual (disch:=assumption) [h φ φ', h' φ φ']
end
section
variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {U}
  {V}

lemma mul_left {F : (X → ℝ) → (X → ℝ)} {ψ : X → ℝ} (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ x => ψ x * F φ x) := by
  intro K cK
  obtain ⟨L, cL, h⟩ := hF K cK
  exact ⟨L, cL, fun φ φ' hφ x hx => by dsimp only; rw [h φ φ' hφ x hx]⟩

lemma mul_right {F : (X → ℝ) → (X → ℝ)} {ψ : X → ℝ} (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ x => F φ x * ψ x) := by
  intro K cK
  obtain ⟨L, cL, h⟩ := hF K cK
  exact ⟨L, cL, fun φ φ' hφ x hx => by dsimp only; rw [h φ φ' hφ x hx]⟩

lemma smul_left [NormedAddCommGroup V] [NormedSpace ℝ V] {F : (X → U) → (X → V)} {ψ : X → ℝ}
    (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ x => ψ x • F φ x) := by
  intro K cK
  obtain ⟨L, cL, h⟩ := hF K cK
  exact ⟨L, cL, fun φ φ' hφ x hx => by dsimp only; rw [h φ φ' hφ x hx]⟩

lemma div {d} : IsLocalizedFunctionTransform fun (φ : Space d → EuclideanSpace ℝ (Fin d)) x =>
    Space.div φ x := by
  intro K cK
  use (Metric.cthickening 1 K)
  constructor
  · exact IsCompact.cthickening cK
  · intro φ φ' hφ
    have h : ∀ (i : Fin d), ∀ x ∈ K,
        (fun x => (φ x) i) =ᶠ[nhds x] fun x => (φ' x) i := by
      intro i x hx
      apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
      · apply Metric.isOpen_thickening.mem_nhds
        exact Metric.self_subset_thickening one_pos K hx
      · intro y hy
        dsimp only
        rw [hφ y (Metric.thickening_subset_cthickening 1 K hy)]
    intro x hx; dsimp;
    simp [Space.div,Space.deriv]
    congr; funext i; congr 1
    exact Filter.EventuallyEq.fderiv_eq (h _ _ hx)

lemma div_comp_repr {d} : IsLocalizedFunctionTransform fun (φ : Space d → Space d) x =>
    Space.div (Space.basis.repr ∘ φ) x := by
  intro K cK
  use (Metric.cthickening 1 K)
  constructor
  · exact IsCompact.cthickening cK
  · intro φ φ' hφ
    have h : ∀ (i : Fin d), ∀ x ∈ K,
        (fun x => (φ x) i) =ᶠ[nhds x] fun x => (φ' x) i := by
      intro i x hx
      apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
      · apply Metric.isOpen_thickening.mem_nhds
        exact Metric.self_subset_thickening one_pos K hx
      · intro y hy
        dsimp only
        rw [hφ y (Metric.thickening_subset_cthickening 1 K hy)]
    intro x hx; dsimp;
    simp [Space.div,Space.deriv]
    congr; funext i; congr 1
    exact Filter.EventuallyEq.fderiv_eq (h _ _ hx)

lemma grad : IsLocalizedFunctionTransform fun (ψ : Space d → ℝ) x => Space.grad ψ x := by
  intro K cK
  use (Metric.cthickening 1 K)
  constructor
  · exact IsCompact.cthickening cK
  · intro φ φ' hφ x hx
    dsimp
    simp [Space.grad_eq_sum, Space.deriv]
    congr
    funext i
    congr 2
    have h : φ =ᶠ[nhds x] φ' := by
      apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
      · apply Metric.isOpen_thickening.mem_nhds
        exact Metric.self_subset_thickening one_pos K hx
      · intro y hy
        exact hφ y (Metric.thickening_subset_cthickening 1 K hy)
    exact Filter.EventuallyEq.fderiv_eq h

lemma gradient : IsLocalizedFunctionTransform fun (ψ : Space d → ℝ) x => gradient ψ x := by
  intro K cK
  use (Metric.cthickening 1 K)
  constructor
  · exact IsCompact.cthickening cK
  · intro φ φ' hφ x hx
    dsimp
    simp [Space.gradient_eq_sum,Space.deriv]
    congr
    funext i
    congr 2
    have h : φ =ᶠ[nhds x] φ' := by
      apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
      · apply Metric.isOpen_thickening.mem_nhds
        exact Metric.self_subset_thickening one_pos K hx
      · intro y hy
        exact hφ y (Metric.thickening_subset_cthickening 1 K hy)
    exact Filter.EventuallyEq.fderiv_eq h

lemma clm_apply [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : X → (U →L[ℝ] V)) : IsLocalizedFunctionTransform fun φ x => (f x) (φ x) := by
  intro K cK
  exact ⟨K, cK, by intro _ _ hφ _ _; simp_all⟩

lemma deriv [NormedAddCommGroup U] [NormedSpace ℝ U] :
    IsLocalizedFunctionTransform (fun φ : ℝ → U => deriv φ) := by
  intro K cK
  use (Metric.cthickening 1 K)
  constructor
  · exact IsCompact.cthickening cK
  · intro φ φ' hφ x hx
    dsimp
    have h : φ =ᶠ[nhds x] φ' := by
      apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
      · apply Metric.isOpen_thickening.mem_nhds
        exact Metric.self_subset_thickening one_pos K hx
      · intro y hy
        exact hφ y (Metric.thickening_subset_cthickening 1 K hy)
    exact h.deriv_eq

lemma fderiv [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedSpace ℝ X] [ProperSpace X] {dx : X} :
    IsLocalizedFunctionTransform fun (φ : X → U) x => (fderiv ℝ φ x) dx := by
  intro K cK
  use (Metric.cthickening 1 K)
  constructor
  · exact IsCompact.cthickening cK
  · intro φ φ' hφ x hx
    dsimp; congr 1
    have h : φ =ᶠ[nhds x] φ' := by
      apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
      · apply Metric.isOpen_thickening.mem_nhds
        exact Metric.self_subset_thickening one_pos K hx
      · intro y hy
        exact hφ y (Metric.thickening_subset_cthickening 1 K hy)
    rw [Filter.EventuallyEq.fderiv_eq h]

lemma fst {F : (X → U) → X → W × V} (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ x => (F φ x).1) := by
  intro K cK
  obtain ⟨L, cL, h⟩ := hF K cK
  exact ⟨L, cL, fun φ φ' hφ x hx => by dsimp only; rw [h φ φ' hφ x hx]⟩

lemma snd {F : (X → U) → X → W × V} (hF : IsLocalizedFunctionTransform F) :
    IsLocalizedFunctionTransform (fun φ x => (F φ x).2) := by
  intro K cK
  obtain ⟨L, cL, h⟩ := hF K cK
  exact ⟨L, cL, fun φ φ' hφ x hx => by dsimp only; rw [h φ φ' hφ x hx]⟩

lemma prod {F : (X → U) → X → W}
    {G : (X → U) → X → V} (hF : IsLocalizedFunctionTransform F)
    (hG : IsLocalizedFunctionTransform G) :
    IsLocalizedFunctionTransform (fun φ x => (F φ x, G φ x)) := by
  intro K cK
  obtain ⟨A,cA,hF⟩ := hF K cK
  obtain ⟨B,cB,hG⟩ := hG K cK
  use A ∪ B
  constructor
  · exact cA.union cB
  · intro φ φ' h x hx; dsimp
    rw[hF,hG] <;> simp_all

omit [MeasureSpace Y] in
lemma adjFDeriv {dy} [NormedSpace ℝ X] [ProperSpace X]
    [InnerProductSpace' ℝ X] [InnerProductSpace' ℝ Y] :
    IsLocalizedFunctionTransform fun (φ : X → Y) x => adjFDeriv ℝ φ x dy := by
  intro K cK
  use (Metric.cthickening 1 K)
  constructor
  · exact IsCompact.cthickening cK
  · intro φ φ' hφ x hx
    unfold _root_.adjFDeriv
    simp only
    congr 1
    simp only [DFunLike.coe_fn_eq]
    have h : φ =ᶠ[nhds x] φ' := by
      apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
      · apply Metric.isOpen_thickening.mem_nhds
        exact Metric.self_subset_thickening one_pos K hx
      · intro y hy
        exact hφ y (Metric.thickening_subset_cthickening 1 K hy)
    exact Filter.EventuallyEq.fderiv_eq h

end
end IsLocalizedFunctionTransform
