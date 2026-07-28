/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.DirectSum.Module
public import Physlib.Mathematics.SymmetricAlgebra.SymmetricMap
-- `TensorAlgebra.symRingCon` is `@[no_expose]`, so a plain `public import` does not expose its
-- body and `symRingCon = ringConGen (SymRel ..)` is not available. This private `import all`
-- supplies it.
import all Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Symmetric monomials and the lift out of the symmetric algebra

## i. Overview

The symmetric algebra `SymmetricAlgebra R M` is the tensor algebra quotiented by the congruence
forcing generators to commute. This file supplies the multilinear constructions mapping into and out
of it.

`ιMulti` maps in. It sends a tuple `v : Fin n → M` to the product of the corresponding generators.
Its symmetry is permutation invariance of a finite product in a commutative algebra.

`liftSymmetric` maps out. It takes a family of symmetric multilinear maps, one in each degree, and
assembles them into a single linear map on the symmetric algebra, sending a degree-`n` monomial to
the value prescribed in degree `n`. The target `N` need only be an `R`-module: the assembled map is
linear but in general not multiplicative, so the family may prescribe unrelated behaviour in each
degree.

The construction passes through tensor powers and their direct sum, then descends from the tensor
algebra through the symmetric congruence. Symmetry supplies the contextual permutation invariance
required for this descent.

## ii. Key results

- `SymmetricAlgebra.ιMulti` : the symmetric multilinear map sending a tuple to the product of the
  corresponding generators.
- `SymmetricAlgebra.liftSymmetric` : the assembly of a degreewise family of symmetric multilinear
  maps into a linear map on the symmetric algebra, itself linear in the family.
- `SymmetricAlgebra.liftSymmetric_apply_ιMulti` : the defining computation on monomials.
- `SymmetricAlgebra.lhom_ext` : a linear map out of the symmetric algebra is determined by its
  values on monomials.
- `SymmetricAlgebra.liftSymmetricEquiv` : the construction packaged as a linear equivalence.

The supporting computation and composition lemmas are documented at their declarations.

## iii. Table of contents

- A. Products of symmetric algebra generators
  - A.1. Definition
  - A.2. Computation lemmas
- B. The lift out of the symmetric algebra
  - B.1. A pure `Fin`-coordinate lemma
  - B.2. Internal helpers (family-independent)
  - B.3. Internal helpers (family-dependent)
  - B.4. Extensionality
  - B.5. The bundled lift and its API

## iv. References

- Bergman, Tensor, Exterior, and Symmetric Algebras.
-/

namespace SymmetricAlgebra

/-!
## A. Products of symmetric algebra generators

Stated throughout via the public generator `SymmetricAlgebra.ι` and commutative multiplication.
-/

@[expose] public section

universe u v

variable (R : Type u) [CommSemiring R]
variable (M : Type v) [AddCommMonoid M] [Module R M]

/-! ### A.1. Definition -/

/-- The canonical symmetric multilinear map sending a finite tuple to the product of the
corresponding generators in the symmetric algebra. -/
def ιMulti (n : ℕ) : SymmetricMap R M (SymmetricAlgebra R M) (Fin n) :=
  (mkPiAlgebra R (Fin n) (SymmetricAlgebra R M)).compLinearMap (ι R M)

/-! ### A.2. Computation lemmas -/

/-- Applying `ιMulti` to a tuple gives the product of the corresponding symmetric-algebra
generators. -/
lemma ιMulti_apply {n : ℕ} (v : Fin n → M) :
    ιMulti R M n v = ∏ i, ι R M (v i) :=
  rfl

/-- The degree-zero symmetric monomial is the multiplicative identity. -/
@[simp]
lemma ιMulti_zero_apply (v : Fin 0 → M) : ιMulti R M 0 v = 1 := by
  rw [ιMulti_apply]
  exact Fin.prod_univ_zero _

/-- A positive-degree symmetric monomial is its first generator multiplied by the product of the
remaining generators. -/
@[simp]
lemma ιMulti_succ_apply {n : ℕ} (v : Fin n.succ → M) :
    ιMulti R M n.succ v = ι R M (v 0) * ιMulti R M n (Matrix.vecTail v) := by
  rw [ιMulti_apply, Fin.prod_univ_succ, ιMulti_apply]
  rfl

end

/-!
## B. The lift out of the symmetric algebra

A degreewise family of symmetric multilinear maps is assembled into a single linear map on the
symmetric algebra, along the pipeline

    ∀ n, SymmetricMap R M N (Fin n)
      → ∀ n, (n-fold tensor power of M) →ₗ[R] N      (PiTensorProduct.lift)
      → (⨁ n, n-fold tensor power of M) →ₗ[R] N      (DirectSum.toModule)
      → TensorAlgebra R M →ₗ[R] N                    (TensorAlgebra.equivDirectSum)
      → SymmetricAlgebra R M →ₗ[R] N                 (the descent)

The first three steps are assembled as the internal `Lhat`; the last is carried out by the internal
`descend`, once `Lhat` is shown constant on the symmetric congruence.
-/

public section

universe u v w w'

/-!
### B.1. A pure `Fin`-coordinate lemma
-/

section FinCoordinates

variable {M : Type v}

/-- Swapping the two middle entries of `Fin.append (Fin.append s ![x, y]) t` is exactly the adjacent
transposition of positions `m` and `m + 1`. -/
private lemma append_pair_swap (x y : M) (m k : ℕ) (s : Fin m → M) (t : Fin k → M) :
    Fin.append (Fin.append s ![y, x]) t
      = fun i => Fin.append (Fin.append s ![x, y]) t
          (Equiv.swap (Fin.castAdd k (Fin.natAdd m (0 : Fin 2)))
            (Fin.castAdd k (Fin.natAdd m (1 : Fin 2))) i) := by
  set U : Fin (m + 2 + k) → M := Fin.append (Fin.append s ![x, y]) t with hU
  set V : Fin (m + 2 + k) → M := Fin.append (Fin.append s ![y, x]) t with hV
  set a₀ : Fin (m + 2 + k) := Fin.castAdd k (Fin.natAdd m (0 : Fin 2)) with ha₀
  set b₀ : Fin (m + 2 + k) := Fin.castAdd k (Fin.natAdd m (1 : Fin 2)) with hb₀
  set e : Equiv.Perm (Fin (m + 2 + k)) := Equiv.swap a₀ b₀ with he
  show V = fun i => U (e i)
  funext i
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun p => ?_) (fun q => ?_) j
    · have hne1 : (Fin.castAdd k (Fin.castAdd 2 p)) ≠ a₀ := by
        rw [ha₀]; simp [Fin.ext_iff]; omega
      have hne2 : (Fin.castAdd k (Fin.castAdd 2 p)) ≠ b₀ := by
        rw [hb₀]; simp [Fin.ext_iff]; omega
      simp only [hU, hV, he, Equiv.swap_apply_of_ne_of_ne hne1 hne2, Fin.append_left]
    · by_cases hq0 : q = 0
      · subst hq0
        have hsw : e (Fin.castAdd k (Fin.natAdd m (0 : Fin 2)))
            = Fin.castAdd k (Fin.natAdd m (1 : Fin 2)) := by
          rw [he, ← ha₀, Equiv.swap_apply_left, ← hb₀]
        rw [hsw]
        simp [hU, hV, Fin.append_left, Fin.append_right]
      · have hq1 : q = 1 := by omega
        subst hq1
        have hsw : e (Fin.castAdd k (Fin.natAdd m (1 : Fin 2)))
            = Fin.castAdd k (Fin.natAdd m (0 : Fin 2)) := by
          rw [he, ← hb₀, Equiv.swap_apply_right, ← ha₀]
        rw [hsw]
        simp [hU, hV, Fin.append_left, Fin.append_right]
  · have hne1 : (Fin.natAdd (m + 2) l) ≠ a₀ := by
      rw [ha₀]; simp [Fin.ext_iff]; omega
    have hne2 : (Fin.natAdd (m + 2) l) ≠ b₀ := by
      rw [hb₀]; simp [Fin.ext_iff]; omega
    simp only [hU, hV, he, Equiv.swap_apply_of_ne_of_ne hne1 hne2, Fin.append_right]

end FinCoordinates

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

open TensorAlgebra
open scoped DirectSum TensorProduct Pointwise

/-!
### B.2. Internal helpers (family-independent)

The parts of the construction not mentioning the degreewise family: the quotient descent, the
identification of a symmetric monomial with the image of a tensor-algebra monomial, and the two
facts about tensor-algebra monomials - they multiply by concatenation, and they span.

The carrier of `SymmetricAlgebra R M` is definitionally the quotient of the additive congruence
underlying `symRingCon`, so the `AddCon.lift` in `descend` lands in it directly, with no transport.
-/

/-- A linear map out of the tensor algebra that is constant on the symmetric congruence descends to
the symmetric algebra. Module-target analogue of `SymmetricAlgebra.lift`. -/
private noncomputable def descend
    (L : TensorAlgebra R M →ₗ[R] N)
    (h : ∀ x y, symRingCon R M x y → L x = L y) :
    SymmetricAlgebra R M →ₗ[R] N where
  toFun := (symRingCon R M).toAddCon.lift L.toAddMonoidHom (fun ⦃x y⦄ hxy => h x y hxy)
  map_add' := map_add _
  map_smul' := fun r x => by
    obtain ⟨a, rfl⟩ := SymmetricAlgebra.algHom_surjective R M x
    rw [RingHom.id_apply, ← map_smul (SymmetricAlgebra.algHom R M) r a]
    exact map_smul L r a

/-- The descended map computes on the image of a tensor-algebra element by evaluating the original
map there. -/
@[simp]
private lemma descend_algHom
    (L : TensorAlgebra R M →ₗ[R] N)
    (h : ∀ x y, symRingCon R M x y → L x = L y)
    (a : TensorAlgebra R M) :
    descend L h (SymmetricAlgebra.algHom R M a) = L a :=
  rfl

/-- The symmetric monomial `ιMulti` is the `algHom`-image of the tensor-algebra monomial `tprod`. -/
private lemma ιMulti_eq_algHom_tprod (n : ℕ) (v : Fin n → M) :
    ιMulti R M n v = SymmetricAlgebra.algHom R M (TensorAlgebra.tprod R M n v) := by
  rw [ιMulti_apply, TensorAlgebra.tprod_apply, map_list_prod, List.map_ofFn]
  simp [SymmetricAlgebra.ι, List.prod_ofFn]

/-- A degree-2 tensor-algebra monomial is the product of its two generators. -/
private lemma tprod_two (x y : M) :
    TensorAlgebra.tprod R M 2 ![x, y] = TensorAlgebra.ι R x * TensorAlgebra.ι R y := by
  rw [TensorAlgebra.tprod_apply]
  simp [List.ofFn_succ]

/-- Concatenation of tensor-algebra monomials. -/
private lemma tprod_mul (m k : ℕ) (s : Fin m → M) (t : Fin k → M) :
    TensorAlgebra.tprod R M m s * TensorAlgebra.tprod R M k t
      = TensorAlgebra.tprod R M (m + k) (Fin.append s t) := by
  have hfun : (fun i => TensorAlgebra.ι R (Fin.append s t i))
      = Fin.append (fun i => TensorAlgebra.ι R (s i)) (fun i => TensorAlgebra.ι R (t i)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  rw [TensorAlgebra.tprod_apply, TensorAlgebra.tprod_apply, TensorAlgebra.tprod_apply,
    ← List.prod_append, ← List.ofFn_fin_append, hfun]

/-- The tensor-algebra monomials span the whole tensor algebra as a module. -/
private lemma tprod_span :
    Submodule.span R
      (Set.range (fun p : (n : ℕ) × (Fin n → M) => TensorAlgebra.tprod R M p.1 p.2)) = ⊤ := by
  set S : Set (TensorAlgebra R M) :=
    Set.range (fun p : (n : ℕ) × (Fin n → M) => TensorAlgebra.tprod R M p.1 p.2)
  have hSmul : S * S ⊆ S := by
    rintro _ ⟨_, ⟨⟨m, s⟩, rfl⟩, _, ⟨⟨k, t⟩, rfl⟩, rfl⟩
    exact ⟨⟨m + k, Fin.append s t⟩, (tprod_mul m k s t).symm⟩
  rw [eq_top_iff]
  intro z hz
  clear hz
  induction z using TensorAlgebra.induction with
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨0, ![]⟩, by simp [TensorAlgebra.tprod_apply]⟩)
  | ι v =>
      exact Submodule.subset_span ⟨⟨1, ![v]⟩, by simp [TensorAlgebra.tprod_apply, List.ofFn_succ]⟩
  | mul u w hu hw =>
      have h := Submodule.mul_mem_mul hu hw
      rw [Submodule.span_mul_span] at h
      exact Submodule.span_mono hSmul h
  | add u w hu hw => exact Submodule.add_mem _ hu hw

/-!
### B.3. Internal helpers (family-dependent)

`Lhat` evaluates the degreewise family on tensor words. Symmetry of the family gives permutation
invariance on monomials, and a span argument extends the generator swap to arbitrary surrounding
factors `a * _ * b`. Passing to `Qcon`, the largest ring congruence on which `Lhat` is constant,
then turns that invariance into compatibility with `symRingCon`.
-/

section Construction

variable (f : ∀ n, SymmetricMap R M N (Fin n))

/-- The linear map on the tensor algebra assembled from the degreewise symmetric maps. -/
private noncomputable def Lhat : TensorAlgebra R M →ₗ[R] N :=
  DirectSum.toModule R ℕ N (fun n => PiTensorProduct.lift (f n).toMultilinearMap) ∘ₗ
    (TensorAlgebra.equivDirectSum (R := R) (M := M)).toLinearMap

/-- `Lhat` sends a tensor-algebra monomial to the value prescribed by the rule of its degree. -/
private lemma Lhat_tprod (n : ℕ) (v : Fin n → M) :
    Lhat f (TensorAlgebra.tprod R M n v) = f n v := by
  rw [Lhat, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    TensorAlgebra.equivDirectSum_apply, TensorAlgebra.toDirectSum_tensorPower_tprod,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof, PiTensorProduct.lift.tprod]
  rfl

/-- Permuting the factors of a tensor-algebra monomial leaves `Lhat` unchanged, because each `f n`
is symmetric. -/
private lemma Lhat_tprod_perm (n : ℕ) (v : Fin n → M) (e : Equiv.Perm (Fin n)) :
    Lhat f (TensorAlgebra.tprod R M n (fun i => v (e i)))
      = Lhat f (TensorAlgebra.tprod R M n v) := by
  rw [Lhat_tprod, Lhat_tprod]
  exact (f n).map_perm e v

/-- The largest ring congruence on which `Lhat f` is constant: it relates `u` and `w` when
`Lhat f (a * u * b) = Lhat f (a * w * b)` for all `a` and `b`. -/
private def Qcon : RingCon (TensorAlgebra R M) where
  r u w := ∀ a b, Lhat f (a * u * b) = Lhat f (a * w * b)
  iseqv :=
    { refl := fun _ _ _ => rfl
      symm := fun h a b => (h a b).symm
      trans := fun h1 h2 a b => (h1 a b).trans (h2 a b) }
  add' := fun h1 h2 a b => by
    simp only [mul_add, add_mul, map_add]; rw [h1 a b, h2 a b]
  mul' := fun {w x y z} h1 h2 a b => by
    have k1 := h1 a (y * b)
    have k2 := h2 (a * x) b
    simp only [← mul_assoc] at k1 k2 ⊢
    rw [k1]; exact k2

/-- The generator swap with monomials as the surrounding factors: the three factors fold into one
`tprod`, and the swap becomes the transposition of two adjacent positions. -/
private lemma Lhat_contextSwap_monomial (x y : M) (m k : ℕ) (s : Fin m → M) (t : Fin k → M) :
    Lhat f (TensorAlgebra.tprod R M m s * (TensorAlgebra.ι R x * TensorAlgebra.ι R y)
        * TensorAlgebra.tprod R M k t)
      = Lhat f (TensorAlgebra.tprod R M m s * (TensorAlgebra.ι R y * TensorAlgebra.ι R x)
        * TensorAlgebra.tprod R M k t) := by
  rw [← tprod_two, ← tprod_two, tprod_mul, tprod_mul, tprod_mul, tprod_mul,
    append_pair_swap x y m k s t]
  exact (Lhat_tprod_perm f (m + 2 + k) (Fin.append (Fin.append s ![x, y]) t) _).symm

/-- The generator swap with arbitrary factors `a` and `b` on either side, obtained from
`Lhat_contextSwap_monomial` by induction over the spanning set of monomials in `a` and `b` at
once. -/
private lemma Lhat_contextSwap (x y : M) (a b : TensorAlgebra R M) :
    Lhat f (a * (TensorAlgebra.ι R x * TensorAlgebra.ι R y) * b)
      = Lhat f (a * (TensorAlgebra.ι R y * TensorAlgebra.ι R x) * b) := by
  classical
  have hspan : Submodule.span R
      (Set.range (fun p : (n : ℕ) × (Fin n → M) => TensorAlgebra.tprod R M p.1 p.2)) = ⊤ :=
    tprod_span
  refine Submodule.span_induction₂
    (p := fun a b _ _ => Lhat f (a * (TensorAlgebra.ι R x * TensorAlgebra.ι R y) * b)
      = Lhat f (a * (TensorAlgebra.ι R y * TensorAlgebra.ι R x) * b))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hspan ▸ Submodule.mem_top) (hspan ▸ Submodule.mem_top)
  · rintro _ _ ⟨⟨m, s⟩, rfl⟩ ⟨⟨k, t⟩, rfl⟩
    exact Lhat_contextSwap_monomial f x y m k s t
  · intro c _; simp
  · intro c _; simp
  · intro c d g _ _ _ hc hd; simp only [add_mul, map_add, hc, hd]
  · intro c d g _ _ _ hd hg; simp only [mul_add, map_add, hd, hg]
  · intro r c d _ _ hc; simp only [smul_mul_assoc, map_smul, hc]
  · intro r c d _ _ hd; simp only [mul_smul_comm, map_smul, hd]

/-- `Lhat f` is constant on the whole symmetric congruence, and so descends. -/
private lemma well_defined : ∀ u w, symRingCon R M u w → Lhat f u = Lhat f w := by
  have hle : symRingCon R M ≤ Qcon f := by
    rw [show symRingCon R M = ringConGen (SymRel R M) from rfl]
    refine RingCon.ringConGen_le.2 ?_
    intro u v h
    cases h with
    | mul_comm x y => exact fun a b => Lhat_contextSwap f x y a b
  intro u w h
  simpa using hle h 1 1

/-- The descended map for a fixed family; `liftSymmetric` bundles it linearly in the family. -/
private noncomputable def liftSymmetricAux : SymmetricAlgebra R M →ₗ[R] N :=
  descend (Lhat f) (well_defined f)

/-- For a fixed family, the descended map sends a symmetric monomial to the prescribed degreewise
value. -/
private lemma liftSymmetricAux_ιMulti (n : ℕ) (v : Fin n → M) :
    liftSymmetricAux f (ιMulti R M n v) = f n v := by
  rw [liftSymmetricAux, ιMulti_eq_algHom_tprod, descend_algHom, Lhat_tprod]

end Construction

/-!
### B.4. Extensionality

Since `algHom` is surjective and the tensor-algebra monomials span, a linear map out of the
symmetric algebra is determined by its values on symmetric monomials.
-/

/-- Two linear maps out of the symmetric algebra agreeing on every symmetric monomial are equal. -/
@[ext]
lemma lhom_ext ⦃g h : SymmetricAlgebra R M →ₗ[R] N⦄
    (H : ∀ (n : ℕ) (v : Fin n → M), g (ιMulti R M n v) = h (ιMulti R M n v)) :
    g = h := by
  have key : g.comp (SymmetricAlgebra.algHom R M).toLinearMap
      = h.comp (SymmetricAlgebra.algHom R M).toLinearMap := by
    refine LinearMap.ext_on_range tprod_span ?_
    rintro ⟨n, v⟩
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← ιMulti_eq_algHom_tprod]
    exact H n v
  ext x
  obtain ⟨a, rfl⟩ := SymmetricAlgebra.algHom_surjective R M x
  simpa using LinearMap.congr_fun key a

/-!
### B.5. The bundled lift and its API

`liftSymmetric` bundles the construction of section B.3 as a map linear in the degreewise family;
both linearity obligations reduce through `lhom_ext` to the computation on monomials. The remaining
results are the computation rule, the two composition laws, the identity case
`liftSymmetric_ιMulti`, and the packaging as a linear equivalence.
-/

/-- Assemble a degreewise family of symmetric multilinear maps into a linear map on the symmetric
algebra, linearly in the family. -/
noncomputable def liftSymmetric :
    (∀ n, SymmetricMap R M N (Fin n)) →ₗ[R] SymmetricAlgebra R M →ₗ[R] N where
  toFun f := liftSymmetricAux f
  map_add' f g := by
    refine lhom_ext fun n v => ?_
    simp only [liftSymmetricAux_ιMulti, LinearMap.add_apply, Pi.add_apply, SymmetricMap.add_coe]
  map_smul' c f := by
    refine lhom_ext fun n v => ?_
    simp only [liftSymmetricAux_ιMulti, RingHom.id_apply, LinearMap.smul_apply, Pi.smul_apply,
      SymmetricMap.smul_coe]

/-- `liftSymmetric` sends a symmetric monomial to the prescribed degreewise value. -/
@[simp]
lemma liftSymmetric_apply_ιMulti (f : ∀ n, SymmetricMap R M N (Fin n))
    {n : ℕ} (v : Fin n → M) :
    liftSymmetric f (ιMulti R M n v) = f n v :=
  liftSymmetricAux_ιMulti f n v

/-- Postcomposing `ιMulti` with the lift recovers the original degreewise map. -/
@[simp]
lemma liftSymmetric_comp_ιMulti (f : ∀ n, SymmetricMap R M N (Fin n)) (n : ℕ) :
    (liftSymmetric f).compSymmetricMap (ιMulti R M n) = f n := by
  ext v
  rw [LinearMap.compSymmetricMap_apply, liftSymmetric_apply_ιMulti]

/-- Lifting the canonical family of symmetric monomials yields the identity. -/
@[simp]
lemma liftSymmetric_ιMulti :
    liftSymmetric (ιMulti R M)
      = (LinearMap.id : SymmetricAlgebra R M →ₗ[R] SymmetricAlgebra R M) := by
  refine lhom_ext fun n v => ?_
  simp only [liftSymmetric_apply_ιMulti, LinearMap.id_coe, id_eq]

variable {N' : Type w'} [AddCommMonoid N'] [Module R N']

/-- Naturality: the lift of a postcomposed family is the postcomposition of the lift. -/
@[simp]
lemma liftSymmetric_comp (g : N →ₗ[R] N') (f : ∀ n, SymmetricMap R M N (Fin n)) :
    liftSymmetric (fun n => g.compSymmetricMap (f n)) = g ∘ₗ liftSymmetric f := by
  refine lhom_ext fun n v => ?_
  simp only [LinearMap.comp_apply, liftSymmetric_apply_ιMulti, LinearMap.compSymmetricMap_apply]

/-- `liftSymmetric` as a linear equivalence between degreewise symmetric families and linear maps
out of the symmetric algebra. -/
noncomputable def liftSymmetricEquiv :
    (∀ n, SymmetricMap R M N (Fin n)) ≃ₗ[R] (SymmetricAlgebra R M →ₗ[R] N) :=
  { liftSymmetric with
    invFun := fun F n => F.compSymmetricMap (ιMulti R M n)
    left_inv := fun f => by
      funext n
      exact liftSymmetric_comp_ιMulti f n
    right_inv := fun F => by
      refine lhom_ext fun n v => ?_
      show liftSymmetric (fun n => F.compSymmetricMap (ιMulti R M n)) (ιMulti R M n v)
        = F (ιMulti R M n v)
      simp only [liftSymmetric_apply_ιMulti, LinearMap.compSymmetricMap_apply] }

end

end SymmetricAlgebra
