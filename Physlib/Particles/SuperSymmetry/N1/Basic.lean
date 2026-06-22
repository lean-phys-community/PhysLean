/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.TensorSpecies.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Module.RingHom
-- Contraction machinery for the type-safety smoke test below. Public because the test lives
-- in the public section and references `TensorSpecies.Tensor` and `contrT`.
public import Physlib.Relativity.Tensors.Contraction.Basic
public import Physlib.Relativity.Tensors.Conjugation.Basic

/-!

# SUSY N=1 chiral sector: index, configuration, and conjugation data

## i. Overview

This file fixes the data that indexes the scalars of the N=1 chiral sector,
makes their contractions type-safe, and equips them with conjugation.

A single finite type `ι` indexes the chiral scalars; it appears as
`ChiralIndexingType` in the signatures. It is the only index type. Variance
(upper versus lower) and holomorphy (a scalar versus its complex conjugate) are
not separate index types but the two axes of a four-element type `ChiralColor`,
the product of `chiral`/`anti` with `up`/`down`.

The dual-colour involution `τ` flips variance and preserves holomorphy. Two
indices may contract exactly when their colours are `τ`-related, so a holomorphic
index pairs only with a holomorphic index of the opposite variance, and a
conjugate ("barred") index only with a conjugate index of the opposite variance.
This is the discipline that makes the F-term contraction `g^{IJ̄} D_I W D̄_J̄ W̄`
type-check.

The physical field content is the configuration `ChiralScalarConfiguration ι =
ι → ℂ`, carrying `2 · Fintype.card ι` real degrees of freedom. The anti-chiral
scalars are the complex conjugates of this data, never an independent
configuration.

The index data is packaged as a `TensorSpecies` over `ChiralColor`. Every colour
shares the one carrier `ι → ℂ`; the four colours are labels recording variance
and holomorphy, not distinct spaces. Each carries the trivial `G`-representation,
so `G` acts as the identity and the chiral scalars hold no `G`-charge.
Contracting a colour against its `τ`-dual is
the dot product of their coordinate vectors in the fixed basis, which on basis
labels is the Kronecker `δ_{IJ}`. The `metric` and `unit` fields are both the
same element, the δ "cap" `∑_I b_I ⊗ b_I` whose components are `δ^{IJ}`.
Supplying this `TensorSpecies` instance equips the chiral sector with the
framework's generic tensor API (`.Tensor`, `.contrT`, and so on).

Conjugation is a separate operation layered on top of the species. The species
fixes which indices contract (via `τ`) but has no notion of complex-conjugating
a tensor; that is the role of `TensorSpecies.Conj`, a structure parameterized by
a species. The chiral sector opts in with `chiralConjStructure` (§F), supplying
the map `conjT` (conjugate the components and flip each index's holomorphy by
`ChiralColor.bar`) and its laws. `bar` is the holomorphy dual, distinct from and
commuting with the variance dual `τ`; it is not used in contraction.

Conjugation enters wherever reality does. It is what lets one state that the
Kähler metric is Hermitian (`conjT g` equals `g` with its two indices swapped),
that the anti-chiral sector is the complex conjugate of the chiral one
(`D̄_J̄ W̄ = conjT (D_I W)`), and hence that the F-term `g^{IJ̄} D_I W D̄_J̄ W̄`
is real. The species can express none of these alone. Since `chiralConjStructure`
has type `(chiralTensor …).Conj` and its coherence is a fact about
`chiralTensor`'s contraction, it necessarily follows the species definition (§F).

## ii. Key results

- `SUSY.N1.ChiralScalarConfiguration` : the scalar configuration space `ι → ℂ`,
    where `ι` is the finite type indexing the chiral scalars. This is the only
    field data in the sector.
- `SUSY.N1.ChiralColor` : the four colours `chiral`/`anti` × `up`/`down`, with the
    dual-colour involution `ChiralColor.tau`.
- `SUSY.N1.chiralTensor` : the `TensorSpecies` assembled from the above, whose
    `τ`-discipline makes the F-term contraction type-safe.
- `SUSY.N1.chiralConjStructure` : the `TensorSpecies.Conj` instance realizing the
    chiral-antichiral conjugation carried by `ChiralColor.bar`, the operation in
    which reality and Hermiticity conditions are phrased.

## iii. Table of contents

- A. The chiral scalar configuration
- B. The chiral colours and the dual involution
- C. Carrier, representation, and basis
- D. The δ structure on a based finite module
  - D.1. The bilinear form, contraction, and cap
  - D.2. Computation lemmas
  - D.3. The coherence laws
  - D.4. The coherence laws in `toSpanSingleton` form
- E. The chiral-index tensor species
- F. Conjugation
  - F.1. The conjugation structure
  - F.2. Scalar and covector helpers

## iv. References

-/

@[expose] public section
open TensorProduct Module ComplexConjugate
noncomputable section

namespace SUSY.N1

/-!
## A. The chiral scalar configuration

-/

/-- The chiral scalar configuration: a complex value for each chiral label. This is
the sector's only field data. Declared as an `abbrev` so that unification sees
through it to `α → ℂ` and applies Mathlib's function-space calculus lemmas directly. -/
abbrev ChiralScalarConfiguration (ChiralIndexingType : Type*) := ChiralIndexingType → ℂ

variable (ι : Type) [Fintype ι] [DecidableEq ι]
variable (G : Type) [Group G]

/-!
## B. The chiral colours and the dual involution

-/

/-- The four colours carried by a chiral-sector index: holomorphy (`chiral` versus
`anti`, a scalar versus its complex conjugate) crossed with variance (`up` versus
`down`, contravariant versus covariant). Carrying both axes here lets the single index
type `ι` label the scalars. -/
inductive ChiralColor | chiralUp | chiralDown | antiUp | antiDown
deriving DecidableEq

namespace ChiralColor

/-- The dual colour: flips variance and preserves holomorphy. Two indices may contract
exactly when their colours are `τ`-related, so `V^I` pairs only with `V_I` (same
holomorphy, opposite variance) and never with a conjugate index. -/
def tau : ChiralColor → ChiralColor
  | chiralUp => chiralDown
  | chiralDown => chiralUp
  | antiUp => antiDown
  | antiDown => antiUp

/-- The conjugate colour: flips holomorphy (`chiral`↔`anti`) and preserves variance. Complex
conjugation sends an index to its conjugate carrier, so `bar` swaps `chiral*` with `anti*`.
Distinct from the variance dual `tau`; the two commute (`bar_tau`). -/
def bar : ChiralColor → ChiralColor
  | chiralUp => antiUp
  | antiUp => chiralUp
  | chiralDown => antiDown
  | antiDown => chiralDown

@[simp] lemma bar_bar (c : ChiralColor) : bar (bar c) = c := by cases c <;> rfl

@[simp] lemma bar_tau (c : ChiralColor) : bar (tau c) = tau (bar c) := by cases c <;> rfl

end ChiralColor

variable {ι G}

/-!
## C. Carrier, representation, and basis

A `TensorSpecies` takes, for each colour `c`, a carrier module, a `G`-representation on it, and a
basis. Here none of these depend on the colour: every colour gets the same carrier `ι → ℂ`, the
trivial `G`-representation (no `G`-charge), and the indicator basis `piBasis`. So `chiralModule`,
`chiralRep`, and `chiralBasis` are constant in `c`; the colour is only the bookkeeping label that
`τ` and `bar` act on.

-/

/-- The carrier module of each colour: every colour shares the single carrier `ι → ℂ`. The
distinctions between colours (variance and holomorphy) are recorded by the colour and the maps
`τ`/`bar`, not by the carrier, so all four colours live in the same space. -/
def chiralModule : ChiralColor → Type := fun _ => ι → ℂ

instance instAddCommGroupChiralModule (c : ChiralColor) :
    AddCommGroup (chiralModule (ι := ι) c) := inferInstanceAs (AddCommGroup (ι → ℂ))

noncomputable instance instModuleChiralModule (c : ChiralColor) :
    Module ℂ (chiralModule (ι := ι) c) := inferInstanceAs (Module ℂ (ι → ℂ))

/-- The `G`-representation on each colour, taken trivial: the chiral scalars carry no
`G`-charge in this sector. -/
def chiralRep : (c : ChiralColor) → Representation ℂ G (chiralModule (ι := ι) c) :=
  fun _ => Representation.trivial ℂ G _

/-- The standard basis of the carrier `ι → ℂ` (the indicator functions). -/
def piBasis : Basis ι ℂ (ι → ℂ) := Pi.basisFun ℂ ι

/-- The standard basis of each colour's carrier: every colour shares the carrier `ι → ℂ`, hence
the basis `piBasis`. -/
def chiralBasis : (c : ChiralColor) → Basis ι ℂ (chiralModule (ι := ι) c) :=
  fun _ => piBasis

/-!
## D. The δ structure on a based finite module

The contraction, unit, and metric are the same δ structure, written in basis coordinates: the
contraction is the Kronecker δ pairing `(x, y) ↦ ∑_I x_I y_I`, while the unit and metric are both
the matching δ "cap" `∑_I b_I ⊗ b_I`. They are defined once below over an abstract based module
`(M, b)`, then used at `piBasis` to build the species' fields in §E. A contraction only ever pairs
a colour with its `τ`-dual (same holomorphy, opposite variance), so it stays within one holomorphy
and needs no conjugation; conjugation is carried instead by the tensor `conjT` and the
anti-holomorphic Wirtinger derivatives that produce barred components.

### D.1. The bilinear form, contraction, and cap

-/

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The δ bilinear form: the dot product of coordinate vectors in a basis `b`,
`(x, y) ↦ ∑_I (b x)_I (b y)_I`. -/
def deltaBil (b : Basis ι ℂ M) : M →ₗ[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => ∑ I, b.equivFun x I * b.equivFun y I)
    (fun x x' y => by simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun I _ => by ring)
    (fun x y y' => by simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun I _ => by ring)

/-- The δ contraction `M ⊗ M → ℂ`: the bilinear form `deltaBil` lifted to the tensor
product. -/
def deltaContr (b : Basis ι ℂ M) : M ⊗[ℂ] M →ₗ[ℂ] ℂ := TensorProduct.lift (deltaBil b)

/-- The δ cap `∑_I b_I ⊗ b_I`: the rank-2 tensor in `M ⊗ M` with two upper indices, whose
components in the basis `b` are `δⁱʲ`. It is an element of `M ⊗ M` (the inverse-metric "cap"
dual to `deltaContr`), not a linear map, and serves as both the metric and the unit of the
species. -/
def deltaCap (b : Basis ι ℂ M) : M ⊗[ℂ] M := ∑ I, b I ⊗ₜ[ℂ] b I

/-!
### D.2. Computation lemmas

Rewrite rules that evaluate the abstractly-defined `deltaContr` and `deltaCap` on concrete
inputs, together with their two symmetries. They are the only place that unfolds the δ
definitions and the basis coordinate facts; the coherence laws of §D.3 are assembled entirely
from them.

`deltaContr_tmul` is the base rule, `deltaContr b (x ⊗ₜ y) = ∑_I x_I y_I`. Specializing the
second argument to a basis vector (`deltaContr_tmul_basis`) reads off one coordinate, and
specializing both (`deltaContr_basis_basis`) gives the Kronecker `δ_{IJ}`, i.e. the basis is
orthonormal for the δ pairing. `deltaContr_comm` and `deltaCap_comm` record that the
contraction is symmetric in its arguments and that the cap is fixed by swapping its factors.

-/

omit [DecidableEq ι] in
/-- `deltaContr b (x ⊗ₜ y) = ∑_I x_I y_I`, the dot product of the coordinate vectors of `x` and
`y` in the basis `b` (writing `x_I := (b.equivFun x) I`). -/
lemma deltaContr_tmul (b : Basis ι ℂ M) (x y : M) :
    deltaContr b (x ⊗ₜ[ℂ] y) = ∑ I, b.equivFun x I * b.equivFun y I := by
  simp only [deltaContr, TensorProduct.lift.tmul, deltaBil, LinearMap.mk₂_apply]

/-- `deltaContr b (x ⊗ₜ b J) = x_J`: pairing with the basis vector `b J` reads off the `J`-th
coordinate `(b.equivFun x) J`. -/
lemma deltaContr_tmul_basis (b : Basis ι ℂ M) (x : M) (J : ι) :
    deltaContr b (x ⊗ₜ[ℂ] b J) = b.equivFun x J := by
  simp [deltaContr_tmul, Basis.equivFun_self]

/-- `deltaContr b (b I ⊗ₜ b J) = δ_{IJ}` (`if I = J then 1 else 0`): the basis vectors are
orthonormal for the δ pairing. -/
lemma deltaContr_basis_basis (b : Basis ι ℂ M) (I J : ι) :
    deltaContr b (b I ⊗ₜ[ℂ] b J) = if I = J then 1 else 0 := by
  rw [deltaContr_tmul_basis, Basis.equivFun_self]

omit [DecidableEq ι] in
/-- `deltaContr b (x ⊗ₜ y) = deltaContr b (y ⊗ₜ x)`: the δ contraction is symmetric, since
`∑_I x_I y_I = ∑_I y_I x_I`. -/
lemma deltaContr_comm (b : Basis ι ℂ M) (x y : M) :
    deltaContr b (x ⊗ₜ[ℂ] y) = deltaContr b (y ⊗ₜ[ℂ] x) := by
  rw [deltaContr_tmul, deltaContr_tmul]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

omit [DecidableEq ι] in
/-- `comm (deltaCap b) = deltaCap b`: swapping the two tensor factors fixes the cap, since
every summand `b_I ⊗ b_I` is symmetric. -/
lemma deltaCap_comm (b : Basis ι ℂ M) :
    TensorProduct.comm ℂ M M (deltaCap b) = deltaCap b := by
  rw [deltaCap, map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [TensorProduct.comm_tmul]

/-!
### D.3. The coherence laws

The three nontrivial axioms a `TensorSpecies` demands of its `unit`, `contr`, and `metric`,
proved here for the δ structure over an abstract based module `(M, b)` so that every colour
inherits them. Each corresponds to one species field:

- `deltaCap_unit_symm` (`unit_symm`): the cap is unchanged by swapping its factors;
- `deltaContr_deltaCap` (`contr_unit`): the snake identity, contracting the cap against a
  vector returns that vector;
- `deltaCap_contr_deltaCap` (`contr_metric`): contracting two adjacent caps yields one cap.

The fourth axiom, `contr_tmul_symm`, is just `deltaContr_comm` from §D.2 and is not repeated
here. These statements use `deltaCap`/`deltaContr` directly; §D.4 repackages them into the
`toSpanSingleton` form the species fields literally require.

-/

omit [DecidableEq ι] in
/-- The `unit_symm` law for the δ cap: `deltaCap b = lTensor M id (comm (deltaCap b))`.
On the right, `comm` swaps the cap's two tensor factors and `lTensor M id` applies the identity
to the left factor (it is the identity because `τ` here keeps the carrier fixed, so the
species' type-cast is trivial). Both operations leave the cap alone, so the law reduces to
`comm (deltaCap b) = deltaCap b` (`deltaCap_comm`): swapping the two legs of `∑_I b_I ⊗ b_I`
leaves it unchanged. -/
lemma deltaCap_unit_symm (b : Basis ι ℂ M) :
    deltaCap b = LinearMap.lTensor M (LinearEquiv.refl ℂ M).toLinearMap
      (TensorProduct.comm ℂ M M (deltaCap b)) := by
  simp only [deltaCap_comm, LinearEquiv.refl_toLinearMap, LinearMap.lTensor_id, LinearMap.id_coe,
    id_eq]

/-- The snake identity `∑_I (x · b_I) b_I = ∑_I x_I b_I = x` (the `contr_unit` law): contracting
`x` into the left leg of the cap `∑_I b_I ⊗ b_I` and keeping the right leg returns `x`. The
displayed term is the framework's spelling of this via `assoc`/`lid`. -/
lemma deltaContr_deltaCap (b : Basis ι ℂ M) (x : M) :
    (TensorProduct.lid ℂ M) ((deltaContr b).rTensor M
      ((TensorProduct.assoc ℂ M M M).symm (x ⊗ₜ[ℂ] deltaCap b))) = x := by
  rw [deltaCap, TensorProduct.tmul_sum, map_sum, map_sum, map_sum]
  conv_rhs => rw [← b.sum_equivFun x]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    deltaContr_tmul_basis]

/-- `∑_{IJ} (b_I · b_J) b_I ⊗ b_J = ∑_I b_I ⊗ b_I = deltaCap b` (the `contr_metric` law): contracting
the two inner legs of `deltaCap b ⊗ deltaCap b` collapses it to a single cap, using
`b_I · b_J = δ_{IJ}`. -/
lemma deltaCap_contr_deltaCap (b : Basis ι ℂ M) :
    (TensorProduct.comm ℂ M M ((TensorProduct.lid ℂ M).lTensor M
      (((deltaContr b).rTensor M).lTensor M
        (((TensorProduct.assoc ℂ M M M).symm.toLinearMap.lTensor M)
          ((TensorProduct.assoc ℂ M M (M ⊗[ℂ] M))
            (deltaCap b ⊗ₜ[ℂ] deltaCap b)))))) = deltaCap b := by
  conv_lhs => rw [deltaCap, TensorProduct.sum_tmul]
  conv_rhs => rw [deltaCap]
  simp only [TensorProduct.tmul_sum, map_sum]
  simp [TensorProduct.assoc_tmul, LinearEquiv.lTensor_tmul, LinearMap.lTensor_tmul,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    TensorProduct.comm_tmul, deltaContr_basis_basis, ite_smul]
  simp [TensorProduct.ite_tmul, Finset.sum_ite_eq]

/-!
### D.4. The coherence laws in `toSpanSingleton` form

The species' `unit` and `metric` fields are not the bare element `deltaCap b` but the map
`toSpanSingleton ℂ _ (deltaCap b)` sending `1 ↦ deltaCap b`, so the coherence goals mention
`toSpanSingleton _ (deltaCap b) 1` wherever §D.3 has `deltaCap b`. These three lemmas bridge
that gap: each rewrites `toSpanSingleton_apply_one` (`toSpanSingleton _ v 1 = v`) and then
applies the matching §D.3 law, restating it in the exact shape the fields require.

- `deltaUnit_symm` ← `deltaCap_unit_symm` (`unit_symm`);
- `deltaContr_unit` ← `deltaContr_deltaCap` (`contr_unit`);
- `deltaContr_metric` ← `deltaCap_contr_deltaCap` (`contr_metric`).

Stated abstractly over `(M, b)`, they reduce each coherence field of `chiralTensor` to a single
`cases c <;> exact …`. The fourth law, `contr_tmul_symm`, needs no adapter and uses
`deltaContr_comm` from §D.2 directly.

-/

omit [DecidableEq ι] in
/-- The `unit_symm` law with `unit = toSpanSingleton _ (deltaCap b)`: evaluated at `1` it is
`deltaCap b = lTensor M id (comm (deltaCap b))` (`deltaCap_unit_symm`). -/
lemma deltaUnit_symm (b : Basis ι ℂ M) :
    LinearMap.toSpanSingleton ℂ _ (deltaCap b) 1 =
      LinearMap.lTensor M (LinearEquiv.refl ℂ M).toLinearMap
        (TensorProduct.comm ℂ M M (LinearMap.toSpanSingleton ℂ _ (deltaCap b) 1)) := by
  simp only [LinearMap.toSpanSingleton_apply_one]
  exact deltaCap_unit_symm b

/-- The `contr_unit` law with the cap as `toSpanSingleton _ (deltaCap b)`: at `1` it is
`∑_I (x · b_I) b_I = x` (`deltaContr_deltaCap`). -/
lemma deltaContr_unit (b : Basis ι ℂ M) (x : M) :
    (TensorProduct.lid ℂ M) ((deltaContr b).rTensor M
      ((TensorProduct.assoc ℂ M M M).symm
        (x ⊗ₜ[ℂ] LinearMap.toSpanSingleton ℂ _ (deltaCap b) 1))) = x := by
  rw [LinearMap.toSpanSingleton_apply_one]
  exact deltaContr_deltaCap b x

/-- The `contr_metric` law with the metric as `toSpanSingleton _ (deltaCap b)`: at `1` it is
`∑_{IJ} (b_I · b_J) b_I ⊗ b_J = deltaCap b` (`deltaCap_contr_deltaCap`). -/
lemma deltaContr_metric (b : Basis ι ℂ M) :
    (TensorProduct.comm ℂ M M ((TensorProduct.lid ℂ M).lTensor M
      (((deltaContr b).rTensor M).lTensor M
        (((TensorProduct.assoc ℂ M M M).symm.toLinearMap.lTensor M)
          ((TensorProduct.assoc ℂ M M (M ⊗[ℂ] M))
            (LinearMap.toSpanSingleton ℂ _ (deltaCap b) 1 ⊗ₜ[ℂ]
              LinearMap.toSpanSingleton ℂ _ (deltaCap b) 1)))))) =
      LinearMap.toSpanSingleton ℂ _ (deltaCap b) 1 := by
  rw [LinearMap.toSpanSingleton_apply_one]
  exact deltaCap_contr_deltaCap b

/-!
## E. The chiral-index tensor species

-/

/-- The chiral-index tensor species. Its colours are `chiral`/`anti` × `up`/`down`, all carried
by `ι → ℂ`, and every colour contracts by the bare δ pairing with the δ cap serving as both
metric and unit. Each coherence law reduces, by case analysis on the colour, to the
corresponding abstract δ lemma above. Instantiating `TensorSpecies` this way gives the chiral
sector the framework's generic tensor API. -/
def chiralTensor : TensorSpecies ℂ ChiralColor G (chiralModule (ι := ι)) (fun _ => ι)
    (chiralRep (ι := ι) (G := G)) (chiralBasis (ι := ι)) where
  τ := ChiralColor.tau
  τ_involution c := by cases c <;> rfl
  -- The carrier is `ι → ℂ` for every colour, so the data fields are uniform in `c`.
  contr _ := { deltaContr piBasis with
      isIntertwining' g := by ext v; simp [Representation.tprod_apply, chiralRep] }
  unit _ := { LinearMap.toSpanSingleton ℂ _ (deltaCap piBasis) with
      isIntertwining' g := by ext; simp [Representation.tprod_apply, chiralRep, deltaCap] }
  metric _ := { LinearMap.toSpanSingleton ℂ _ (deltaCap piBasis) with
      isIntertwining' g := by ext; simp [Representation.tprod_apply, chiralRep, deltaCap] }
  -- Each coherence law reduces, by case analysis on `c`, to the matching abstract δ lemma.
  contr_tmul_symm c x y := by cases c <;> exact deltaContr_comm _ _ _
  unit_symm c := by cases c <;> exact deltaUnit_symm _
  contr_unit c x := by cases c <;> exact deltaContr_unit _ x
  contr_metric c := by cases c <;> exact deltaContr_metric _

/-- Type-safety smoke test. `chiralUp` and `chiralDown` are `τ`-dual, so a rank-2 tensor with
those index colours admits the framework contraction `contrT`. A same-variance pair would
fail the `τ`-hypothesis `S.τ (c I) = c J`, which is exactly the safety the species provides. -/
example (t : (chiralTensor (ι := ι) (G := G)).Tensor
      ![ChiralColor.chiralUp, ChiralColor.chiralDown]) :
    (chiralTensor (ι := ι) (G := G)).Tensor
      (![ChiralColor.chiralUp, ChiralColor.chiralDown] ∘ Fin.succSuccAbove 0 1) :=
  TensorSpecies.Tensor.contrT 0 0 1 ⟨by decide, rfl⟩ t

/-!
## F. Conjugation

Conjugation is a layer on top of the species of §E, not part of it: `TensorSpecies.Conj S` is a
structure parameterized by a species `S`, and the framework defines the conjugation map `conjT`
and its laws once, abstractly, against any species that supplies one. This section therefore
follows §E: `chiralConjStructure` has type `(chiralTensor …).Conj`, and its `conj_contrComm`
field is a fact about `chiralTensor`'s contraction, neither of which can be stated before the
species exists.

The chiral sector's conjugation flips holomorphy (`ChiralColor.bar`) while preserving variance, and
through the resulting `conjT` the reality and Hermiticity conditions are phrased. The basis index
type `ι` is the same for every colour, so the index identification `barIdx_eq` is `rfl` and the
component reindexing is the identity.

### F.1. The conjugation structure

-/

section Conjugation

open TensorSpecies TensorSpecies.Tensor ChiralColor

/-- The chiralTensor contraction coefficient of two basis vectors is the Kronecker δ, stated at
the colour level so it matches goals carrying `chiralModule d`. -/
lemma chiralTensor_contr_chiralBasis (d : ChiralColor) (x₁ x₂ : ι) :
    (chiralTensor (ι := ι) (G := G)).contr d
        (chiralBasis d x₁ ⊗ₜ[ℂ] chiralBasis ((chiralTensor (ι := ι) (G := G)).τ d) x₂)
      = if x₁ = x₂ then 1 else 0 := by
  cases d <;>
    exact deltaContr_basis_basis _ x₁ x₂

/-- The conjugation structure on the chiral tensor species: `bar` flips holomorphy while
preserving variance, and the basis labels of each colour are identified with those of its
conjugate via the identity (both carry the same index type `ι`). -/
def chiralConjStructure : (chiralTensor (ι := ι) (G := G)).Conj where
  bar := ChiralColor.bar
  bar_involution := ChiralColor.bar_bar
  bar_tau := ChiralColor.bar_tau
  barIdx_eq _ := rfl
  conj_contrComm := by
    intro d x₁ x₂
    cases d <;> simp [chiralTensor_contr_chiralBasis, apply_ite (starRingEnd ℂ), basisIdxCongr]

-- Smoke tests: type-safety and behaviour checks for `chiralConjStructure`.

/-- Conjugating a metric-typed tensor `g : Tensor ![chiralDown, antiDown]` via `chiralConjStructure`
lands in the conjugate-colour list `ChiralColor.bar ∘ ![chiralDown, antiDown]`, i.e.
`![antiDown, chiralDown]`. This is purely a type-safety check. -/
example (g : (chiralTensor (ι := ι) (G := G)).Tensor ![chiralDown, antiDown]) :
    (chiralTensor (ι := ι) (G := G)).Tensor (ChiralColor.bar ∘ ![chiralDown, antiDown]) :=
  chiralConjStructure.conjT g

/-- `conjT_contrT` applies to a one-index contraction: conjugating first and then contracting
equals contracting the conjugate. Checked at colour `![chiralUp, chiralDown]` contracted at
slots `0` and `1`. -/
example (t : (chiralTensor (ι := ι) (G := G)).Tensor ![ChiralColor.chiralUp, ChiralColor.chiralDown]) :
    chiralConjStructure.conjT (TensorSpecies.Tensor.contrT 0 0 1 ⟨by decide, rfl⟩ t)
      = TensorSpecies.Tensor.contrT 0 0 1 ⟨by decide, rfl⟩ (chiralConjStructure.conjT t) :=
  chiralConjStructure.conjT_contrT 0 1 ⟨by decide, rfl⟩ t

/-!
### F.2. Scalar and covector helpers

These two definitions normalize the output of `chiralConjStructure.conjT` back to the canonical
colour lists for scalar and anti-holomorphic covector tensors respectively.

-/

/-- Conjugation of a scalar tensor, normalized back to the scalar colour list `![]`. -/
def conjScalar (t : (chiralTensor (ι := ι) (G := G)).Tensor ![]) :
    (chiralTensor (ι := ι) (G := G)).Tensor ![] :=
  permT id ⟨Function.bijective_id, fun i => by fin_cases i⟩
    (chiralConjStructure.conjT t)

/-- Conjugation of a holomorphic covector, normalized to the anti-holomorphic covector colour
list `![antiDown]`. -/
def conjChiralCovector
    (t : (chiralTensor (ι := ι) (G := G)).Tensor ![chiralDown]) :
    (chiralTensor (ι := ι) (G := G)).Tensor ![antiDown] :=
  permT ![0] ⟨by decide, fun i => by fin_cases i; rfl⟩
    (chiralConjStructure.conjT t)

/-- For scalar tensors, `toField` of the normalized tensor conjugate is the complex conjugate of
`toField`. -/
theorem toField_conjScalar (t : (chiralTensor (ι := ι) (G := G)).Tensor ![]) :
    (conjScalar t).toField = star t.toField := by
  rw [conjScalar, toField_permT]
  rw [toField_eq_repr, toField_eq_repr]
  change componentMap (S := chiralTensor (ι := ι) (G := G))
      (chiralConjStructure.bar ∘ ![]) (chiralConjStructure.conjT t) (fun j => Fin.elim0 j) =
    star ((basis (S := chiralTensor (ι := ι) (G := G)) ![]).repr t (fun j => Fin.elim0 j))
  rw [TensorSpecies.Conj.componentMap_conjT (cj := chiralConjStructure)]
  rfl

/-- Component formula for the holomorphic covector conjugate: the `![I]` basis component of
`conjChiralCovector t` is the complex conjugate of the `![I]` component of `t`. -/
theorem repr_conjChiralCovector
    (t : (chiralTensor (ι := ι) (G := G)).Tensor ![chiralDown]) (I : ι) :
    (basis (S := chiralTensor (ι := ι) (G := G)) ![antiDown]).repr
        (conjChiralCovector t) ![I] =
      star ((basis (S := chiralTensor (ι := ι) (G := G)) ![chiralDown]).repr t ![I]) := by
  rw [conjChiralCovector, permT_basis_repr_symm_apply]
  change componentMap (S := chiralTensor (ι := ι) (G := G))
      (chiralConjStructure.bar ∘ ![chiralDown]) (chiralConjStructure.conjT t) _ = _
  rw [TensorSpecies.Conj.componentMap_conjT (cj := chiralConjStructure)]
  apply congrArg star
  apply congrArg (fun idx => componentMap (S := chiralTensor (ι := ι) (G := G))
    ![chiralDown] t idx)
  funext i
  fin_cases i
  rfl

/-- Conjugation of a holomorphic covector is additive. -/
@[simp]
theorem conjChiralCovector_add
    (t₁ t₂ : (chiralTensor (ι := ι) (G := G)).Tensor ![chiralDown]) :
    conjChiralCovector (t₁ + t₂) = conjChiralCovector t₁ + conjChiralCovector t₂ := by
  rw [conjChiralCovector, chiralConjStructure.conjT_add]
  simp [conjChiralCovector, map_add]

/-- Conjugation of a holomorphic covector is conjugate-linear: a scalar `r` pulls out as
`star r`. -/
@[simp]
theorem conjChiralCovector_smul (r : ℂ)
    (t : (chiralTensor (ι := ι) (G := G)).Tensor ![chiralDown]) :
    conjChiralCovector (r • t) = star r • conjChiralCovector t := by
  rw [conjChiralCovector, chiralConjStructure.conjT_smul]
  simp [conjChiralCovector]

end Conjugation

end SUSY.N1

end

end
