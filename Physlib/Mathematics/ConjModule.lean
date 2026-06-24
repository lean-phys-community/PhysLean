/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Tactic.Ring

/-!

# The conjugate module

Over a commutative star-ring `k`, the *conjugate module* `ConjModule M` of a `k`-module `M` is the
same additive group with the scalar action twisted by conjugation: `r • v := star r • v`. It is the
device that turns a sesquilinear pairing into a genuine bilinear one: a map conjugate-linear in a
slot `M` is linear in the slot `ConjModule M`.

`ConjModule M` is a type synonym carrying a fresh `Module k` instance (`Module.compHom` along
`starRingEnd k`), so the twisted action does not leak onto `M` and vice versa. The canonical
conjugate-linear identity `conjEquiv : M ≃ₛₗ[starRingEnd k] ConjModule M`, the involution
`ConjModule (ConjModule M) ≃ₗ[k] M`, and the transported basis `Basis.conj` are provided.

## Key results

- `ConjModule` : the conjugate-module type synonym, with its twisted `Module` instance.
- `conjEquiv` : the canonical conjugate-linear equivalence `M ≃ₛₗ[starRingEnd k] ConjModule M`.
- `ConjModule.involution` : the involution `ConjModule (ConjModule M) ≃ₗ[k] M`.
- `Basis.conj` : a basis of `M` transported to a basis of `ConjModule M` (coordinates by `star`).

-/

@[expose] public section

open Module

variable {k : Type*} [CommRing k] [StarRing k]
variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The conjugate module of `M`: the same additive group with the scalar action twisted by
conjugation, `r • v = star r • v`. A type synonym so the twisted action stays off `M`. -/
def ConjModule (M : Type*) := M

namespace ConjModule

instance : AddCommGroup (ConjModule M) := inferInstanceAs (AddCommGroup M)

/-- The twisted action `r • v = star r • v`, obtained by restricting scalars along the
conjugation ring endomorphism `starRingEnd k`. -/
noncomputable instance instModule : Module k (ConjModule M) :=
  Module.compHom M (starRingEnd k)

lemma smul_def (r : k) (v : M) :
    (r • (id v : ConjModule M) : ConjModule M) = (star r • v : M) := rfl

end ConjModule

/-- The canonical conjugate-linear equivalence `M ≃ₛₗ[starRingEnd k] ConjModule M`, the identity on
the underlying additive group. -/
noncomputable def conjEquiv : M ≃ₛₗ[starRingEnd k] ConjModule M where
  toFun v := v
  map_add' _ _ := rfl
  map_smul' r v := by show (r • v : M) = (star (star r) • v : M); rw [star_star]
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl

namespace ConjModule

/-- Conjugating twice returns the original module: `ConjModule (ConjModule M) ≃ₗ[k] M`. Built by
composing the two `conjEquiv`s (`starRingEnd ∘ starRingEnd = id`) and taking the inverse. -/
noncomputable def involution : ConjModule (ConjModule M) ≃ₗ[k] M :=
  ((conjEquiv (k := k) (M := M)).trans (conjEquiv (k := k) (M := ConjModule M))).symm

variable {ι : Type*}

/-- Coordinate-wise conjugation on `ι →₀ k`, a conjugate-linear self-equivalence. -/
noncomputable def starFinsupp : (ι →₀ k) ≃ₛₗ[starRingEnd k] (ι →₀ k) where
  toFun f := f.mapRange star (star_zero k)
  invFun f := f.mapRange star (star_zero k)
  map_add' f g := by ext i; simp [Finsupp.mapRange_apply, star_add]
  map_smul' r f := by
    ext i
    simp only [Finsupp.mapRange_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      starRingEnd_apply, star_mul']
  left_inv f := by ext i; simp [Finsupp.mapRange_apply]
  right_inv f := by ext i; simp [Finsupp.mapRange_apply]

/-- A basis of `M` transported to a basis of `ConjModule M`: the same basis vectors, with
coordinates conjugated (`(Basis.conj b).repr v = star ∘ b.repr v`). -/
noncomputable def _root_.Basis.conj (b : Basis ι k M) : Basis ι k (ConjModule M) :=
  Basis.ofRepr
    (((conjEquiv (k := k) (M := M)).symm.trans b.repr).trans starFinsupp)

end ConjModule

end
