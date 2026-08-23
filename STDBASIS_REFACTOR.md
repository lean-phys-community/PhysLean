# `StdBasis` refactor: scoping, design, and migration plan

Status of this document: Stages 0–2, Stage 5, and most of Stage 3 have landed, and the whole of
`QuantumInfo` builds green with zero errors and zero warnings.

* **Stage 0** — `QuantumInfo/ForMathlib/StdBasis.lean` and `QuantumInfo/Finite/StdBasisState.lean`.
* **Stage 1 (partial)** — `QuantumInfo/ForMathlib/HermitianOp.lean` defines
  `HermitianOp E := selfAdjoint (E →L[ℂ] E)` with `trace`, `cfc`, the Loewner order, and the
  bridge `HermitianOp.toMat : HermitianOp E ≃ₗ[ℝ] HermitianMat ι ℂ` induced by a `StdBasis ℂ E ι`,
  together with `toMat_le_toMat`, `trace_toMat`, `spectrum_toMat` and `toMat_cfc`. `HermitianMat`
  itself is unchanged, and the individual `HermitianMat/*` files have not been ported.
* **Stage 2** — `MState` is now basis-free: `DensityOp E` is a structure carrying a positive
  unit-trace `HermitianOp E`, and `MState d` is the abbreviation
  `DensityOp (EuclideanSpace ℂ d)`. `DensityOp.M`/`DensityOp.m` recover the density matrix through
  the preferred basis, and every previously-matrix-stated fact in `MState.lean` is re-derived from
  the operator-level one. `Braket.lean` has *not* been migrated: `Ket`/`Bra` are still functions
  `d → ℂ`.

* **Stage 3 (most of it)** — the state-level quantities are now basis-free, each paired with a
  "matrix analogue" theorem that recovers the old matrix formula through an arbitrary `StdBasis`:

  | Basis-free definition | Matrix analogue |
  | --- | --- |
  | `Sᵥₙ (ρ : DensityOp E)` | `Sᵥₙ_eq_trace_cfc_negMulLog`, `Sᵥₙ_eq_re_trace_matrix_cfc` |
  | `TrDistance` | `TrDistance.eq_matrix_traceNorm` |
  | `DensityOp.fidelity` | `DensityOp.fidelity_eq_matrix` |
  | `DensityOp.U_conj` | `DensityOp.U_conj_M` (and `MState.U_conj`, `U ◃ ρ`, on top of it) |
  | `SandwichedRelRentropy`, `qRelativeEnt` | `sandwichedRelRentropy_eq_matrix`, and its
    index-determined specialisation `MState.sandwichedRelRentropy_eq_matrix` |

  Supporting this, `ForMathlib/HermitianOp.lean` gained `conj_nonneg`, `trace_conj_unitary`,
  `conj_unitary_le_conj_unitary`, `inner_conj_unitary`, the operator kernel/support (`ker`,
  `support`) with the coordinate bridge `lin_toMat_apply`/`mem_ker_toMat_iff`/
  `ker_toMat_le_ker_toMat`, and `ForMathlib/StdBasis.lean` gained the bijection
  `StdBasis.toMatUnitary`/`StdBasis.unitaryOfMat` between `unitary (E →L[𝕜] E)` and
  `Matrix.unitaryGroup ι 𝕜`.

  Two general patterns carried the work:
  - To prove a basis-free statement, introduce an arbitrary basis locally with
    `let _ : StdBasis ℂ E (Fin (Module.finrank ℂ E)) := StdBasis.some ℂ E` and rewrite with the
    matrix analogue.
  - To reuse an `MState`-level matrix fact for a general `DensityOp E`, push its density matrix
    back through `DensityOp.ofMat` to get an `MState ι` with the same `M` (the `coords` device in
    `Entropy/Relative.lean`).

  Two casualties, both from `SandwichedRelRentropy`'s index type no longer being a plain argument:
  `sandwichedRelRentropy_congr` and `qRelEntropy_heq_congr` lost their `@[gcongr]` attributes,
  because `gcongr` requires the varying arguments of the head function to be free variables and
  they are now `EuclideanSpace ℂ d₁` / `EuclideanSpace ℂ d₂`. Their two call sites apply them by
  name instead.

  Not yet done in Stage 3: `Entropy/SSA.lean` (still matrix-stated throughout) and
  `Entropy/DPI.lean` (blocked on Stage 4).

* **Stage 5** — `CPTPMap/OpMap.lean` defines `OpMap E F := (E →L[ℂ] E) →ₗ[ℂ] (F →L[ℂ] F)` with
  `OpMap.toMat`/`OpMap.ofMat` as the bridge to `MatrixMap`, and `CPTPMap/Bundled.lean` carries the
  nine-structure hierarchy `HPOp/UnitalOp/TPOp/POp/CPOp/PTPOp/PUOp/CPTPOp/CPUOp` at the operator
  level, with `abbrev CPTPMap dIn dOut := CPTPOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)`
  (and likewise for the other eight). Every channel constructed from a matrix presentation —
  `of_kraus`, `ofUnitary`, `traceLeft`/`traceRight`, `assoc`, `piProd`, `replacement`, … — is
  `<Class>Op.ofMat <matrixmap> <proofs>` together with a `@[simp]` "matrix analogue" lemma
  `X_map : X.map = <matrixmap>`. Choi matrices and Kraus decompositions stay matrix-side, as
  planned in §4 Stage 5.

Remaining downstream files (`Entropy/{SSA,DPI}`, `Ensemble`, `POVM`, `Entanglement`, `Pinching`,
`ResourceTheory/*`) have been repaired against the new `DensityOp`/`CPTPOp` API but not yet
migrated to operator form; they still speak in matrices via `ρ.M`. Stages 4, 6 and 7 below are
unstarted.

### Known ergonomic wart: dot notation through the `MState`/`CPTPMap` abbreviations

`MState d` is an `abbrev` for `DensityOp (EuclideanSpace ℂ d)`, and dot notation `x.foo` resolves on
the *inferred* head constant of `x`'s type. A channel application `Λ ρ` has inferred type
`DensityOp (EuclideanSpace ℂ dOut)`, so `(Λ ρ).exp_val T` fails with "the environment does not
contain `DensityOp.exp_val`" for any lemma that lives in the `MState` namespace. A type ascription
`(Λ ρ : MState dOut).exp_val` does **not** help — the ascription is erased before resolution. The
two things that do work are a *binder* annotation (`∀ ρ : MState d, …`, since binder types are
stored un-unfolded) and the fully qualified name (`MState.exp_val (Λ ρ) T`).

The fix is to move `MState`'s basis-free API into the `DensityOp` namespace, since dot notation
retries after unfolding reducible definitions; `MState.*` names that are genuinely basis-dependent
(`ofClassical`, `uniform`, `spectrum`, `relabel`) should stay put.

---

## 1. Reconnaissance

### 1.1 Genuinely basis-dependent vs. basis-free-but-matrix-stated

The library is ~33k lines across 89 files under `QuantumInfo/`. Sorting the content by how it
relates to a choice of basis:

**Genuinely basis-dependent** (a `StdBasis` instance is real input, not bookkeeping):

| Location | What depends on the basis |
| --- | --- |
| `Finite/Braket.lean` | `Ket d`/`Bra d` are *functions* `d → ℂ`; `Ket.basis i`, `Ket.MES`, `uniform_superposition`, `Ket.prod` are all defined coordinatewise |
| `Finite/MState.lean` | `MState.ofClassical`, `MState.uniform`, `MState.spectrum` (canonically *sorted* eigenvalues, hence index-dependent), `relabel` |
| `Finite/POVM.lean` | measurement outcomes indexed by a type; the computational-basis measurement |
| `Finite/Qubit/Basic.lean` | Pauli matrices, Bloch sphere coordinates |
| `QECC/*` (≈3.4k lines) | Pauli group, stabilizer groups, CSS codes, transversal gates — all defined on `Fin n → …` index tuples. This subtree is *irreducibly* basis-dependent and is the main consumer of the new class |
| `ForMathlib/HermitianMat/Basic.lean` `diagonal`, `Proj.lean`, `Majorization.lean` | diagonal matrices, coordinate projections, majorization of eigenvalue vectors |
| `StatMech/*` | Hamiltonians given as explicit matrices |

**Basis-free in content, matrix-stated in form** (the bulk; this is what a refactor buys):

| Location | Why it is basis-free |
| --- | --- |
| `ForMathlib/HermitianMat/{Order,Trace,Inner,Sqrt,CFC,Rpow,LogExp,Schatten,Jordan,NonSingular}.lean` (≈4.3k lines) | everything is a statement about a self-adjoint element of a C\*-algebra: order, trace, `cfc`, `rpow`, `log`/`exp`, Schatten norms, Jordan product |
| `Finite/Entropy/*` (≈2.3k + 1.3k + 0.4k lines) | von Neumann entropy, relative entropy, SSA, DPI: all unitary-invariant spectral functionals |
| `Finite/Distance/*` | trace distance and fidelity are unitarily invariant |
| `Finite/CPTPMap/*` (≈2.9k lines) | positivity/complete positivity/trace preservation of a linear map; Choi matrix and Kraus decompositions are matrix-*presentations* of basis-free notions |
| `Finite/ResourceTheory/*`, `Finite/Pinching.lean`, `Finite/Capacity.lean` | consequences of the above |

Rough scale of matrix-level surface: `.mat` appears ~1180 times in 25 files, `Matrix.trace` ~210
times, eigenvalue/spectrum identifiers ~1300 times, kronecker ~445, `submatrix`/`reindex` ~300.

### 1.2 The dependency spine

```
ForMathlib/{Matrix, Isometry, Unitary, LinearEquiv, ContinuousLinearMap}
        └── ForMathlib/HermitianMat/{Basic, Order, Trace, Reindex, Inner, NonSingular,
                                      Sqrt, CFC, Rpow, LogExp, Jordan, Proj, Schatten}
                └── Finite/Braket ──┐
                                    ├── Finite/MState ── Finite/Unitary
                                    │        ├── Finite/CPTPMap/{MatrixMap, Unbundled,
                                    │        │      Bundled, CPTP, Dual}
                                    │        ├── Finite/Entropy/{VonNeumann, Relative, SSA, DPI}
                                    │        ├── Finite/Distance/{TraceDistance, Fidelity}
                                    │        ├── Finite/{Ensemble, POVM, Entanglement, Pinching}
                                    │        └── Finite/ResourceTheory/{FreeState,
                                    │               HypothesisTesting, SteinsLemma}
                                    └── QECC/{Pauli, Stabilizer, StabilizerGroup, Codes,
                                              CSS, Transversal, Defs, Bounds, Concatenation}
```

`MState` is the single choke point: `HermitianMat` sits below it, and essentially everything else
sits above it.

### 1.3 What `HermitianMat` would have to become

`HermitianMat n α := selfAdjoint (Matrix n n α)`. The basis-free counterpart is
`selfAdjoint (E →L[ℂ] E)`, which Mathlib already supports well:

* `CStarAlgebra (E →L[ℂ] E)`, `ContinuousLinearMap.instStarOrderedRing` and
  `IsSelfAdjoint.instContinuousFunctionalCalculus` are **global** instances needing only
  `[CompleteSpace E]`. The corresponding `Matrix` instances are **scoped** (`Matrix.Norms.L2Operator`,
  `MatrixOrder`), so the operator side is if anything *better* supported than the matrix side.
* Consequently `cfc`, `rpow`, `log`, `exp`, `sqrt`, positivity, and the Loewner order all port
  essentially verbatim: `ForMathlib/HermitianMat/{CFC, Rpow, LogExp, Sqrt, Order, Jordan}.lean`
  (≈3.6k lines) are already phrased in CFC/order language and would mostly need only their
  `HermitianMat n α` binders swapped.

What does **not** port for free:

* `trace`. `LinearMap.trace 𝕜 E` exists and `LinearMap.trace_eq_sum_inner` /
  `trace_eq_matrix_trace` connect it to matrices, but there is no `HermitianMat.trace`-style real
  valued trace on operators; it must be rebuilt (small).
* `Schatten.lean`, `MatrixNorm/TraceNorm.lean`. **Mathlib has no Schatten norms, no trace class, no
  Hilbert–Schmidt norms** for operators. Zero hits. These would have to be defined from scratch on
  the operator side or kept matrix-side behind the `toMat` bridge.
* `traceLeft`/`traceRight`. **Mathlib has no partial trace at all.** Zero hits. This is defined
  index-wise in `HermitianMat/Trace.lean`. On the operator side it must be built from
  `TensorProduct` + `LinearMap.trace`, which is a genuine new development.
* `diagonal`, `Proj`, `Majorization` — these are basis-dependent by nature and stay matrix-side,
  now consuming a `StdBasis`.

### 1.4 What Mathlib provides

Available and directly usable:

* `OrthonormalBasis ι 𝕜 E` — a one-field structure wrapping `repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι`
  (requires `[Fintype ι]`).
* `LinearMap.toMatrixOrthonormal : (E →ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix ι ι 𝕜` (needs `FiniteDimensional`),
  `Matrix.toEuclideanCLM : Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)`,
  `Matrix.toEuclideanLin`, `LinearIsometryEquiv.conjStarAlgEquiv`.
* `Module.Basis.toMatrix`, `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`,
  `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`.
* Basis-free spectral theorem: `LinearMap.IsSymmetric.eigenvectorBasis`, `.eigenvalues`,
  `.apply_eigenvectorBasis`, `.diagonalization`.
* `LinearMap.trace`, `LinearMap.trace_eq_sum_inner`, `LinearMap.trace_eq_matrix_trace`.
* `TensorProduct.instInnerProductSpace` and `OrthonormalBasis.tensorProduct`.
* Full CFC on `E →L[ℂ] E` (see above), `ContinuousLinearMap.IsPositive`,
  `ContinuousLinearMap.nonneg_iff_isPositive`, `Matrix.isPositive_toEuclideanLin_iff`.

Missing from Mathlib (each is a cost line-item for the migration):

* Partial trace (any form).
* Schatten / trace-class / Hilbert–Schmidt norms for operators.
* `OrthonormalBasis.single`; a `StdBasis`-style canonical-basis class.
* CFC on bare `E →ₗ[ℂ] E` (only the CLM version).
* `HilbertBasis → OrthonormalBasis` (only the forward `OrthonormalBasis.toHilbertBasis`).
* A CLM version of `TensorProduct.map`.
* **`FiniteDimensional.complete` is a theorem, not an instance.** This is a real ergonomic problem
  (see §2.4).

---

## 2. Design evaluation

### 2.1 Recommendation

```lean
class StdBasis (𝕜 : Type*) (E : Type*) (ι : outParam Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] where
  stdBasis : OrthonormalBasis ι 𝕜 E
```

with `EuclideanSpace 𝕜 d` carrying `EuclideanSpace.basisFun d 𝕜` as the canonical instance, and
`E ⊗[𝕜] F` carrying `OrthonormalBasis.tensorProduct`.

### 2.2 `OrthonormalBasis` vs `Module.Basis` vs `HilbertBasis`

**`OrthonormalBasis` wins, decisively.**

* With a bare `Module.Basis`, the change-of-basis matrix ranges over all of `GL`. Eigenvalues,
  entropies, Schatten norms and positivity are **not** invariant under general similarity, so the
  insensitivity lemmas that are the entire point of the refactor would be *false*. Orthonormality
  is exactly the condition that makes the change-of-basis matrix unitary
  (`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`).
* `Module.Basis` gives `LinearMap.toMatrix : (E →ₗ[𝕜] E) ≃ₐ[𝕜] Matrix ι ι 𝕜` — an *algebra*
  equivalence. `OrthonormalBasis` gives `LinearMap.toMatrixOrthonormal`, a `≃⋆ₐ[𝕜]`. The star
  structure is what transports adjoints, self-adjointness, unitarity, spectra and the entire CFC.
  Without it, `HermitianMat` and everything downstream cannot cross the bridge.
* `HilbertBasis` was rejected: it lands in `lp` rather than `EuclideanSpace`, drags in
  `CompleteSpace`, and has no reverse of `OrthonormalBasis.toHilbertBasis`. It buys nothing in
  finite dimensions.

### 2.3 `(ι 𝕜 E)` vs `(ι E)` with `𝕜 := ℂ`

Keep `𝕜` general (`RCLike`). It costs one extra argument and nothing else; `HermitianMat` in this
library is already generic over `RCLike 𝕜` in several files (`Trace.lean`, `Inner.lean`), and
`ClassicalInfo` needs the real case. Specialising to `ℂ` now would force a second class later.

`ι` is an `outParam`: a type carries at most one preferred basis, and the index type is part of
that choice. Empirically this infers correctly even though the `[Fintype ι]` binder precedes the
class (Lean postpones instance subgoals containing metavariables). Making `ι` a regular parameter
would leave it unconstrained at every use site.

### 2.4 Instance-diamond and defeq risks

* **Two instances on one type.** Prevented by treating `StdBasis` as canonical data:
  `StdBasis.reindex` and `StdBasis.transport` are **`def`s, not instances**. As instances they
  would loop (`transport` along any isometry) and would silently install non-canonical bases. The
  price is that a relabelled basis must be passed explicitly — acceptable, and
  `StdBasisState.ofOp_reindex` shows the resulting boilerplate is one line.
* **`d₁ × d₂` vs tensor product.** No diamond: `StdBasis ℂ (EuclideanSpace ℂ (d₁ × d₂)) (d₁ × d₂)`
  and `StdBasis ℂ (E ⊗[ℂ] F) (ι × κ)` are instances on *different carrier types*. The bridge
  between them (`EuclideanSpace ℂ d₁ ⊗[ℂ] EuclideanSpace ℂ d₂ ≃ₗᵢ EuclideanSpace ℂ (d₁ × d₂)`) has
  to be an explicit isometry, which is the honest state of affairs anyway.
* **`CompleteSpace`.** `FiniteDimensional.complete` is a theorem, not an instance, so a
  `[StdBasis 𝕜 E ι]` binder does **not** give `CompleteSpace E`, and without it the C\*-algebra and
  `Star` structure on `E →L[𝕜] E` do not synthesize. Every operator-level declaration must carry
  `[CompleteSpace E]` explicitly (it is a `Prop` class, so there is no diamond, only noise). The
  prototype supplies the missing `CompleteSpace (E ⊗[𝕜] F)` instance. **This is the single largest
  ergonomic tax of the whole design.** The clean fix is upstream: make `FiniteDimensional.complete`
  an instance in Mathlib, or add a local low-priority instance in this repo. Recommend the latter
  as a follow-up experiment, gated on checking it does not slow down instance search.

### 2.5 Should `EuclideanSpace ℂ d` be canonical?

Yes, and it is. `StdBasis.toMat 𝕜 (EuclideanSpace 𝕜 d) d = (Matrix.toEuclideanCLM).symm` holds by
`rfl` (`toMat_euclideanSpace`), and `MState.ofOp_basisFun` is likewise `rfl`. That means today's
matrix-level library is *definitionally* the special case `E := EuclideanSpace ℂ d`, so a
compatibility shim `MState d := MState' (EuclideanSpace ℂ d)` will be defeq-transparent rather than
requiring a transport.

### 2.6 Simp normal form: `Matrix d d ℂ` vs `M →L[ℂ] M`

Recommendation: **`E →L[𝕜] E` is the normal form for basis-free statements; matrices are the normal
form only inside genuinely basis-dependent files** (`QECC/`, `Qubit/`, `Majorization`, `Proj`,
`diagonal`). `StdBasis.toMatOf_apply` is the `@[simp]` lemma that pushes through the bridge when a
matrix entry is genuinely wanted. Do not mark `toMatOf_eq_toMatrixOrthonormal` as `simp`: it should
be used deliberately, not as a rewrite direction.

### 2.7 Cost

`StdBasis` adds one class with one field, resolved by at most two instances per type. The real
cost is not typeclass search, it is the `[NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
[CompleteSpace E] [FiniteDimensional 𝕜 E] [StdBasis 𝕜 E ι] [Fintype ι] [DecidableEq ι]` binder
block, which is seven binders where today's code has two (`[Fintype d] [DecidableEq d]`). A
`variable` block plus judicious `abbrev`s keeps this tolerable, but it will make every signature in
the library visibly longer. Universes are unproblematic (`E` and `ι` live in independent
universes).

---

## 3. What the prototype contains

### `QuantumInfo/ForMathlib/StdBasis.lean` (330 lines, compiles clean, no `sorry`)

* `class StdBasis`, `export StdBasis (stdBasis)`.
* Instances: `EuclideanSpace.instStdBasis`, `StdBasis.instTensorProduct`,
  `StdBasis.toFiniteDimensional`, `TensorProduct.instCompleteSpaceOfFiniteDimensional`.
* Non-instances by design: `StdBasis.reindex`, `StdBasis.transport`.
* Bridge: `toMatOf b : (E →L[𝕜] E) ≃⋆ₐ[𝕜] Matrix ι ι 𝕜`, `toMat 𝕜 E ι`, with
  `@[simp] toMatOf_apply : toMatOf b A i j = ⟪b i, A (b j)⟫_𝕜`,
  `@[simp] toMat_euclideanSpace` (`rfl`), `@[simp] toMatOf_reindex`, `toMat_mk`,
  `toMatOf_eq_toMatrixOrthonormal`.
* Change of basis: `changeOfBasis b b' : Matrix.unitaryGroup ι 𝕜`, `changeOfBasis_star`,
  `toMatOf_conj`, and the workhorse
  `congr_of_unitaryInvariant` / `toMat_congr_of_unitaryInvariant`: *any* `f : Matrix ι ι 𝕜 → X`
  invariant under unitary conjugation is basis-insensitive. This is what makes "prove the matrix
  definition is basis-independent" a one-liner.
* Transfer lemmas: `posSemidef_toMatOf_iff`, `posSemidef_toMatOf_iff_nonneg`,
  `isHermitian_toMatOf_iff`, `trace_toMatOf`.
* Two lemmas contributed to the `ContinuousLinearMap` namespace en route:
  `ContinuousLinearMap.IsPositive.conjStarAlgEquiv` and
  `ContinuousLinearMap.isPositive_conjStarAlgEquiv_iff`. Both are Mathlib-shaped.

### `QuantumInfo/Finite/StdBasisState.lean` (115 lines, compiles clean, no `sorry`)

The end-to-end demonstration on von Neumann entropy:

* `MState.ofOp b A hA htr : MState d` — a positive trace-one operator plus an orthonormal basis
  gives a mixed state.
* `MState.ofOp_basisFun` (`rfl`) — on `EuclideanSpace ℂ d` this *is* the existing matrix state.
* `MState.Sᵥₙ_U_conj` — a lemma the library was missing; immediate from `U_conj_spectrum_eq`.
* `MState.ofOp_eq_U_conj` — changing basis conjugates the state by `changeOfBasis`.
* `MState.Sᵥₙ_ofOp_congr` and `MState.Sᵥₙ_ofOp_congr_instances` — **the insensitivity theorem**,
  proved, in two rewrites.
* `MState.ofOp_reindex`, `MState.Sᵥₙ_ofOp_reindex` — insensitivity to the index type.

Both files pass `scripts/lint-style.py` and produce no Lean warnings.

---

## 4. Migration plan

Sizes below are rough (S ≈ ≤ 1 day, M ≈ 2–4 days, L ≈ 1–2 weeks, XL ≈ ≥ 1 month of focused work).

### Stage 0 — foundations (done; S)

`ForMathlib/StdBasis.lean` + `Finite/StdBasisState.lean`. Already landed and green.

**Remaining Stage-0 items before proceeding:**
1. Decide the `CompleteSpace` question (§2.4). Try a local
   `instance (priority := low) : [FiniteDimensional 𝕜 E] → CompleteSpace E` and measure build time.
   If it is safe, every subsequent stage gets three binders shorter. **Do this first** — it changes
   the shape of every signature written afterwards.
2. Add `StdBasis` instances for `𝕜` itself, `Fin n → 𝕜`, `PiLp 2`, and `Matrix` (Hilbert–Schmidt)
   if downstream needs them. (S)

### Stage 1 — `HermitianMat` becomes an abbreviation (M/L)

Introduce `SelfAdjointOp E := selfAdjoint (E →L[ℂ] E)` alongside `HermitianMat`, with
`HermitianMat d ℂ ≃ SelfAdjointOp (EuclideanSpace ℂ d)` induced by `toMat` (a `≃⋆ₐ`, so it is a
star-order isomorphism). Do **not** yet change `HermitianMat`'s definition.

Order of files, each self-contained:
* `HermitianMat/Order.lean` (627 lines) — port via `posSemidef_toMatOf_iff_nonneg`. Low risk: the
  Loewner order on CLMs is already in Mathlib.
* `HermitianMat/Trace.lean` (245) — needs a real-valued operator trace built on `LinearMap.trace`;
  `trace_toMatOf` is the bridge. `traceLeft`/`traceRight` are **deferred to Stage 4**.
* `HermitianMat/{Sqrt, CFC, Rpow, LogExp, Jordan, NonSingular}.lean` (≈2.6k lines) — these are
  already CFC statements. Expect ~90% to port by changing binders only, because the CFC instances
  on `E →L[ℂ] E` are global. Budget the remaining 10% for eigenvalue-indexed statements.
* `HermitianMat/{Basic, Inner}.lean` (≈1.3k) — `conj B A = B * A * Bᴴ` becomes
  `A ↦ B ∘L A ∘L B†`; `HermitianMat.diagonal` stays basis-dependent and takes a `StdBasis`.
* **Stays matrix-side, unchanged:** `HermitianMat/{Proj, Reindex}.lean`, `Majorization.lean`,
  `MatrixNorm/TraceNorm.lean`, `HermitianMat/Schatten.lean`.

Expected breakage: several hundred proofs across these files, most of them binder-only. Shim: keep
`HermitianMat` as-is and add `@[simp]` bridge lemmas (`toMat_trace`, `toMat_cfc`, `toMat_rpow`, …)
so that downstream files continue to compile untouched.

### Stage 2 — `MState` (L)

* Define `MState' (E) [..] := {A : E →L[ℂ] E // 0 ≤ A ∧ trace A = 1}` and
  `abbrev MState d := MState' (EuclideanSpace ℂ d)`. Because `toMat_euclideanSpace` is `rfl`, this
  abbreviation is defeq-transparent and existing `MState d` code keeps working.
* `MState.m` becomes `StdBasis.toMat _ _ _ ρ.val`, retaining its `@[simp]` lemmas.
* `MState.spectrum` is the hard part: it is `Matrix.IsHermitian.eigenvalues`, which is
  *canonically sorted*, so the value depends on the index type but not the basis. Replace with
  `LinearMap.IsSymmetric.eigenvalues` plus an explicit sort, and prove
  `spectrum_toMat = spectrum` by unitary invariance (`HermitianMat.eigenvalues_conj` already
  exists).
* `Braket.lean` (393 lines): `Ket d`/`Bra d` become vectors in `E` with `‖ψ‖ = 1`. `Ket.basis i`
  requires a `StdBasis` argument. ~51 declarations; most rewrite mechanically, but everything
  coordinatewise (`dot`, `Ket.prod`, `MES`, `uniform_superposition`) needs the basis threaded.

Breakage estimate: `MState.lean` has ~153 declarations; expect ~40 to need real work and the rest
to be binder churn. `Braket.lean` ~15 of 51 need real work.

### Stage 3 — `Unitary`, `Distance`, `Entropy` (M; all but `SSA` and `DPI` done)

These are the payoff stage: every result here is unitarily invariant, so
`StdBasis.congr_of_unitaryInvariant` discharges the insensitivity obligations mechanically, exactly
as demonstrated in `Finite/StdBasisState.lean`.

* `Finite/Unitary.lean` — done. `DensityOp.U_conj` takes a `unitary (E →L[ℂ] E)`; `MState.U_conj`
  is defined from it through `StdBasis.unitaryOfMat`, so all twelve existing `◃` call sites are
  unchanged.
* `Finite/Distance/{TraceDistance, Fidelity}.lean` — done, with the trace norm staying matrix-side
  behind `HermitianOp.traceNorm`.
* `Finite/Entropy/VonNeumann.lean` — done.
* `Finite/Entropy/Relative.lean` — done. The definition is basis-free; the ~1450 lines of existing
  matrix-level machinery below it are untouched, reached through the `coords` transport.
* `Finite/Entropy/SSA.lean` (1293) — not started. Large but shallow: statements about traces, `log`,
  and CFC, almost no coordinate reasoning.
* `Finite/Entropy/DPI.lean` (427) — depends on Stage 4.

### Stage 4 — tensor products and partial trace (L, genuinely hard)

This is the first stage with real mathematical content to write, because **Mathlib has no partial
trace**.

* Build `traceLeft`/`traceRight` on `(E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)` from `LinearMap.trace` and
  `TensorProduct`, and prove they agree with the index-wise matrix definition under `toMat` and
  `instTensorProduct`. Needs a CLM version of `TensorProduct.map` (also missing from Mathlib).
* Reconcile `EuclideanSpace ℂ (d₁ × d₂)` with `EuclideanSpace ℂ d₁ ⊗[ℂ] EuclideanSpace ℂ d₂` via an
  explicit isometry (§2.4). Everything in the library that currently writes `d₁ × d₂` for a
  composite system passes through this.
* Affects: `Finite/Entanglement.lean`, `Finite/Ensemble.lean`, `MState.purify`,
  `MState.prod`/`SWAP`, and the `kron`/Choi machinery in `CPTPMap`.

### Stage 5 — `CPTPMap` (L)

`MatrixMap A B R := Matrix A A R →ₗ[R] Matrix B B R` becomes
`(E →L[ℂ] E) →ₗ[ℂ] (F →L[ℂ] F)`. Roughly 2.9k lines and ~270 declarations across five files.

* `IsTracePreserving`, `Unital`, `IsHermitianPreserving`, `IsPositive` port directly.
* `IsCompletelyPositive`, `choi_matrix`, `of_choi_matrix`, `choi_equiv`, `toMatrix`, `of_kraus`,
  `kron`, `piProd` are all *matrix presentations*. Keep them matrix-side behind `toMat` and add a
  basis-independence theorem for each derived notion (CP-ness, Kraus rank), rather than trying to
  make the Choi matrix itself basis-free. Attempting the latter is the main way this stage could
  blow up.

### Stage 6 — the long tail (L)

`Finite/{Pinching, POVM, Capacity, Qubit}.lean`, `Finite/ResourceTheory/*`. `SteinsLemma.lean`
(2113 lines, but only ~8 top-level declarations, so it is a small number of very long proofs) is
the highest-variance single file: long analytic arguments where one changed definition can require
re-deriving a whole chain. Budget it separately.

### Stage 7 — `QECC/` (M, but *do it last and do it differently*)

The ~3.4k lines under `QECC/` are the intended *beneficiary*, not a victim: Pauli groups,
stabilizer groups, CSS codes and transversal gates are genuinely basis-relative, and the refactor
lets them state that fact instead of hard-coding `EuclideanSpace ℂ (Fin 2)^n`. The work is adding
`[StdBasis ℂ E (Fin 2)]` binders and a `StdBasis` instance for `n`-fold tensor powers, not
rewriting proofs. Should not be started until Stage 4 (tensor products) is solid.

### Total

Stages 1–7 are an XL project: on the order of 3–6 months of focused work, dominated by Stages 1, 2,
5 and 6. The shim strategy (keep `HermitianMat`/`MState` as defeq-transparent abbreviations of the
`EuclideanSpace` case, add `@[simp]` bridge lemmas) means the library can stay green throughout and
the project can be paused after any stage.

---

## 5. Top risks

1. **`CompleteSpace` is not derivable from `FiniteDimensional` by instance search.** Every
   operator-level signature in the library grows binders. Resolve in Stage 0.
2. **No partial trace and no Schatten norms in Mathlib.** These are the two largest genuinely-new
   developments, and they sit under `Entropy`, `Distance` and `CPTPMap`.
3. **`MState.spectrum` is canonically sorted.** It is basis-independent but index-dependent, and
   the sorting is currently supplied by `Matrix.IsHermitian.eigenvalues`; the basis-free spectral
   theorem in Mathlib does not sort.
4. **The Choi matrix is irreducibly a matrix.** Trying to make `CPTPMap` fully basis-free rather
   than stating basis-independence of its consequences is the most likely way Stage 5 overruns.
5. **`SteinsLemma.lean`.** 2113 lines in ~8 declarations; long analytic proofs are brittle under
   definitional change, and there is no way to migrate it incrementally.
