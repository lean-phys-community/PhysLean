# `StdBasis` refactor: scoping, design, and migration plan

Status of this document: Stages 0–3, Stage 5, and the core of Stage 4 have landed.
The branch has since been merged with `master`, which brought Lean `v4.33.0` and its **module
system** (`module` / `public import` / `@[expose] public section`), the `PhysLean` → `Physlib`
rename, the flattening of `QuantumInfo/Finite/` into `States/`, `Channels/`, `Entropy/`,
`Measurements/`, `Operators/` and `Capacity/`, and a completed data processing inequality for the
sandwiched Rényi divergence. All 91 modules under `QuantumInfo/` (45k lines) build with zero errors
and zero warnings, and `QuantumInfo.lean` now imports every one of them, so the default
`lake build` target covers the whole library.

The quantum error correction development lives in the separate `QuantumLib` repository, not here.

Sorries remaining in the parts of the library that are meant to be complete:

| Location | Statement | What it needs |
| --- | --- | --- |
| `Capacity/Capacity.lean:394` | the LSD theorem (achievability of the coherent information) | decoupling / random-coding machinery, none of which exists here |
| `Capacity/Capacity.lean:400` | the regularized capacity formula | follows from the LSD theorem plus the converse |

Two subtrees are works in progress rather than finished developments, and carry sorries by
design: `Entropy/Axiomatized/` (16, the axiomatic characterisation of relative entropy and its
Rényi family) and `ClassicalInfo/Capacity.lean` (4, Shannon's noisy-channel coding theorem).

The sandwiched Rényi DPI no longer needs Riesz–Thorin interpolation. `Entropy/DPI.lean` (1649 lines)
proves it from Stinespring: `sandwichedTraceFunctional_mono_traceRight` gives monotonicity under a
partial trace for `α > 1`, `sandwichedRenyiEntropy_conj_unitary` gives unitary invariance, and
`sandwichedRenyiEntropy_DPI` assembles them through `CPTPOp.prepDefault` and the Stinespring
dilation, with the `α = 1` case recovered as a limit
(`sandwichedRelRentropy_tendsto_qRelativeEnt`). Joint convexity of the relative entropy
(`qRelativeEnt_joint_convexity`) falls out of the same machinery.

The two endpoint contractions that Beigi's interpolation argument would have used are available
anyway, in `MatrixMap.IsPositive`: `traceNorm_le` (a positive trace-preserving map is a trace-norm
contraction, via the Jordan decomposition `X = X⁺ - X⁻` and
`HermitianMat.traceNorm_eq_trace_posPart_add_negPart`) and `mem_Icc_smul_one_of_unital` (a positive
unital map maps the Loewner interval `[-c • 1, c • 1]` into itself, i.e. is an operator-norm
contraction).

* **Stage 0** — `QuantumInfo/ForMathlib/StdBasis.lean` and `QuantumInfo/StdBasisState.lean`.
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

* **Stage 3** — the state-level quantities are now basis-free, each paired with a
  "matrix analogue" theorem that recovers the old matrix formula through an arbitrary `StdBasis`:

  | Basis-free definition | Matrix analogue |
  | --- | --- |
  | `Sᵥₙ (ρ : DensityOp E)` | `Sᵥₙ_eq_trace_cfc_negMulLog`, `Sᵥₙ_eq_re_trace_matrix_cfc` |
  | `TrDistance` | `TrDistance.eq_matrix_traceNorm` |
  | `DensityOp.fidelity` | `DensityOp.fidelity_eq_matrix` |
  | `DensityOp.uConj` | `DensityOp.uConj_M` (and `MState.uConj`, `U ◃ ρ`, on top of it) |
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

  `Entropy/SSA.lean` and `Entropy/DPI.lean` each end in a `basis_free` section that restates their
  headline results for a `DensityOp E`, reducing to the index-level version by choosing an
  arbitrary basis with `StdBasis.some` and transporting: `DensityOp.Sᵥₙ_strong_subadditivity`,
  `Sᵥₙ_subadditivity`, `Sᵥₙ_triangle_subaddivity`, the `qcmi` bounds, and
  `DensityOp.sandwichedRenyiEntropy_DPI` / `DensityOp.qRelativeEnt_DPI`. The bodies of both files
  remain matrix-level, which is the intended end state: the mathematics happens in coordinates and
  the interface does not.

  The one headline result of `Entropy/DPI.lean` with no basis-free counterpart is
  `qRelativeEnt_joint_convexity`. It is stated with `Mixable`, and the only `Mixable` instance is
  `Mixable (HermitianMat d ℂ) (MState d)`; a basis-free statement needs
  `Mixable (HermitianOp E) (DensityOp E)` first, which is new infrastructure rather than a
  restatement.

* **Stage 4 (core)** — the partial trace and the tensor/index bridge exist.

  `QuantumInfo/ForMathlib/PartialTrace.lean` (409 lines) builds the partial trace from scratch, as
  Mathlib has none. `ContinuousLinearMap.traceLeft/traceRight` on `(E ⊗[𝕜] F) →L[𝕜] E ⊗[𝕜] F` are
  defined by summing `tmulLeftL`/`tmulRightL` sandwiches over an orthonormal basis of the traced-out
  factor; a `BasisIndependence` section shows the sum does not depend on that basis, so the
  definition is honest. They are additive, `𝕜`-linear, and preserve symmetry, positivity and the
  trace. `HermitianOp.traceLeft/traceRight` lift this to `HermitianOp`, and `toMat_traceLeft`/
  `toMat_traceRight` are the matrix analogues, landing on `HermitianMat`'s index-wise partial trace.
  `DensityOp.traceLeft/traceRight` follow in `MState.lean`.

  The `EuclideanSpace ℂ (d₁ × d₂)` vs. `EuclideanSpace ℂ d₁ ⊗[ℂ] EuclideanSpace ℂ d₂` reconciliation
  (§2.4) is now available generically. `StdBasis.equiv 𝕜 E F ι` is the isometry matching the two
  preferred bases of spaces sharing an index type, and `DensityOp.transport F ρ` reads a state on any
  such space, with `DensityOp.M_transport` saying the density matrix is unchanged. The general
  workhorse behind all of this is "an isometry carrying preferred basis to preferred basis up to a
  relabelling `σ : ι ≃ κ` relabels the matrix along `σ`", available at each layer as
  `StdBasis.toMat_conjStarAlgEquiv_of_stdBasis`, `HermitianOp.toMat_congr_of_stdBasis` and
  `DensityOp.M_congr_of_stdBasis`. That single lemma identifies the index-level rearrangements with
  the operator-level ones: `MState.SWAP_transport` against `TensorProduct.commIsometry`, and
  `MState.assoc_transport`/`assoc'_transport` against `TensorProduct.assocIsometry`. Partial traces
  commute with `transport` (`MState.traceLeft_transport`, `traceRight_transport`), so `MState.toTensor`
  turns any bipartite `MState (d₁ × d₂)` into a genuine tensor-product state with the same marginals.

  On top of that, `Entropy/VonNeumann.lean` gains the operator-level composite quantities
  `DensityOp.qConditionalEnt`, `DensityOp.qMutualInfo` and `DensityOp.qcmi` — the last stated with
  `assocIsometry.symm` rather than an index permutation — each with its matrix analogue
  (`qConditionalEnt_transport`, `qMutualInfo_transport`, `qcmi_transport`), alongside `Sᵥₙ_transport`.

  Not yet done in Stage 4: `MState.purify`, `MState.prod`, `Ensemble.lean`, `Entanglement.lean`, and
  the `kron`/Choi machinery.

* **Stage 5** — `Channels/OpMap.lean` defines `OpMap E F := (E →L[ℂ] E) →ₗ[ℂ] (F →L[ℂ] F)` with
  `OpMap.toMat`/`OpMap.ofMat` as the bridge to `MatrixMap`, and `Channels/Bundled.lean` carries the
  nine-structure hierarchy `HPOp/UnitalOp/TPOp/POp/CPOp/PTPOp/PUOp/CPTPOp/CPUOp` at the operator
  level, with `abbrev CPTPMap dIn dOut := CPTPOp (EuclideanSpace ℂ dIn) (EuclideanSpace ℂ dOut)`
  (and likewise for the other eight). Every channel constructed from a matrix presentation —
  `of_kraus`, `ofUnitary`, `traceLeft`/`traceRight`, `assoc`, `piProd`, `replacement`, … — is
  `<Class>Op.ofMat <matrixmap> <proofs>` together with a `@[simp]` "matrix analogue" lemma
  `X_map : X.map = <matrixmap>`. Choi matrices and Kraus decompositions stay matrix-side, as
  planned in §4 Stage 5.

  The *action* of a map is basis-free too. `HPOp.opApply` sends a `HermitianOp E` to a
  `HermitianOp F`, `POp.opApply_nonneg` and `PTPOp.trace_opApply` say it preserves positivity and
  the trace, and `PTPOp.applyState` assembles those into the map on states that `PTPOp.instMFunLike`
  installs as the coercion. Neither that instance nor `CPTPOp.instMFunLike` mentions a `StdBasis`
  any more, so `Λ ρ` elaborates for any `Λ : PTPOp E F` and `ρ : DensityOp E`.
  `CPTPOp.transport ι κ` reads a channel as a `CPTPMap ι κ` between the Euclidean spaces of the two
  preferred bases, with `map_transport` (the matrix is unchanged) and `transport_apply` (it commutes
  with transporting states); that is what lets a basis-free statement be discharged by the
  index-level theorem.

Remaining downstream files (`States/{Ensemble,Entanglement}.lean`, `Measurements/POVM.lean`,
`Channels/Pinching.lean`, `Capacity/Capacity.lean`, `ResourceTheory/*`) have been repaired against
the new `DensityOp`/`CPTPOp` API but not yet migrated to operator form; they still speak in matrices
via `ρ.M`. Stages 6 and 7 below are unstarted.

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

### Known ergonomic wart: matrix analogues of basis-free *applications* cannot be `simp` lemmas

A matrix analogue is normally a fine `simp` lemma: `(ρ.transport F).M = ρ.M` has the index type on
both sides, so it is determined by the term being rewritten. But for the action of a map,
`(Λ ρ).M = Λ.map ρ.M`, the *input* index type appears only on the right — nothing in `(Λ ρ).M`
mentions it, now that `PTPOp.instMFunLike` no longer takes a `StdBasis` on the domain. `simp`
then reports "has unassigned metavariables after unification" and silently declines, because it
tries the `[Fintype ι]` subgoal before the `[StdBasis ℂ E ι]` one that would have solved `ι` through
its `outParam`. Worse, the failure is not always quiet: a following `apply` can whnf the unreduced
`applyState` term into a deterministic timeout.

So `PTPOp.M_apply_MState`, `PTPOp.M_applyState` and `HPOp.toMat_opApply` are deliberately *not*
`@[simp]`; apply them with `rw` (or as terms, supplying `ι`). Their docstrings say so.

---

## 1. Reconnaissance

### 1.1 Genuinely basis-dependent vs. basis-free-but-matrix-stated

The library is ~45k lines across 91 files under `QuantumInfo/`. Sorting the content by how it
relates to a choice of basis:

**Genuinely basis-dependent** (a `StdBasis` instance is real input, not bookkeeping):

| Location | What depends on the basis |
| --- | --- |
| `States/Pure/Braket.lean` | `Ket d`/`Bra d` are *functions* `d → ℂ`; `Ket.basis i`, `Ket.MES`, `uniform_superposition`, `Ket.prod` are all defined coordinatewise |
| `States/Mixed/MState.lean` | `MState.ofClassical`, `MState.uniform`, `MState.spectrum` (canonically *sorted* eigenvalues, hence index-dependent), `relabel` |
| `Measurements/POVM.lean` | measurement outcomes indexed by a type; the computational-basis measurement |
| `States/Pure/Qubit.lean` | Pauli matrices, Bloch sphere coordinates |
| `ForMathlib/HermitianMat/Basic.lean` `diagonal`, `Proj.lean`, `Majorization.lean` | diagonal matrices, coordinate projections, majorization of eigenvalue vectors |

**Basis-free in content, matrix-stated in form** (the bulk; this is what a refactor buys):

| Location | Why it is basis-free |
| --- | --- |
| `ForMathlib/HermitianMat/{Order,Trace,Inner,Sqrt,CFC,Rpow,LogExp,Schatten,Jordan,NonSingular}.lean` (≈4.3k lines) | everything is a statement about a self-adjoint element of a C\*-algebra: order, trace, `cfc`, `rpow`, `log`/`exp`, Schatten norms, Jordan product |
| `Entropy/*` (≈2.3k + 1.3k + 0.4k lines) | von Neumann entropy, relative entropy, SSA, DPI: all unitary-invariant spectral functionals |
| `States/Mixed/{TraceDistance,Fidelity}.lean` | trace distance and fidelity are unitarily invariant |
| `Channels/*` (≈4.4k lines) | positivity/complete positivity/trace preservation of a linear map; Choi matrix and Kraus decompositions are matrix-*presentations* of basis-free notions |
| `ResourceTheory/*`, `Channels/Pinching.lean`, `Capacity/Capacity.lean` | consequences of the above |

Rough scale of matrix-level surface: `.mat` appears ~1180 times in 25 files, `Matrix.trace` ~210
times, eigenvalue/spectrum identifiers ~1300 times, kronecker ~445, `submatrix`/`reindex` ~300.

### 1.2 The dependency spine

```
ForMathlib/{Matrix, Isometry, Unitary, LinearEquiv, ContinuousLinearMap}
        └── ForMathlib/HermitianMat/{Basic, Order, Trace, Reindex, Inner, NonSingular,
                                      Sqrt, CFC, Rpow, LogExp, Jordan, Proj, Schatten}
                └── States/Pure/Braket ──┐
                                         ├── States/Mixed/MState ── Operators/Unitary
                                         │    ├── Channels/{OpMap, MatrixMap, Unbundled,
                                         │    │      Bundled, CPTP, Dual, Pinching}
                                         │    ├── Entropy/{VonNeumann, Relative, SSA, DPI}
                                         │    ├── States/Mixed/{TraceDistance, Fidelity}
                                         │    ├── States/{Ensemble, Entanglement},
                                         │    │      Measurements/POVM, Capacity/Capacity
                                         │    └── ResourceTheory/{FreeState,
                                         │           HypothesisTesting, SteinsLemma,
                                         │           ResourceTheory}
                                         └── States/Pure/{Qubit, BlochSphere,
                                                          BargmannInvariant}
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
* **`FiniteDimensional.complete` is a theorem, not an instance.** This was a real ergonomic problem;
  see §2.4 for how it was resolved locally.

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
* **`CompleteSpace`. Resolved.** `FiniteDimensional.complete` is a theorem, not an instance, because
  the scalar field cannot be recovered from the goal `CompleteSpace E`; without completeness the
  C\*-algebra and `Star` structure on `E →L[𝕜] E` do not synthesize. Two local low-priority
  instances remove the problem: `StdBasis.toCompleteSpace` (a `StdBasis 𝕜 E ι` instance pins down
  `𝕜`, so the search terminates) and `FiniteDimensional.toCompleteSpaceComplex` (Mathlib registers
  `FiniteDimensional.proper` only for `𝕜 = ℝ`, so the `ℂ` case needs its own route). Together they
  mean `[CompleteSpace E]` never appears in a signature: `[StdBasis ℂ E ι]` or
  `[FiniteDimensional ℂ E]` alone is enough. `CompleteSpace` is a `Prop`, so the extra routes create
  no diamond, and the build shows no measurable instance-search cost. `CompleteSpace (E ⊗[𝕜] F)`
  is supplied for the general `𝕜` case.

### 2.5 Should `EuclideanSpace ℂ d` be canonical?

Yes, and it is. `StdBasis.toMat 𝕜 (EuclideanSpace 𝕜 d) d = (Matrix.toEuclideanCLM).symm` holds by
`rfl` (`toMat_euclideanSpace`), and `MState.ofOp_basisFun` is likewise `rfl`. That means today's
matrix-level library is *definitionally* the special case `E := EuclideanSpace ℂ d`, so a
compatibility shim `MState d := MState' (EuclideanSpace ℂ d)` will be defeq-transparent rather than
requiring a transport.

### 2.6 Simp normal form: `Matrix d d ℂ` vs `M →L[ℂ] M`

Recommendation: **`E →L[𝕜] E` is the normal form for basis-free statements; matrices are the normal
form only inside genuinely basis-dependent files** (`States/Pure/Qubit.lean`, `Majorization`,
`Proj`, `diagonal`). `StdBasis.toMatOf_apply` is the `@[simp]` lemma that pushes through the bridge when a
matrix entry is genuinely wanted. Do not mark `toMatOf_eq_toMatrixOrthonormal` as `simp`: it should
be used deliberately, not as a rewrite direction.

### 2.7 Cost

`StdBasis` adds one class with one field, resolved by at most two instances per type. The real
cost is not typeclass search, it is the `[NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
[StdBasis 𝕜 E ι] [Fintype ι] [DecidableEq ι]` binder block, which is five binders where today's
code has two (`[Fintype d] [DecidableEq d]`) — `CompleteSpace` and `FiniteDimensional` are now
inferred (§2.4), and a basis-free signature needs only the first two plus
`[FiniteDimensional ℂ E]`. A
`variable` block plus judicious `abbrev`s keeps this tolerable, but it will make every signature in
the library visibly longer. Universes are unproblematic (`E` and `ι` live in independent
universes).

---

## 3. What the prototype contains

### `QuantumInfo/ForMathlib/StdBasis.lean` (588 lines, compiles clean, no `sorry`)

* `class StdBasis`, `export StdBasis (stdBasis)`.
* Instances: `EuclideanSpace.instStdBasis`, `StdBasis.instTensorProduct`,
  `StdBasis.toFiniteDimensional`, `StdBasis.toCompleteSpace`,
  `FiniteDimensional.toCompleteSpaceComplex`, `TensorProduct.instCompleteSpaceOfFiniteDimensional`.
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

### `QuantumInfo/StdBasisState.lean` (114 lines, compiles clean, no `sorry`)

The end-to-end demonstration on von Neumann entropy:

* `MState.ofOp b A hA htr : MState d` — a positive trace-one operator plus an orthonormal basis
  gives a mixed state.
* `MState.ofOp_basisFun` (`rfl`) — on `EuclideanSpace ℂ d` this *is* the existing matrix state.
* `MState.Sᵥₙ_uConj` — a lemma the library was missing; immediate from `uConj_spectrum_eq`.
* `MState.ofOp_eq_uConj` — changing basis conjugates the state by `changeOfBasis`.
* `MState.Sᵥₙ_ofOp_congr` and `MState.Sᵥₙ_ofOp_congr_instances` — **the insensitivity theorem**,
  proved, in two rewrites.
* `MState.ofOp_reindex`, `MState.Sᵥₙ_ofOp_reindex` — insensitivity to the index type.

Both files pass `scripts/lint-style.py` and produce no Lean warnings.

---

## 4. Migration plan

Sizes below are rough (S ≈ ≤ 1 day, M ≈ 2–4 days, L ≈ 1–2 weeks, XL ≈ ≥ 1 month of focused work).

### Stage 0 — foundations (done; S)

`ForMathlib/StdBasis.lean` + `StdBasisState.lean`. Already landed and green.

Both Stage-0 follow-ups are settled:

1. The `CompleteSpace` question (§2.4) is resolved in favour of the local low-priority instances
   `StdBasis.toCompleteSpace` and `FiniteDimensional.toCompleteSpaceComplex`. Nothing in the library
   carries a `[CompleteSpace E]` binder.
2. `StdBasis` instances for `𝕜` itself, `Fin n → 𝕜`, `PiLp 2` and `Matrix` (Hilbert–Schmidt) were
   never needed: everything downstream lives on `EuclideanSpace`, a tensor product, or an abstract
   `E`. Adding them speculatively would only widen the instance search, so the recommendation is to
   add each one when a use site actually appears.

### Stage 1 — `HermitianMat` becomes an abbreviation (M/L)

Introduce `SelfAdjointOp E := selfAdjoint (E →L[ℂ] E)` alongside `HermitianMat`, with
`HermitianMat d ℂ ≃ SelfAdjointOp (EuclideanSpace ℂ d)` induced by `toMat` (a `≃⋆ₐ`, so it is a
star-order isomorphism). Do **not** yet change `HermitianMat`'s definition.

Order of files, each self-contained:
* `HermitianMat/Order.lean` (760 lines) — port via `posSemidef_toMatOf_iff_nonneg`. Low risk: the
  Loewner order on CLMs is already in Mathlib.
* `HermitianMat/Trace.lean` (282) — needs a real-valued operator trace built on `LinearMap.trace`;
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
* `Braket.lean` (452 lines): `Ket d`/`Bra d` become vectors in `E` with `‖ψ‖ = 1`. `Ket.basis i`
  requires a `StdBasis` argument. ~51 declarations; most rewrite mechanically, but everything
  coordinatewise (`dot`, `Ket.prod`, `MES`, `uniform_superposition`) needs the basis threaded.

Breakage estimate: `MState.lean` has ~153 declarations; expect ~40 to need real work and the rest
to be binder churn. `Braket.lean` ~15 of 51 need real work.

### Stage 3 — `Unitary`, `Distance`, `Entropy` (M; done)

These are the payoff stage: every result here is unitarily invariant, so
`StdBasis.congr_of_unitaryInvariant` discharges the insensitivity obligations mechanically, exactly
as demonstrated in `StdBasisState.lean`.

* `Operators/Unitary.lean` — done. `DensityOp.uConj` takes a `unitary (E →L[ℂ] E)`; `MState.uConj`
  is defined from it through `StdBasis.unitaryOfMat`, so all twelve existing `◃` call sites are
  unchanged.
* `States/Mixed/{TraceDistance, Fidelity}.lean` — done, with the trace norm staying matrix-side
  behind `HermitianOp.traceNorm`. `TraceDistance.lean` also gained the data processing inequality
  `TrDistance.DPI_PTP` (for a `PTPOp E F`, matching `Fidelity.lean`'s existing fidelity DPI) with
  `TrDistance.DPI` as the `CPTPOp` corollary. Both are basis-free, since the coercion
  `PTPOp E F → DensityOp E → DensityOp F` no longer needs a `StdBasis` on either side; the proof
  picks bases internally.
* `Entropy/VonNeumann.lean` — done.
* `Entropy/Relative.lean` — done. The definition is basis-free; the ~1450 lines of existing
  matrix-level machinery below it are untouched, reached through the `coords` transport.
  `sandwichedRelRentropy_transport` and `qRelativeEnt_transport` say the two entropies do not see
  which of two spaces sharing an index type the states are read on, which is what makes the
  basis-free statements downstream reducible to the index-level ones.
* `Entropy/SSA.lean` (1520) and `Entropy/DPI.lean` (1649) — done, in the sense described in the
  header: the proofs stay matrix-level and each file ends in a `basis_free` section restating its
  headline results for a `DensityOp E`.

### Stage 4 — tensor products and partial trace (L, genuinely hard; core done)

This is the first stage with real mathematical content to write, because **Mathlib has no partial
trace**.

* Build `traceLeft`/`traceRight` on `(E ⊗[ℂ] F) →L[ℂ] (E ⊗[ℂ] F)` from `LinearMap.trace` and
  `TensorProduct`, and prove they agree with the index-wise matrix definition under `toMat` and
  `instTensorProduct`. **Done**, in `ForMathlib/PartialTrace.lean`; a CLM version of
  `TensorProduct.map` turned out to be unnecessary — summing `tmulLeftL`/`tmulRightL` sandwiches over
  a basis of the traced-out factor avoids it, at the cost of a basis-independence proof.
* Reconcile `EuclideanSpace ℂ (d₁ × d₂)` with `EuclideanSpace ℂ d₁ ⊗[ℂ] EuclideanSpace ℂ d₂` via an
  explicit isometry (§2.4). Everything in the library that currently writes `d₁ × d₂` for a
  composite system passes through this. **Done**, via `StdBasis.equiv` / `DensityOp.transport`, which
  handle any pair of spaces sharing an index type rather than just this one pair; `SWAP` and `assoc`
  are covered too.
* Still to do: `MState.purify`, `MState.prod`, `States/Entanglement.lean`, `States/Ensemble.lean`,
  and the `kron`/Choi machinery in `Channels/`.

### Stage 5 — `Channels/` (L)

`MatrixMap A B R := Matrix A A R →ₗ[R] Matrix B B R` becomes
`(E →L[ℂ] E) →ₗ[ℂ] (F →L[ℂ] F)`. Roughly 4.4k lines and ~270 declarations across six files.

* `IsTracePreserving`, `Unital`, `IsHermitianPreserving`, `IsPositive` port directly.
* `IsCompletelyPositive`, `choi_matrix`, `of_choi_matrix`, `choi_equiv`, `toMatrix`, `of_kraus`,
  `kron`, `piProd` are all *matrix presentations*. Keep them matrix-side behind `toMat` and add a
  basis-independence theorem for each derived notion (CP-ness, Kraus rank), rather than trying to
  make the Choi matrix itself basis-free. Attempting the latter is the main way this stage could
  blow up.

### Stage 6 — the long tail (L)

`Channels/Pinching.lean`, `Measurements/POVM.lean`, `Capacity/Capacity.lean`,
`States/Pure/Qubit.lean`, `ResourceTheory/*`. `SteinsLemma.lean`
(2121 lines, but only ~8 top-level declarations, so it is a small number of very long proofs) is
the highest-variance single file: long analytic arguments where one changed definition can require
re-deriving a whole chain. Budget it separately.

### Stage 7 — the `QuantumLib` error-correction library (M, but *do it last and do it differently*)

The ~10.5k lines of quantum error correction live in the separate `QuantumLib` repository, which
depends on this one. They are the intended *beneficiary* of the refactor, not a victim: Pauli
groups, stabilizer groups, CSS codes and transversal gates are genuinely basis-relative, and the
refactor lets them state that fact instead of hard-coding `EuclideanSpace ℂ (Fin 2)^n`. The work is
adding `[StdBasis ℂ E (Fin 2)]` binders and a `StdBasis` instance for `n`-fold tensor powers, not
rewriting proofs. Should not be started until Stage 4 (tensor products) is solid.

### Total

Stages 1–7 are an XL project: on the order of 3–6 months of focused work, dominated by Stages 1, 2,
5 and 6. The shim strategy (keep `HermitianMat`/`MState` as defeq-transparent abbreviations of the
`EuclideanSpace` case, add `@[simp]` bridge lemmas) means the library can stay green throughout and
the project can be paused after any stage.

---

## 5. Top risks

1. ~~**`CompleteSpace` is not derivable from `FiniteDimensional` by instance search.**~~ Resolved in
   Stage 0 by two local low-priority instances (§2.4); no signature carries `[CompleteSpace E]`.
2. **No partial trace and no Schatten norms in Mathlib.** These are the two largest genuinely-new
   developments, and they sit under `Entropy/`, `States/Mixed/` and `Channels/`. The partial trace has since
   been written (`ForMathlib/PartialTrace.lean`); the Schatten norms remain matrix-side behind
   `HermitianOp.traceNorm`.
3. **`MState.spectrum` is canonically sorted.** It is basis-independent but index-dependent, and
   the sorting is currently supplied by `Matrix.IsHermitian.eigenvalues`; the basis-free spectral
   theorem in Mathlib does not sort.
4. **The Choi matrix is irreducibly a matrix.** Trying to make `CPTPMap` fully basis-free rather
   than stating basis-independence of its consequences is the most likely way Stage 5 overruns.
5. **`SteinsLemma.lean`.** 2121 lines in ~8 declarations; long analytic proofs are brittle under
   definitional change, and there is no way to migrate it incrementally.
