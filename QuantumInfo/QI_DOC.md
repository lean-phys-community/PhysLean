# QuantumInfo Documentation

This document provides a comprehensive overview of mathematical and physical definitions in the
QuantumInfo part of Physlib, explaining the exact conventions adopted, their motivations,
and highlighting key theorems.

---

## Table of Contents

**Part I: Mathematical Preliminaries**
1. [Basic Types and Structures](#basic-types-and-structures)
2. [Hermitian Matrices](#hermitian-matrices)
3. [The Loewner Order](#the-loewner-order)
4. [Continuous Functional Calculus](#continuous-functional-calculus)
5. [Projectors and the Order](#projectors-and-the-order)
6. [Logarithm and Special Functions](#logarithm-and-special-functions)
7. [Other Mathematical Results](#other-mathematical-results)

**Part II: Quantum Information Theory**
8. [Pure States: Bra and Ket](#pure-states-bra-and-ket)
9. [Mixed States: MState](#mixed-states-mstate)
10. [Matrix Maps and Quantum Channels](#matrix-maps-and-quantum-channels)
11. [Entropy and Information Theory](#entropy-and-information-theory)
12. [Named Subsystems and Permutations](#named-subsystems-and-permutations)
13. [Distances and Fidelity](#distances-and-fidelity)
14. [Kronecker Products](#kronecker-products)

**Part III: Reference**
15. [Notations and Scopes](#notations-and-scopes)
16. [Major Theorems](#major-theorems)

---

# Part I: Mathematical Preliminaries

## Basic Types and Structures

### Prob

**`Prob`** is a real number between 0 and 1, representing a probability:

```lean
def Prob := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }
```

**Key operations:**
- **`toReal (p : Prob) : ℝ`**: Extract the underlying real number
- Arithmetic operations when they preserve the bounds
- **`Mixable`** instance: Probabilities form a convex set

### Distribution

**`Distribution α`** on a finite type `α` is a probability distribution:

```lean
def Distribution (α : Type u) [Fintype α] : Type u :=
  { f : α → Prob // Finset.sum Finset.univ (fun i ↦ (f i).toReal) = 1 }
```

A function from `α` to `Prob` whose values sum to 1.

**Key operations:**
- **`uniform : Distribution α`**: The uniform distribution
- **`expect_val`**: Expected value of a function under the distribution
- **`Mixable`** instance: Distributions are convex

---

## Hermitian Matrices

### Definition

**`HermitianMat n 𝕜`** is the type of Hermitian `n × n` matrices over a field `𝕜` (typically `ℂ`):

```lean
def HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))
```

It's defined as the subtype of self-adjoint elements in `Matrix n n α`, which is equivalent to:

```lean
{ M : Matrix n n α // M.IsHermitian }
```

where `M.IsHermitian` means `Mᴴ = M` (conjugate transpose equals itself).

**Key fields and functions:**
- **`mat (A : HermitianMat n α) : Matrix n n α`**: The underlying matrix
- **`H (A : HermitianMat n α)`**: Proof that `A.mat.IsHermitian`
- **Construction**: Use `⟨M, h⟩` where `h : M.IsHermitian`

### Basic Operations

**Algebraic structure:**
- `HermitianMat n α` is an `AddGroup` (inherits from matrices)
- Has `0`, `1` when appropriate
- Addition and subtraction defined componentwise
- Scalar multiplication by **real numbers** (see below)

**Key operations:**
- **`conj (B : Matrix m n α) : HermitianMat n α →+ HermitianMat m α`**:
  Conjugation by a (possibly rectangular) matrix: `A ↦ B * A * Bᴴ`
  - Returns a `HermitianMat m α` (different size!)
  - This is an `AddMonoidHom`

- **`conjLinear (B : Matrix m n α) : HermitianMat n α →ₗ[R] HermitianMat m α`**:
  Same as `conj` but as a linear map (when we have scalar multiplication by `R`)

- **`diagonal (f : n → ℝ) : HermitianMat n 𝕜`**:
  Diagonal matrix with real entries on the diagonal

- **`kronecker (A : HermitianMat m α) (B : HermitianMat n α) : HermitianMat (m × n) α`**:
  Kronecker product. Notation: `A ⊗ₖ B` (scoped to `HermitianMat`)

### The Trace and IsMaximalSelfAdjoint

The trace of a Hermitian matrix has a subtlety related to scalar multiplication.

**The Problem:**
Hermitian matrices over `ℂ` can be viewed as matrices over a **real** vector space (with real scalar multiplication) or over a complex vector space (with complex scalar multiplication). The trace of a Hermitian matrix is **real**, but we want it to be well-behaved with respect to scalar multiplication.

**The `IsMaximalSelfAdjoint` Typeclass:**
This typeclass handles the relationship between the scalar field for matrices (`α = ℂ`) and the scalar field for Hermitian matrices (effectively `ℝ`):

```lean
class IsMaximalSelfAdjoint (R A : Type*) [CommSemiring R] [AddCommGroup A] [Module R A]
    [Star A] [StarAddMonoid A] where
  selfadjMap : selfAdjoint A →ₗ[R] R
```

For `HermitianMat n ℂ`, this provides a way to take real-valued functions (like trace) and make them respect the real scalar structure.

**The Trace Definition:**
```lean
def trace (A : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap (A.mat.trace)
```

This wraps the standard matrix trace to ensure it respects the scalar structure properly. For `ℂ`, this extracts the real part (which equals the full trace since the trace of a Hermitian matrix is real).

**Why this matters:**
- The trace of a Hermitian matrix is always **real**
- We want `trace (r • A) = r • trace A` for **real** `r`
- But `A.mat.trace` is technically in `ℂ`
- `IsMaximalSelfAdjoint` provides the canonical map from the self-adjoint elements to the real scalars

**Key properties:**
- **`trace_eq_re_trace`**: The HermitianMat trace equals the real part of the matrix trace
- **`trace_add`**: `(A + B).trace = A.trace + B.trace`
- **`trace_smul`**: `(r • A).trace = r • A.trace` for real `r`

### Partial Traces

For bipartite systems:

- **`traceLeft (A : HermitianMat (m × n) α) : HermitianMat n α`**:
  Trace out the first subsystem

- **`traceRight (A : HermitianMat (m × n) α) : HermitianMat m α`**:
  Trace out the second subsystem

These operations are crucial for dealing with composite quantum systems.

### Inner Product

Hermitian matrices have a real inner product (the Hilbert-Schmidt inner product):

```lean
⟪A, B⟫ := (A.mat * B.mat).trace.re
```

This is written with double angle brackets and is always **real-valued**.

**Properties:**
- **Bilinearity** (over real scalars)
- **Symmetry**: `⟪A, B⟫ = ⟪B, A⟫`
- **Positive definiteness**: `⟪A, A⟫ ≥ 0` with equality iff `A = 0`
- **Cauchy-Schwarz**: `|⟪A, B⟫| ≤ ⟪A, A⟫^(1/2) * ⟪B, B⟫^(1/2)`

---

## The Loewner Order

### Definition

The **Loewner order** is a partial order on Hermitian matrices:

```lean
A ≤ B  ↔  (B - A).mat.PosSemidef
```

**In words:** `A ≤ B` if and only if `B - A` is positive semidefinite (all eigenvalues ≥ 0, or equivalently, `⟨x, (B-A)x⟩ ≥ 0` for all vectors `x`).

### Implementation

**For HermitianMat:**
- Implemented via `PartialOrder (HermitianMat n 𝕜)` instance
- Always in scope (no need to open a namespace)
- Comes with `IsOrderedAddMonoid` structure

**For Matrix:**
- In the `MatrixOrder` namespace
- Must open with `open MatrixOrder` to use
- Same definition: `A ≤ B ↔ (B - A).PosSemidef`

### Characterizations

Multiple equivalent ways to express the order:

1. **`le_iff`**: `A ≤ B ↔ (B - A).mat.PosSemidef`

2. **`zero_le_iff`**: `0 ≤ A ↔ A.mat.PosSemidef`

3. **`le_iff_mulVec_le`**:
   ```
   A ≤ B ↔ ∀ x, ⟨x, A*x⟩ ≤ ⟨x, B*x⟩
   ```
   (All quadratic forms are ordered)

4. **Via inner product**: `A ≤ B ↔ ∀ C ≥ 0, ⟪C, A⟫ ≤ ⟪C, B⟫`

### Order Properties

**Compatibility with operations:**
- **Addition**: `A ≤ B → A + C ≤ B + C`
- **Scalar multiplication** (nonnegative): `0 ≤ r, A ≤ B → r • A ≤ r • B`
- **Conjugation** (`conj_mono`): `A ≤ B → M*A*Mᴴ ≤ M*B*Mᴴ`
- **Trace** (`trace_mono`): `A ≤ B → A.trace ≤ B.trace`
- **Diagonal** (`diag_mono`): `A ≤ B → ∀ i, A.diag i ≤ B.diag i`
- **Inner product** (`inner_mono`): If `0 ≤ A` and `B ≤ C`, then `⟪A, B⟫ ≤ ⟪A, C⟫`

**Kernels:**
- **`ker_antitone`**: If `0 ≤ A ≤ B`, then `ker(B) ⊆ ker(A)`
  - Larger matrices in Loewner order have smaller kernels

**Convexity:**
- **`convex_cone`**: If `0 ≤ A, B` and `0 ≤ c₁, c₂`, then `0 ≤ c₁•A + c₂•B`
  - The set of positive semidefinite matrices is a convex cone

### Topological Properties

- **`OrderClosedTopology`**: The order relation is closed
  - If `Aₙ ≤ Bₙ` and `Aₙ → A`, `Bₙ → B`, then `A ≤ B`

- **`CompactIccSpace`**: Order intervals are compact
  - The set `{X | A ≤ X ≤ B}` is compact for any `A ≤ B`

### Special Elements

- **`ZeroLEOneClass`**: `0 ≤ 1` in the Loewner order
  - The identity matrix is positive semidefinite

---

## Continuous Functional Calculus

### The CFC Framework

The **continuous functional calculus (CFC)** allows us to apply continuous functions to the eigenvalues of a Hermitian matrix:

```lean
def cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) : HermitianMat d 𝕜
```

**Conceptually:** If `A = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` (spectral decomposition), then:
```
A.cfc f = ∑ᵢ f(λᵢ) |eᵢ⟩⟨eᵢ|
```

**Mathematical basis:** Uses Mathlib's CFC for C*-algebras, specialized to matrices.

### Basic CFC Operations

**Identity and constants:**
- **`cfc_id`**: `A.cfc id = A`
- **`cfc_const`**: `A.cfc (fun _ => c) = c • 1`

**Arithmetic:**
- **`cfc_add`**: `A.cfc (f + g) = A.cfc f + A.cfc g`
- **`cfc_mul`**: `A.cfc (f * g) = A.cfc f * A.cfc g` (when commutative)
- **`cfc_smul`**: `A.cfc (c • f) = c • A.cfc f`
- **`cfc_neg`**: `A.cfc (-f) = -(A.cfc f)`
- **`cfc_sub`**: `A.cfc (f - g) = A.cfc f - A.cfc g`

**Composition:**
- **`cfc_comp`**: `A.cfc (f ∘ g) = (A.cfc g).cfc f` (under appropriate conditions)

**Conjugation:**
- **`cfc_conj_unitary`**: `(A.conj U).cfc f = (A.cfc f).conj U` for unitary `U`

### CFC and the Order

**Monotonicity:**
- **`cfc_le_cfc_of_commute_monoOn`**: If `f` is monotone on `(0, ∞)`, `A` and `B` commute, and are positive definite with `A ≤ B`, then `f(A) ≤ f(B)`

This is crucial for proving operator monotonicity and concavity results.

### Relationship to Diagonal Matrices

For diagonal matrices, the CFC is particularly simple:

**`cfc_diagonal`**:
```
(diagonal 𝕜 d).cfc f = diagonal 𝕜 (f ∘ d)
```

This just applies `f` componentwise to the diagonal entries.

---

## Projectors and the Order

### Definitions

**`proj_le (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜`** (notation `{A ≤ₚ B}`):

```lean
def proj_le (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  (B - A).cfc (fun x ↦ if 0 ≤ x then 1 else 0)
```

Projects onto the eigenspace where `B - A` has non-negative eigenvalues.

**`proj_lt (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜`** (notation `{A <ₚ B}`):

```lean
def proj_lt (A B : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  (B - A).cfc (fun x ↦ if 0 < x then 1 else 0)
```

Projects onto the eigenspace where `B - A` has strictly positive eigenvalues.

**Flipped notations:**
- `{A ≥ₚ B}` = `{B ≤ₚ A}`
- `{A >ₚ B}` = `{B <ₚ A}`

**Note:** The default ordering here uses `≤ₚ`, opposite to some papers that use `≥ₚ` as default.

### Properties

**Idempotency:**
- **`proj_le_sq`**: `{A ≤ₚ B}² = {A ≤ₚ B}`
- **`proj_lt_sq`**: `{A <ₚ B}² = {A <ₚ B}`

These are genuine projectors (satisfy `P² = P`).

**Bounds:**
- **`proj_le_nonneg`**: `0 ≤ {A ≤ₚ B}`
- **`proj_lt_nonneg`**: `0 ≤ {A <ₚ B}`
- **`proj_le_le_one`**: `{A ≤ₚ B} ≤ 1`
- **`proj_lt_le_one`**: `{A <ₚ B} ≤ 1`

**Relationship:**
- **`proj_le_add_lt`**: `{A ≤ₚ B} + {A <ₚ B} ≤ 1` (typically equality when eigenvalues are distinct)
- **`one_sub_proj_le`**: `1 - {B ≤ₚ A} = {A <ₚ B}`

**Special cases:**
- **`proj_zero_le_cfc`**: `{0 ≤ₚ A} = A.cfc (fun x => if 0 ≤ x then 1 else 0)`
  - This is the projector onto the non-negative eigenspace of `A`

**Inner products:**
- **`proj_le_inner_nonneg`**: `0 ≤ ⟪{A ≤ₚ B}, B - A⟫`
- **`proj_le_inner_le`**: `⟪{A ≤ₚ B}, A⟫ ≤ ⟪{A ≤ₚ B}, B⟫`

**Interpretation:** The projector `{A ≤ₚ B}` is the unique maximum projector `P` such that `P * A * P ≤ P * B * P` in the Loewner order.

### Positive and Negative Parts

Related to projectors are the positive and negative parts:

**`posPart (A : HermitianMat d 𝕜) : HermitianMat d 𝕜`** (notation `A⁺`):
```lean
def posPart (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc (fun x => max x 0)
```

**`negPart (A : HermitianMat d 𝕜) : HermitianMat d 𝕜`** (notation `A⁻`):
```lean
def negPart (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc (fun x => max (-x) 0)
```

**Properties:**
- **`posPart_add_negPart`**: `A⁺ - A⁻ = A`
- **`zero_le_posPart`**: `0 ≤ A⁺`
- **`posPart_continuous`**: The map `A ↦ A⁺` is continuous
- **`negPart_continuous`**: The map `A ↦ A⁻` is continuous

---

## Logarithm and Special Functions

### Matrix Logarithm

**Definition:**
```lean
def log (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.log
```

**Crucial convention:** Uses Mathlib's `Real.log`, which satisfies:
- `Real.log 0 = 0`
- `Real.log (-x) = Real.log x` for `x > 0`

### Consequences of the Convention

1. **Works on singular matrices:**
   - If `A` has zero eigenvalues, `A.log` is still defined
   - Zero eigenvalues map to zero

2. **Kernel preservation:**
   - `ker(A) = ker(A.log)`
   - Vectors in the kernel of `A` remain in the kernel of `A.log`

3. **Negation property:**
   - **`log_smul_of_pos`**: For PSD `A` and `x ≠ 0`, `(x • A).log = Real.log x • {0 <ₚ A} + A.log`
   - In particular, for negative `x`, the sign is absorbed by `Real.log`

### Basic Properties

**Special values:**
- **`log_zero`**: `(0 : HermitianMat n 𝕜).log = 0`
- **`log_one`**: `(1 : HermitianMat n 𝕜).log = 0`

**Scaling:**
- **`log_smul`**: For nonsingular `A` and `x ≠ 0`:
  ```
  (x • A).log = Real.log x • 1 + A.log
  ```

**Conjugation:**
- **`log_conj_unitary`**: `(A.conj U).log = A.log.conj U` for unitary `U`
  - The logarithm commutes with unitary conjugation

### Monotonicity

**`log_mono`** (Operator Monotonicity):
If `A, B` are positive definite and `A ≤ B`, then `A.log ≤ B.log`.

**Proof method:** Uses an integral approximation:
```lean
def logApprox (x : HermitianMat n 𝕜) (T : ℝ) : HermitianMat n 𝕜 :=
  ∫ t in (0)..T, ((1 + t)⁻¹ • 1 - (x + t • 1)⁻¹)
```

**Key steps:**
1. **`logApprox_mono`**: The approximation is monotone for each `T`
2. **`tendsto_logApprox`**: As `T → ∞`, `logApprox x T → x.log`
3. Monotonicity is preserved in the limit

### Concavity

**`log_concave`** (Operator Concavity):
For positive definite `A, B` and `a, b ≥ 0` with `a + b = 1`:
```
a • A.log + b • B.log ≤ (a • A + b • B).log
```

**Proof method:** Similar integral approximation:
1. **`logApprox_concave`**: The approximation is concave
2. Take the limit as `T → ∞`

**Related result** — **`inv_antitone`**:
For positive definite `A ≤ B`, we have `B⁻¹ ≤ A⁻¹`.
The matrix inverse is **operator antitone**.

**And** — **`inv_convex`**:
For positive definite `A, B` and convex weights:
```
(a • A + b • B)⁻¹ ≤ a • A⁻¹ + b • B⁻¹
```
The matrix inverse is **operator convex**.

### Kronecker Products

**`log_kron`** (Positive Definite Case):
For positive definite `A : HermitianMat m 𝕜` and `B : HermitianMat n 𝕜`:
```
(A ⊗ₖ B).log = A.log ⊗ₖ 1 + 1 ⊗ₖ B.log
```

**Interpretation:** The logarithm distributes over tensor products (with identity padding).

**`log_kron_with_proj`** (General Case):
For any Hermitian `A, B` (possibly singular):
```
(A ⊗ₖ B).log = (A.log ⊗ₖ B.cfc χ_{≠0}) + (A.cfc χ_{≠0} ⊗ₖ B.log)
```
where `χ_{≠0}` is the indicator function of non-zero eigenvalues: `fun x => if x = 0 then 0 else 1`.

**Why the projectors?** They account for the kernel, ensuring the formula works even when matrices are singular.

### Matrix Exponential

**Definition:**
```lean
def exp (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.exp
```

**Properties:**
- **Positivity**: `0 ≤ A.exp` always (exponential of a Hermitian matrix is PSD)
- **Exponential of zero**: `(0 : HermitianMat n 𝕜).exp = 1`
- **Exponential is always nonsingular**: `A.exp` is always invertible
- **Inverse**: `(A.exp)⁻¹ = (-A).exp`

---

## Other Mathematical Results

### Sion's Minimax Theorem

The library includes a formalization of **Sion's minimax theorem**, a generalization of the classical von Neumann minimax theorem.

**Context:** In classical minimax theory, we want to exchange the order of max and min:
```
max_x min_y f(x, y) ≤ min_y max_x f(x, y)
```
The question is: when does equality hold?

**Von Neumann's theorem:** If `X` and `Y` are compact convex subsets of Euclidean space and `f` is continuous, convex in `x`, and concave in `y`, then equality holds.

**Sion's theorem:** Generalizes to locally convex topological vector spaces. If `X` and `Y` are compact convex sets in locally convex spaces, and `f` is:
- Continuous
- Quasi-convex in `x` for each fixed `y`
- Quasi-concave in `y` for each fixed `x`

Then the minimax equality holds.

**Formalization:** Located in `QuantumInfo/ForMathlib/SionMinimax.lean`

**Key definitions:**
- **`QuasiconvexOn`**: Generalizes convexity
- **`QuasiconcaveOn`**: Generalizes concavity

**The theorem:** States that under appropriate compactness and continuity assumptions, we can exchange sup and inf.

**Why it matters:**
- Used in quantum resource theory for optimization problems
- Essential for capacity formulas
- Provides a general framework for saddle point problems

### Regularization and Limits

The library also formalizes notions of regularized quantities:

**`SupRegularized (fn : ℕ → ℝ) : ℝ`**:
The limit of `fn n / n` as `n → ∞` when it exists, using supremum-based regularization.

**`InfRegularized (fn : ℕ → ℝ) : ℝ`**:
The limit of `fn n / n` as `n → ∞` when it exists, using infimum-based regularization.

**Key theorems:**
- **`mono_sup`**: If `fn` is monotone, the regularization equals the supremum
- **`InfRegularized.of_Subadditive`**: For subadditive sequences, the infimum regularization exists

**Application:** These are used for regularized entropies and channel capacities, where we need `lim_{n→∞} f(n)/n`.

### Superadditivity and Subadditivity

**Definitions:**
```lean
def Superadditive (f : ℕ → ℝ) : Prop := ∀ m n, f m + f n ≤ f (m + n)
def Subadditive (f : ℕ → ℝ) : Prop := ∀ m n, f (m + n) ≤ f m + f n
```

**Key theorems:**
- **`Subadditive.to_Superadditive`**: If `f` is subadditive, then `-f` is superadditive
- **`Superadditive.to_Subadditive`**: If `f` is superadditive, then `-f` is subadditive

**Application:** Quantum channel capacities often exhibit superadditivity or subadditivity, crucial for proving coding theorems.

---

# Part II: Quantum Information Theory

## Pure States: Bra and Ket

### Ket Vectors

**`Ket d`** represents a normalized quantum state as a vector:

```lean
structure Ket (d : Type*) [Fintype d] where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1
```

**Interpretation:** A `Ket d` is a unit vector in the Hilbert space `ℂᵈ`. The `normalized'` field ensures `⟨ψ|ψ⟩ = 1`.

**Notation:** `∣ψ〉` (scoped to `Braket`)

**Function-like behavior:**
- Has `FunLike` instance: can apply to indices
- `ψ i` gives the `i`-th component

**Key operations:**
- **`Ket.prod` (`ψ₁ ⊗ᵠ ψ₂`)**: Tensor product giving `Ket (d₁ × d₂)`
  - Defined as: `(ψ₁ ⊗ᵠ ψ₂) (i, j) = ψ₁ i * ψ₂ j`

- **`uniform_superposition : Ket d`**: The equal superposition `|+⟩ = (1/√d) ∑ᵢ |i⟩`

### Bra Vectors

**`Bra d`** is defined identically to `Ket d`:

```lean
structure Bra (d : Type*) [Fintype d] where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1
```

**Why separate from Ket?** To avoid confusion with complex conjugation. In quantum mechanics, bras and kets are related by conjugate transpose, but we want to make this explicit.

**Notation:** `〈ψ∣` (scoped to `Braket`)

**Conversion:**
- **`Ket.to_bra (ψ : Ket d) : Bra d`**: Componentwise conjugation
- **`Bra.to_ket (ψ : Bra d) : Ket d`**: Componentwise conjugation

### Inner Product

**`dot (ξ : Bra d) (ψ : Ket d) : ℂ`**:
```lean
def dot (ξ : Bra d) (ψ : Ket d) : ℂ := ∑ x, (ξ x) * (ψ x)
```

**Notation:** `〈ξ‖ψ〉` (scoped to `Braket`)

**Note:** This is the "mixed" form where we don't automatically conjugate. To get the standard inner product `⟨φ|ψ⟩`, use `〈φ.to_bra‖ψ〉`.

**Properties:**
- **Linearity** (in the second argument)
- **`dot_self_nonneg`**: `〈ψ.to_bra‖ψ〉` is real and non-negative
- **Normalization**: `〈ψ.to_bra‖ψ〉 = 1` for any ket `ψ`

### Design Philosophy

**Why not use Mathlib's Hilbert spaces directly?**

The library uses basis-dependent vectors (`d → ℂ`) rather than abstract Hilbert spaces because:

1. **Computational basis is canonical** in quantum information theory
2. **Classical limit** is obvious: diagonal elements correspond to classical probabilities
3. **Explicit finite dimension** makes many proofs simpler
4. **Connection to matrices** is straightforward

The trade-off is that we don't get basis-independent formulations, but this is usually not needed in finite-dimensional quantum information theory.

---

## Mixed States: MState

### Definition

**`MState d`** is a mixed quantum state (density matrix):

```lean
structure MState (d : Type*) [Fintype d] [DecidableEq d] where
  M : HermitianMat d ℂ
  zero_le : 0 ≤ M
  tr : M.trace = 1
```

**Interpretation:** A positive semidefinite Hermitian matrix with trace 1. Represents a statistical ensemble of pure states.

**Key fields:**
- **`M`**: The underlying `HermitianMat d ℂ`
- **`m`**: The underlying `Matrix d d ℂ` (lowercase)
- **`zero_le`**: Proof that `M` is PSD (equivalently, all eigenvalues ≥ 0)
- **`tr`**: Proof that `trace(M) = 1`

### Constructing MStates

**From pure states:**
```lean
def pure (ψ : Ket d) : MState d
```
Creates the rank-1 projector `|ψ⟩⟨ψ|`.

**Properties:**
- `pure ψ` is PSD with a single non-zero eigenvalue (equal to 1)
- `(pure ψ).m = vecMulVec ψ (ψ : Bra d)`
- `(pure ψ).purity = 1`

**From classical distributions:**
```lean
def ofClassical (dist : Distribution d) : MState d
```
Embeds a probability distribution as a diagonal density matrix.

**Properties:**
- `(ofClassical dist).m = diagonal (fun i => dist i)`
- Represents classical mixture with no quantum coherence
- Commutes with all matrices in the computational basis

**Uniform state:**
```lean
def uniform : MState d := ofClassical Distribution.uniform
```
The maximally mixed state `I/d`.

**Properties:**
- `uniform.m = (1/d) • 1`
- Maximum entropy: `Sᵥₙ uniform = log d`
- Minimum purity: `purity uniform = 1/d`

### Basic Properties

**Spectrum:**
```lean
def spectrum (ρ : MState d) : Distribution d
```
The eigenvalues of `ρ`, viewed as a probability distribution.

**Key facts:**
- Eigenvalues are non-negative (from `zero_le`)
- Eigenvalues sum to 1 (from `tr`)
- Entropy can be computed from spectrum: `Sᵥₙ ρ = Hₛ (ρ.spectrum)`

**Purity:**
```lean
def purity (ρ : MState d) : Prob := ⟪ρ, ρ⟫
```
Measures how "pure" a state is:
- `purity ρ = 1` iff `ρ` is a pure state
- `purity ρ = 1/d` for the uniform state
- Equivalently: `Tr[ρ²]`

**Eigenvalue bounds:**
- **`eigenvalue_nonneg`**: All eigenvalues are non-negative
- **`eigenvalue_le_one`**: All eigenvalues are at most 1
- **`le_one`**: `ρ.M ≤ 1` in the Loewner order

### Tensor Products

**`prod` (`ρ₁ ⊗ᴹ ρ₂`)**:
For `ρ₁ : MState d₁` and `ρ₂ : MState d₂`, gives `MState (d₁ × d₂)`.

```lean
def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂)
```

**Properties:**
- `(ρ₁ ⊗ᴹ ρ₂).m = ρ₁.m ⊗ₖ ρ₂.m` (Kronecker product of matrices)
- Product of pure states: `pure ψ₁ ⊗ᴹ pure ψ₂ = pure (ψ₁ ⊗ᵠ ψ₂)`
- **`prod_inner_prod`**: `⟪ρ₁ ⊗ᴹ ρ₂, σ₁ ⊗ᴹ σ₂⟫ = ⟪ρ₁, σ₁⟫ * ⟪ρ₂, σ₂⟫`

**n-fold products:**
```lean
def npow (ρ : MState d) (n : ℕ) : MState (Fin n → d)
```
Notation: `ρ ⊗ᴹ^ n`

Creates `n` identical copies on the product space.

### Partial Traces

For bipartite states `ρ : MState (d₁ × d₂)`:

**`traceLeft ρ : MState d₂`**: Reduces to second subsystem
```lean
def traceLeft (ρ : MState (d₁ × d₂)) : MState d₂
```
Mathematically: `ρ_B = Tr_A[ρ_{AB}] = ∑ᵢ ⟨i|ρ|i⟩_A` where the trace is over the first subsystem.

**`traceRight ρ : MState d₁`**: Reduces to first subsystem
```lean
def traceRight (ρ : MState (d₁ × d₂)) : MState d₁
```
Mathematically: `ρ_A = Tr_B[ρ_{AB}]`

**Properties:**
- **Linearity**: Both are linear maps
- **Composition**: `ρ.traceLeft.traceLeft` makes sense for tripartite systems
- **With SWAP**: `ρ.SWAP.traceLeft = ρ.traceRight`

### Subsystem Manipulation

**SWAP:**
```lean
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm
```

Exchanges the two subsystems.

**Properties:**
- **`SWAP_SWAP`**: `ρ.SWAP.SWAP = ρ`
- **`traceLeft_SWAP`**: `ρ.SWAP.traceLeft = ρ.traceRight`
- **`spectrum_SWAP`**: Eigenvalues preserved (up to relabeling)

**Associators:**
```lean
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃)
def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃)
```

**Properties:**
- **`assoc_assoc'`**: `ρ.assoc'.assoc = ρ`
- **`assoc'_assoc`**: `ρ.assoc.assoc' = ρ`
- **`traceRight_assoc`**: `ρ.assoc.traceRight = ρ.traceRight.traceRight`

### Purification

**`purify (ρ : MState d) : Ket (d × d)`**:

Produces a pure state `|Ψ⟩` on an enlarged space such that tracing out half gives back `ρ`.

```lean
def purify (ρ : MState d) : Ket (d × d)
```

**Key theorem:**
- **`traceRight_of_purify`**: `(pure ρ.purify).traceRight = ρ`

This is the **purification theorem**: every mixed state has a purification.

### Unitary Conjugation

**`U_conj (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) : MState d`**:

Applies unitary transformation: `ρ ↦ U ρ U†`.

**Notation:** `U ◃ ρ` (scoped to `MState`)

**Properties:**
- Preserves all eigenvalues
- Preserves entropy: `Sᵥₙ (U ◃ ρ) = Sᵥₙ ρ`
- Preserves purity: `purity (U ◃ ρ) = purity ρ`

### Relabeling

**`relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : MState d₂`**:

Changes the index type via an equivalence. The underlying matrix gets permuted.

**Properties:**
- **`spectrum_relabel_eq`**: Multiset of eigenvalues preserved
- **`relabel_kron`**: Commutes with tensor products (appropriately)

### Topology and Convexity

**Topological structure:**
- **`CompactSpace (MState d)`**: The space of states is compact
- **`MetricSpace (MState d)`**: Inherits metric from Hermitian matrices
- **`BoundedSpace (MState d)`**: All states are within bounded distance

**Convexity:**
- **`instMixable`**: MStates have a `Mixable` instance
- **`convex`**: The set of MStates is convex in the ambient space

**Interpretation:** Quantum states form a compact convex set (the **Bloch ball** in 2D).

---

## Matrix Maps and Quantum Channels

### MatrixMap: The Base Type

```lean
abbrev MatrixMap (A B R : Type*) [Semiring R] := Matrix A A R →ₗ[R] Matrix B B R
```

A `MatrixMap A B R` is a linear map from `A×A` matrices to `B×B` matrices over `R`.

**Philosophy:** We view quantum channels as linear maps on the space of matrices, not on the space of states. This is more general and makes the theory cleaner.

### Choi Matrix Representation

Every matrix map has two representations:

1. **As a linear map** (the definition)
2. **Via the Choi matrix**

**`choi_matrix (M : MatrixMap A B R) : Matrix (B × A) (B × A) R`**:
```lean
def choi_matrix (M : MatrixMap A B R) : Matrix (B × A) (B × A) R :=
  fun (j₁,i₁) (j₂,i₂) ↦ M (Matrix.single i₁ i₂ 1) j₁ j₂
```

**Interpretation:** Apply the map to all elementary matrices and collect results.

**`of_choi_matrix (M : Matrix (B × A) (B × A) R) : MatrixMap A B R`**:

Inverse operation: given a matrix, construct the corresponding map.

**Key theorems:**
- **`choi_map_inv`**: `of_choi_matrix (choi_matrix M) = M`
- **`map_choi_inv`**: `choi_matrix (of_choi_matrix M) = M`
- **`choi_equiv`**: These form a linear equivalence

**Transfer matrix:** There's also a `toMatrix` function giving the "transfer matrix" representation (different from Choi).

### Kraus Representation

**`of_kraus (M N : κ → Matrix B A R)`**:

Constructs the map `X ↦ ∑ₖ Mₖ * X * Nₖᴴ`.

**Key fact:** Every CPTP map has a Kraus representation.

### The Hierarchy: Unbundled Properties

These are **propositions** about matrix maps:

**1. Trace Preserving:**
```lean
def IsTracePreserving (M : MatrixMap A B R) : Prop :=
  ∀ (x : Matrix A A R), (M x).trace = x.trace
```

**Equivalent characterization:**
- **`IsTracePreserving_iff_trace_choi`**: `M.IsTracePreserving ↔ M.choi_matrix.traceLeft = 1`

**Key theorems:**
- **`IsTracePreserving.comp`**: Composition preserves TP
- **`IsTracePreserving.kron`**: Tensor products preserve TP
- **`IsTracePreserving.of_kraus_isTracePreserving`**: Kraus form is TP iff `∑ₖ Nₖᴴ Mₖ = I`

**2. Unital:**
```lean
def Unital (M : MatrixMap A B R) : Prop := M 1 = 1
```

Maps identity to identity.

**3. Hermitian Preserving:**
```lean
def IsHermitianPreserving (M : MatrixMap A B 𝕜) : Prop :=
  ∀ {x}, x.IsHermitian → (M x).IsHermitian
```

**4. Positive:**
```lean
def IsPositive (M : MatrixMap A B 𝕜) : Prop :=
  ∀ {x}, x.PosSemidef → (M x).PosSemidef
```

Maps PSD matrices to PSD matrices.

**5. Completely Positive:**
```lean
def IsCompletelyPositive (M : MatrixMap A B 𝕜) : Prop :=
  ∀ (n : ℕ), (M ⊗ₖₘ MatrixMap.id (Fin n) 𝕜).IsPositive
```

Positive even when tensored with identity maps.

**Key theorem:**
- **`choi_PSD_iff_CP_map`** (Choi's Theorem): `M.IsCompletelyPositive ↔ M.choi_matrix.PosSemidef`

### The Hierarchy: Bundled Structures

These **bundle** a map with proofs of properties:

**1. HPMap (Hermitian Preserving):**
```lean
structure HPMap extends MatrixMap dIn dOut 𝕜 where
  HP : MatrixMap.IsHermitianPreserving toLinearMap
```

- Has `FunLike` instance: can apply to `HermitianMat`
- **`funext_mstate`**: Two HP maps are equal if they agree on all `MState`s

**2. TPMap (Trace Preserving):**
```lean
structure TPMap extends MatrixMap dIn dOut R where
  TP : MatrixMap.IsTracePreserving toLinearMap
```

**3. UnitalMap:**
```lean
structure UnitalMap extends MatrixMap dIn dOut R where
  unital : MatrixMap.Unital toLinearMap
```

**4. PMap (Positive):**
```lean
structure PMap extends HPMap dIn dOut 𝕜 where
  pos : MatrixMap.IsPositive toLinearMap
```

Note: Extends `HPMap` (positive maps are automatically Hermitian preserving).

**5. CPMap (Completely Positive):**
```lean
structure CPMap extends PMap dIn dOut 𝕜 where
  cp : MatrixMap.IsCompletelyPositive toLinearMap
```

**6. PTPMap (Positive Trace Preserving):**
```lean
structure PTPMap extends PMap dIn dOut 𝕜, TPMap dIn dOut 𝕜
```

Combines positivity and trace preservation.

**7. PUMap (Positive Unital):**
```lean
structure PUMap extends PMap dIn dOut 𝕜, UnitalMap dIn dOut 𝕜
```

Dual notion to PTP.

**8. CPTPMap (Completely Positive Trace Preserving):**
```lean
structure CPTPMap extends PTPMap dIn dOut, CPMap dIn dOut where
```

**The main object:** Quantum channels. Over `ℂ` by default.

**9. CPUMap (Completely Positive Unital):**
```lean
structure CPUMap extends CPMap dIn dOut 𝕜, PUMap dIn dOut 𝕜
```

Dual to CPTP: maps observables (Hermitian matrices) in the opposite direction.

### CPTPMap: Quantum Channels

**`CPTPMap dIn dOut`** represents a quantum channel.

**Key operations:**
- **`id : CPTPMap dIn dIn`**: Identity channel
- **`compose` (`M₂ ∘ₘ M₁`)**: Sequential composition
- **`prod` (`M₁ ⊗ₖ M₂`)**: Parallel composition (tensor product)
- **`CPTP_of_choi_PSD_Tr`**: Construct from Choi matrix

**Important examples:**
- **`of_unitary (U : Matrix.unitaryGroup d ℂ)`**: The unitary channel `ρ ↦ U ρ U†`
- **`replacement (σ : MState dOut)`**: Constant channel outputting `σ`
- **`SWAP : CPTPMap (d₁ × d₂) (d₂ × d₁)`**: Swaps subsystems
- **`assoc : CPTPMap ((d₁ × d₂) × d₃) (d₁ × d₂ × d₃)`**: Reassociates
- **`traceLeft : CPTPMap (d₁ × d₂) d₂`**: Partial trace as a channel
- **`traceRight : CPTPMap (d₁ × d₂) d₁`**: Partial trace as a channel

**Function-like behavior:**
- Has `FunLike` instance when `DecidableEq dOut`
- Can apply to states: `Λ ρ : MState dOut` for `ρ : MState dIn`

**Extensionality:**
- **`funext`**: Two channels are equal if they agree on all states

**State-Channel Correspondence:**
- **`choi_MState_iff_CPTP`**: Bijection between `CPTPMap dIn dOut` and `MState (dIn × dOut)`
- This is the **Choi-Jamiołkowski isomorphism**

**Mixability:**
- **`instMixable`**: Channels are convex (via Choi matrices)
- Can take convex combinations of channels

### Duality

**`dual (M : MatrixMap A B 𝕜) : MatrixMap B A 𝕜`**:

The adjoint map with respect to the Hilbert-Schmidt inner product.

**Defining property:** `Tr[M(X) * Y] = Tr[X * M.dual(Y)]`

**Key theorems:**
- **`IsCompletelyPositive.dual`**: CP maps have CP duals
- **`dual_kron`**: `(M ⊗ₖₘ N).dual = M.dual ⊗ₖₘ N.dual`
- **`dual_id`**: `(MatrixMap.id A 𝕜).dual = MatrixMap.id A 𝕜`

**Interpretation:** The dual map acts on observables in the "backwards" direction.

---

## Entropy and Information Theory

### Von Neumann Entropy

```lean
def Sᵥₙ (ρ : MState d) : ℝ := Hₛ (ρ.spectrum)
```

The von Neumann entropy, defined via the Shannon entropy of the eigenvalue distribution:
```
S(ρ) = -∑ᵢ λᵢ log λᵢ
```

**Properties:**
- **`Sᵥₙ_nonneg`**: `0 ≤ Sᵥₙ ρ`
- **`Sᵥₙ_le_log_d`**: `Sᵥₙ ρ ≤ log(d)` with equality for uniform state
- **Concavity:** Von Neumann entropy is concave
- **Unitary invariance:** `Sᵥₙ (U ◃ ρ) = Sᵥₙ ρ`
- **Subadditivity:** `Sᵥₙ ρ ≤ Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight`

### Conditional Entropy

```lean
def qConditionalEnt (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ - Sᵥₙ ρ.traceLeft
```

Quantum conditional entropy: `S(A|B) = S(ρ_{AB}) - S(ρ_B)`.

**Key difference from classical:** Can be **negative** (indicates entanglement).

**Interpretation:**
- Negative conditional entropy means the joint system has less uncertainty than subsystem B alone
- This is impossible classically but common for entangled quantum states

### Mutual Information

```lean
def qMutualInfo (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ
```

Quantum mutual information: `I(A:B) = S(ρ_A) + S(ρ_B) - S(ρ_{AB})`.

**Properties:**
- **Non-negativity:** `0 ≤ qMutualInfo ρ`
- **Symmetry:** `qMutualInfo ρ = qMutualInfo ρ.SWAP`
- Measures total correlations (classical + quantum)

**Relationship to relative entropy:**
- **`qMutualInfo_as_qRelativeEnt`**: `I(A:B) = 𝐃(ρ_{AB} ‖ ρ_A ⊗ ρ_B)`

### Conditional Mutual Information

```lean
def qcmi (ρ : MState (dA × dB × dC)) : ℝ :=
  qConditionalEnt ρ.assoc'.traceRight - qConditionalEnt ρ
```

Quantum conditional mutual information: `I(A;C|B) = S(A|B) - S(A|BC)`.

**Physical meaning:** Information about `A` contained in `C`, given knowledge of `B`.

**Key theorem:**
- **`Sᵥₙ_weak_monotonicity`**: Related to strong subadditivity

### Coherent Information

```lean
def coherentInfo (ρ : MState d₁) (Λ : CPTPMap d₁ d₂) : ℝ :=
  -qConditionalEnt (Λ.prod CPTPMap.id (pure ρ.purify))
```

The coherent information of `ρ` through channel `Λ`.

**Physical meaning:** Maximum rate at which quantum information can be transmitted through `Λ`.

**Connection to capacity:** Related to the quantum capacity of the channel.

### Relative Entropy

```lean
def qRelativeEnt (ρ σ : MState d) : EReal := D̃_1(ρ‖σ)
```

**Notation:** `𝐃(ρ‖σ)`

The quantum relative entropy (also called quantum Kullback-Leibler divergence):
```
𝐃(ρ‖σ) = Tr[ρ (log ρ - log σ)]
```

When supports are compatible, otherwise `+∞`.

**Properties:**
- **Non-negativity:** `0 ≤ 𝐃(ρ‖σ)` with equality iff `ρ = σ` (quantum Pinsker)
- **`qRelativeEnt_additive`**: `𝐃(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂)`
- **`qRelativeEnt_joint_convexity`**: Jointly convex in `(ρ, σ)`
- **Data processing inequality:** `𝐃(Λ ρ‖Λ σ) ≤ 𝐃(ρ‖σ)` for any CPTP `Λ`

**Relationship to mutual information:**
Mutual information is relative entropy to the product state:
```
I(A:B) = 𝐃(ρ_{AB} ‖ ρ_A ⊗ ρ_B)
```

### Sandwiched Rényi Relative Entropy

```lean
def SandwichedRelRentropy (α : ℝ) (ρ σ : MState d) : EReal
```

**Notation:** `D̃_α(ρ‖σ)`

A family of relative entropies parameterized by `α ∈ [0, ∞]`:
```
D̃_α(ρ‖σ) = (1/(α-1)) log Tr[(σ^((1-α)/(2α)) ρ σ^((1-α)/(2α)))^α]
```

**Special cases:**
- `α = 1`: Quantum relative entropy `𝐃(ρ‖σ)` (defined as limit)
- `α = 1/2`: Related to fidelity
- `α → ∞`: Min-relative entropy

**Properties:**
- **`sandwichedRelRentropy_additive`**: `D̃_α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_α(ρ₁‖σ₁) + D̃_α(ρ₂‖σ₂)`
- Monotone in `α`
- Data processing inequality

---

## Named Subsystems and Permutations

### The Subsystem Problem

**The issue:** In standard quantum information notation, we write:
- `ρ_{ABC}` for a tripartite state
- `ρ_{AC}` after tracing out `B`
- `I(A:C|B)` for conditional mutual information

This treats subsystems by **name**.

**In Lean:** A type like `MState (dA × dB × dC)` is actually `MState (dA × (dB × dC))` due to right-associativity of `×`.

**Consequence:** Partial traces act on the outermost split. We can directly talk about:
- The partition `dA` vs `(dB × dC)`
- But **not** directly about `dA × dC` vs `dB`

### Solution: Explicit Permutations

To access different bipartitions, we use explicit permutation functions.

**SWAP:**
```lean
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm
```

Exchanges two subsystems.

**Properties:**
- **`SWAP_SWAP`**: `ρ.SWAP.SWAP = ρ` (involutive)
- **`traceLeft_SWAP`**: `ρ.SWAP.traceLeft = ρ.traceRight`
- **`traceRight_SWAP`**: `ρ.SWAP.traceRight = ρ.traceLeft`
- **`spectrum_SWAP`**: Eigenvalues preserved up to relabeling

**Associators:**
```lean
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃) :=
  ρ.relabel (Equiv.prodAssoc d₁ d₂ d₃).symm

def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃) :=
  ρ.SWAP.assoc.SWAP.assoc.SWAP
```

Change the grouping of a tripartite system.

**Properties:**
- **`assoc_assoc'`**: `ρ.assoc'.assoc = ρ`
- **`assoc'_assoc`**: `ρ.assoc.assoc' = ρ`
- **`traceRight_assoc`**: `ρ.assoc.traceRight = ρ.traceRight.traceRight`
- **`traceLeft_assoc'`**: `ρ.assoc'.traceLeft = ρ.traceLeft.traceLeft`
- **`traceLeft_right_assoc`**: `ρ.assoc.traceLeft.traceRight = ρ.traceRight.traceLeft`

### Example: Computing S(A|C)

**Setup:** We have `ρ : MState (dA × dB × dC)` which is really `dA × (dB × dC)`.

**Goal:** Compute `S(A|C)` = conditional entropy of `A` given `C`, ignoring `B`.

**Challenge:** We need access to the bipartition `(dA × dC)` vs `dB`, but our type structure doesn't give this directly.

**Method:**
1. Use `SWAP` and `assoc` to rearrange: move subsystems so `A` and `C` are adjacent
2. Apply partial traces to get `ρ_{AC}`
3. Compute conditional entropy on the result

**Current state:** Entropy inequalities explicitly use these permutations in their statements.

**Future direction:** A more flexible "named subsystems" API is desired but not yet implemented.

### Channel Versions

All permutations exist as CPTPMap channels:

- **`CPTPMap.SWAP : CPTPMap (d₁ × d₂) (d₂ × d₁)`**
- **`CPTPMap.assoc : CPTPMap ((d₁ × d₂) × d₃) (d₁ × d₂ × d₃)`**
- **`CPTPMap.assoc' : CPTPMap (d₁ × d₂ × d₃) ((d₁ × d₂) × d₃)`**
- **`CPTPMap.traceLeft : CPTPMap (d₁ × d₂) d₂`**
- **`CPTPMap.traceRight : CPTPMap (d₁ × d₂) d₁`**

**Consistency:** These satisfy `CPTPMap.SWAP ρ = ρ.SWAP`, etc.

---

## Distances and Fidelity

### Trace Distance

```lean
def TrDistance (ρ σ : MState d) : ℝ :=
  (1/2) * (ρ.m - σ.m).traceNorm
```

The **trace distance** between states: `D(ρ, σ) = (1/2) ‖ρ - σ‖₁`.

**Interpretation:** The trace norm `‖A‖₁ = Tr[√(A†A)]` is the sum of singular values.

**Properties:**
- **Bounds:** `0 ≤ TrDistance ρ σ ≤ 1`
- **`TrDistance.prob`**: Can be bundled as a `Prob`
- **Metric:** Forms a metric on `MState d`
- **Contractivity:** `TrDistance (Λ ρ) (Λ σ) ≤ TrDistance ρ σ` for CPTP `Λ`
  - Channels cannot increase distinguishability

**Physical meaning:** Optimal success probability in distinguishing `ρ` from `σ` using any measurement.

### Fidelity

```lean
def Fidelity (ρ σ : MState d) : ℝ
```

The **fidelity** between states: `F(ρ, σ) = Tr[√(√ρ σ √ρ)]`.

**Alternative definition (via purifications):** Maximum overlap between purifications of `ρ` and `σ`.

**Properties:**
- **Bounds:** `0 ≤ Fidelity ρ σ ≤ 1`
- **`Fidelity.prob`**: Can be bundled as a `Prob`
- **Symmetry:** `Fidelity ρ σ = Fidelity σ ρ`
- **Monotonicity:** `Fidelity (Λ ρ) (Λ σ) ≥ Fidelity ρ σ` for CPTP `Λ`
  - Opposite direction from trace distance!

**Physical meaning:** Measures "closeness" of quantum states, with different operational interpretation than trace distance.

**Uhlmann's theorem:** The fidelity is achieved by optimal choice of purifications.

### Relationships

The trace distance and fidelity are related by various inequalities:

**Fuchs-van de Graaf inequalities:**
```
1 - F(ρ, σ) ≤ D(ρ, σ) ≤ √(1 - F(ρ, σ)²)
```

These relate the two fundamental distance measures in quantum information theory.

---

## Kronecker Products

### Overview

Kronecker products (tensor products) are fundamental in quantum information theory. The library defines them for many types, using different notations to avoid ambiguity.

**Key convention:** The product of types `d₁` and `d₂` has type `d₁ × d₂` (Cartesian product in Lean's type system).

### Product Notations by Type

| Type | Notation | Input Types | Output Type | Scope |
|------|----------|-------------|-------------|-------|a
| **Matrix** | `⊗ₖ` | `Matrix A B R`, `Matrix C D R` | `Matrix (A×B) (C×D) R` | `Kronecker` |
| **Ket** | `⊗ᵠ` | `Ket d₁`, `Ket d₂` | `Ket (d₁ × d₂)` | default |
| **MState** | `⊗ᴹ` | `MState d₁`, `MState d₂` | `MState (d₁ × d₂)` | default |
| **HermitianMat** | `⊗ₖ` | `HermitianMat m 𝕜`, `Hermitia(nMat n 𝕜` | `HermitianMat (m × n) 𝕜` | `HermitianMat` |
| **CPTPMap** | `⊗ᶜᵖ` | `CPTPMap dIn₁ dOut₁`, `CPTPMap dIn₂ dOut₂` | `CPTPMap (dIn₁×dIn₂) (dOut₁×dOut₂)` | default |
| **MatrixMap** | `⊗ₖₘ` | `MatrixMap A B R`, `MatrixMap C D R` | `MatrixMap (A×C) (B×D) R` | `MatrixMap` |
| **Unitary** | `⊗ᵤ` | Unitary, Unitary | Unitary on product | `Matrix` |
| **Categorical** | `⊗ᵣ` | `MState (H i)`, `MState (H j)` | MState (H (i * j)) | `ResourcePretheory` |

The first of these, for bare matrices, comes from Mathlib. The last of these is used in the context of quantum resource theories (or, more generally, categorical quantum mechanics) where there is a _product isomorphism_; this product gives a state on the corresponding Hilbert space identified by the category, as opposed to a Hilbert space indexed by Lean's `Prod` type.

**Why different notations?**
- Avoids ambiguity when multiple products are in scope
- Makes code more readable
- Each notation is tailored to its domain

### Properties

**Linearity:** All products are (bi)linear.

**Associativity:** Products are associative up to canonical isomorphism:
```
(ρ₁ ⊗ᴹ ρ₂) ⊗ᴹ ρ₃  ≅  ρ₁ ⊗ᴹ (ρ₂ ⊗ᴹ ρ₃)
```
But they live in different types: `((d₁ × d₂) × d₃)` vs `(d₁ × (d₂ × d₃))`.

**For pure states:**
```
pure ψ₁ ⊗ᴹ pure ψ₂ = pure (ψ₁ ⊗ᵠ ψ₂)
```

**For channels:**
```
(Λ₁ ⊗ₖ Λ₂) (ρ₁ ⊗ᴹ ρ₂) = (Λ₁ ρ₁) ⊗ᴹ (Λ₂ ρ₂)
```

### n-fold Products

**For MState:**
```lean
def npow (ρ : MState d) (n : ℕ) : MState (Fin n → d)
```
**Notation:** `ρ ⊗ᴹ^ n`

Creates `n` identical copies on the type `Fin n → d`.

**Example:** `ρ ⊗ᴹ^ 3` represents three copies of `ρ`.

### Key Theorems Involving Products

**Logarithm:**
- **`log_kron`**: `(A ⊗ₖ B).log = A.log ⊗ₖ 1 + 1 ⊗ₖ B.log`

**Trace preservation:**
- **`IsTracePreserving.kron`**: Tensor products of TP maps are TP

**Relative entropy:**
- **`qRelativeEnt_additive`**: Relative entropy is additive on product states

**Duality:**
- **`dual_kron`**: `(M ⊗ₖₘ N).dual = M.dual ⊗ₖₘ N.dual`

---

# Part III: Reference

## Notations and Scopes

### Quantum States

| Notation | Meaning | Type | Scope |
|----------|---------|------|-------|
| `〈ψ∣` | Bra vector | `Bra d` | `Braket` |
| `∣ψ〉` | Ket vector | `Ket d` | `Braket` |
| `〈ξ‖ψ〉` | Inner product (bra·ket) | `ℂ` | `Braket` |
| `⟪A, B⟫` | Hilbert-Schmidt inner product | `ℝ` | default |
| `ψ₁ ⊗ᵠ ψ₂` | Ket tensor product | `Ket (d₁ × d₂)` | default |
| `ρ₁ ⊗ᴹ ρ₂` | State tensor product | `MState (d₁ × d₂)` | default |
| `ρ ⊗ᴹ^ n` | n-fold state power | `MState (Fin n → d)` | default |

### Hermitian Matrices

| Notation | Meaning | Type | Scope |
|----------|---------|------|-------|
| `A ⊗ₖ B` | Kronecker product | `HermitianMat (m × n) 𝕜` | `HermitianMat` |
| `{A ≤ₚ B}` | Projection onto `B-A ≥ 0` eigenspace | `HermitianMat n 𝕜` | `HermitianMat` |
| `{A <ₚ B}` | Projection onto `B-A > 0` eigenspace | `HermitianMat n 𝕜` | `HermitianMat` |
| `{A ≥ₚ B}` | Same as `{B ≤ₚ A}` | `HermitianMat n 𝕜` | `HermitianMat` |
| `{A >ₚ B}` | Same as `{B <ₚ A}` | `HermitianMat n 𝕜` | `HermitianMat` |
| `A⁺` | Positive part `max(A, 0)` | `HermitianMat d 𝕜` | `HermitianMat` |
| `A⁻` | Negative part `max(-A, 0)` | `HermitianMat d 𝕜` | `HermitianMat` |

### Quantum Channels

| Notation | Meaning | Type | Scope |
|----------|---------|------|-------|
| `M₁ ⊗ₖ M₂` | Channel tensor product | `CPTPMap ...` | default |
| `M₁ ∘ₘ M₂` | Channel composition (M₁ after M₂) | `CPTPMap dIn dOut` | default |
| `U ◃ ρ` | Unitary conjugation `U ρ U†` | `MState d` | `MState` |
| `M ⊗ₖₘ N` | MatrixMap tensor product | `MatrixMap ...` | `MatrixMap` |
| `𝐔[n]` | Unitary group `U(n)` | `Matrix.unitaryGroup n ℂ` | default |
| `C[g]` | Controlled unitary gate | Qubit unitary | qubit-specific |

### Information Theory

| Notation | Meaning | Value Type | Scope |
|----------|---------|------------|-------|
| `𝐃(ρ‖σ)` | Quantum relative entropy | `EReal` | default |
| `D̃_α(ρ‖σ)` | Sandwiched Rényi entropy (α-parametrized) | `EReal` | default |
| `β_ε(ρ‖S)` | Optimal hypothesis test error rate | `Prob` | `OptimalHypothesisRate` |

### Resource Theory

| Notation | Meaning | Type | Scope |
|----------|---------|------|-------|
| `ρ₁ ⊗ᵣ ρ₂` | Resource-theoretic product | `MState (H (i * j))` | resource theory |
| `M₁ ⊗ᶜᵖᵣ M₂` | RT channel product | `CPTPMap ...` | resource theory |
| `i ⊗^H[n]` | n-fold RT space power | Space type | resource theory |
| `ρ ⊗ᵣ^[n]` | n-fold RT state power | `MState (H (i ^ n))` | resource theory |
| `𝑅ᵣ` | Relative entropy resource measure | `ℝ` | resource theory |
| `𝑅ᵣ∞` | Regularized RE resource | `ℝ` | resource theory |

### Scope Usage

**To use scoped notations:**
```lean
open scoped HermitianMat  -- enables ⊗ₖ for HermitianMat
open scoped MatrixMap     -- enables ⊗ₖₘ
open scoped Braket        -- enables ∣ψ〉, 〈ψ∣, etc.
```

**Default scope:** Notations like `⊗ᴹ`, `∘ₘ` are always available.

---

## Some Theorems

### Operator Theory

1. **`log_mono`** (Logarithm Monotonicity):
   For positive definite `A ≤ B`, we have `A.log ≤ B.log`.
   - The matrix logarithm is **operator monotone**

2. **`log_concave`** (Logarithm Concavity):
   For positive definite `A, B` and convex combination weights `a, b ≥ 0` with `a + b = 1`:
   ```
   a • A.log + b • B.log ≤ (a • A + b • B).log
   ```
   - The matrix logarithm is **operator concave**

3. **`inv_antitone`** (Inverse Antitonicity):
   For positive definite `A ≤ B`, we have `B⁻¹ ≤ A⁻¹`.
   - The matrix inverse is **operator antitone**

4. **`inv_convex`** (Inverse Convexity):
   For positive definite `A, B` and convex weights:
   ```
   (a • A + b • B)⁻¹ ≤ a • A⁻¹ + b • B⁻¹
   ```
   - The matrix inverse is **operator convex**

5. **`log_kron`** (Logarithm of Kronecker Product):
   For positive definite `A, B`:
   ```
   (A ⊗ₖ B).log = A.log ⊗ₖ 1 + 1 ⊗ₖ B.log
   ```

### Quantum Channels

7. **`choi_PSD_iff_CP_map`** (Choi's Theorem):
   A map is completely positive iff its Choi matrix is positive semidefinite.
   - This is the fundamental **Choi-Jamiołkowski** correspondence

8. **`choi_MState_iff_CPTP`** (State-Channel Correspondence):
   CPTP maps from `dIn` to `dOut` correspond bijectively to states on `dIn × dOut`.

9. **`IsTracePreserving.of_kraus_isTracePreserving`** (Kraus TP Criterion):
   Kraus operators `{Mₖ, Nₖ}` define a TP map iff `∑ₖ Nₖ† Mₖ = I`.

10. **`IsCompletelyPositive.dual`** (Duality of CP Maps):
    The dual of a completely positive map is completely positive.

11. **`dual_kron`** (Duality Preserves Kronecker Products):
    `(M ⊗ₖₘ N).dual = M.dual ⊗ₖₘ N.dual`

### Information Theory

12. **`qRelativeEnt_additive`** (Additivity of Relative Entropy):
    ```
    𝐃(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂)
    ```

13. **`qRelativeEnt_joint_convexity`** (Joint Convexity):
    Quantum relative entropy is jointly convex in both arguments.

14. **`sandwichedRelRentropy_additive`** (Rényi Additivity):
    Sandwiched Rényi entropy is additive on product states for all `α`.

15. **`Sᵥₙ_weak_monotonicity`** (Weak Monotonicity):
    Related to strong subadditivity of von Neumann entropy.

16. **`qMutualInfo_as_qRelativeEnt`** (Mutual Information as Relative Entropy):
    ```
    I(A:B) = 𝐃(ρ_{AB} ‖ ρ_A ⊗ ρ_B)
    ```

### Convexity and Order

17. **`MState.convex`** (States Form Convex Set):
    The set of quantum states is convex in the ambient Hermitian matrix space.

18. **`HermitianMat.convex_cone`** (PSD Cone is Convex):
    Non-negative combinations of PSD Hermitian matrices are PSD.

19. **`Matrix.PosSemidef.convex_cone`** (Matrix PSD Cone):
    Same for plain matrices.

### Monotonicity

20. **`trace_mono`** (Trace Monotonicity):
    `A ≤ B → A.trace ≤ B.trace` in Loewner order.

21. **`conj_mono`** (Conjugation Preserves Order):
    `A ≤ B → M * A * Mᴴ ≤ M * B * Mᴴ`

22. **`inner_mono`** (Inner Product Monotonicity):
    If `0 ≤ A` and `B ≤ C`, then `⟪A, B⟫ ≤ ⟪A, C⟫`.

23. **`diagonal_mono`** (Diagonal Monotonicity):
    Componentwise order on diagonal entries corresponds to Loewner order.

24. **`optimalHypothesisRate_antitone`** (Data Processing for Hypothesis Testing):
    Quantum channels cannot improve hypothesis testing performance.

### Topology and Analysis

25. **`CompactSpace (MState d)`** (States are Compact):
    The space of quantum states on a finite-dimensional system is compact.

26. **`OrderClosedTopology (HermitianMat d 𝕜)`** (Order is Closed):
    The Loewner order on Hermitian matrices is topologically closed.

27. **`CompactIccSpace (HermitianMat d 𝕜)`** (Order Intervals Compact):
    Order intervals `[A, B] = {X | A ≤ X ≤ B}` are compact.

28. **`tendsto_logApprox`** (Logarithm Approximation Convergence):
    For positive definite `x`, `logApprox x T → x.log` as `T → ∞`.

### Extensionality

29. **`HPMap.funext_mstate`** (Extensionality for HP Maps):
    Two Hermitian-preserving maps are equal if they agree on all `MState`s.

30. **`CPTPMap.funext`** (Extensionality for Channels):
    Two CPTP maps are equal if they agree on all input states.

### Resource Theory

31. **`RelativeEntResource.Subadditive`** (Relative Entropy Resource):
    The relative entropy of resource is subadditive under tensor products.

### Minimax Theory

32. **Sion's Minimax Theorem**:
    Under appropriate compactness and quasi-convexity conditions, `sup_x inf_y f(x,y) = inf_y sup_x f(x,y)`.
