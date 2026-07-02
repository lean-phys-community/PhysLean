/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Contraction.Basic
public import Physlib.Relativity.Tensors.Evaluation
public import Physlib.Relativity.Tensors.Tensorial
/-!

# Elaboration of tensor expressions

- Syntax in Lean allows us to represent tensor expressions in a way close to what we expect to
  see on pen-and-paper.
- The elaborator turns this syntax into a tensor tree.

## Examples

- Suppose `T` and `T'` are tensors with color `![c1, c2]`.
- `{T | μ ν}ᵀ` is `tensorNode T`.
- We can also write e.g. `{T | μ ν}ᵀ.tensor` to get the tensor itself.
- `{- T | μ ν}ᵀ` is `neg (tensorNode T)`.
- `{T | 0 ν}ᵀ` is `eval 0 0 (tensorNode T)`.
- `{T | [μ] ν}ᵀ` is `eval 0 μ (tensorNode T)`.
- `{T | μ ν + T' | μ ν}ᵀ` is `addNode (tensorNode T) (perm _ (tensorNode T'))`, where
  here `_` will be the identity permutation so does nothing.
- `{T | μ ν = T' | μ ν}ᵀ` is `(tensorNode T).tensor = (perm _ (tensorNode T')).tensor`.
- If `a ∈ k` then `{a •ₜ T | μ ν}ᵀ` is `smulNode a (tensorNode T)`.
- If `g ∈ S.G` then `{g •ₐ T | μ ν}ᵀ` is `actionNode g (tensorNode T)`.
- Suppose `T2` is a tensor with color `![c3]`.
  Then `{T | μ ν ⊗ T2 | σ}ᵀ` is `prodNode (tensorNode T1) (tensorNode T2)`.
- If `T3` is a tensor with color `![S.τ c1, S.τ c2]`, then
  `{T | μ ν ⊗ T3 | μ σ}ᵀ` is `contr 0 1 _ (prodNode (tensorNode T1) (tensorNode T3))`.
  `{T | μ ν ⊗ T3 | μ ν }ᵀ` is
  `contr 0 0 _ (contr 0 1 _ (prodNode (tensorNode T1) (tensorNode T3)))`.
- If `T4` is a tensor with color `![c2, c1]` then
  `{T | μ ν + T4 | ν μ }ᵀ`is `addNode (tensorNode T) (perm _ (tensorNode T4))` where `_`
  is the permutation of the two indices of `T4`.
  `{T | μ ν = T4 | ν μ }ᵀ` is `(tensorNode T).tensor = (perm _ (tensorNode T4)).tensor` is the
  permutation of the two indices of `T4`.

## Comments

- In all of these expressions `μ`, `ν` etc are free. It does not matter what they are called,
  Lean will elaborate them in the same way. In other words, `{T | μ ν ⊗ T3 | μ ν }ᵀ` is exactly
  the same to Lean as `{T | α β ⊗ T3 | α β }ᵀ`.
- Note that compared to ordinary index notation, we do not rise or lower the indices.
  This is for two reasons: 1) It is difficult to make this general for all tensor species,
  2) It is a redundancy in ordinary index notation, since the tensor `T` itself already tells you
  this information.

-/

@[expose] public meta section
open Lean Meta Elab Tactic Term

namespace TensorSpecies
namespace Tensor

/-!

## Indices

-/

/-- A syntax category for indices of tensor expressions. -/
declare_syntax_cat indexExpr

/-- A basic index is a ident. -/
syntax ident : indexExpr

/-- An index can be a num, which will be used to evaluate the tensor. -/
syntax num : indexExpr

/-- Notation to describe the jiggle of a tensor index. -/
syntax "τ(" ident ")" : indexExpr

/-- Notation to describe the evaluation of a tensor index. -/
syntax "[" ident "]" : indexExpr

/-- Bool which is true if an index is a num. -/
def indexExprIsNum (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr|$_:num) => true
  | _ => false

/-- Bool which is true if an index is evaluated bracket `[μ]`. -/
def indexExprIsBracketEval(stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr|[$_]) => true
  | _ => false

/-- If an index is a num - the underlying natural number. -/
def indexToNum (stx : Syntax) : TermElabM Nat :=
  match stx with
  | `(indexExpr|$a:num) =>
    match a.raw.isNatLit? with
    | some n => return n
    | none => throwError "Expected a natural number literal."
  | _ =>
    throwError "Unsupported tensor expression syntax in indexToNum: {stx}"

/-- When an index is not a num, the corresponding ident. -/
def indexToIdent (stx : Syntax) : TermElabM Ident :=
  match stx with
  | `(indexExpr|$a:ident) => return a
  | `(indexExpr| τ($a:ident)) => return a
  | `(indexExpr| [$a:ident]) => return a
  | _ =>
    throwError "Unsupported expression syntax in indexToIdent: {stx}"

/-- Takes a pair ``a b : ℕ × TSyntax `indexExpr``. If `a.1 < b.1` and `a.2 = b.2` then
  outputs `some (a.1, b.1)`, otherwise `none`. -/
def indexPosEq (a b : TSyntax `indexExpr × ℕ) : TermElabM (Option (ℕ × ℕ)) := do
  let a' ← indexToIdent a.1
  let b' ← indexToIdent b.1
  if a.2 < b.2 ∧ Lean.TSyntax.getId a' = Lean.TSyntax.getId b' then
    return some (a.2, b.2)
  else
    return none

/-- Bool which is true if an index is of the form τ(i) that is, to be dualed. -/
def indexToDual (stx : Syntax) : Bool :=
  match stx with
  | `(indexExpr| τ($_)) => true
  | _ => false

/-!

## Manipulation of lists of indexExpr

-/

/-- Adjusts a list `List ℕ` by subtracting from each natural number the number
  of elements before it in the list which are less than itself. This is used
  to form a list of pairs which can be used for evaluating indices. -/
def evalAdjustPos (l : List ℕ) : List ℕ :=
  let l' := List.mapAccumr
    (fun x (prev : List ℕ) =>
      let e := prev.countP (fun y => y < x)
      (x :: prev, x - e)) l.reverse []
  l'.2.reverse

/-- For list of `indexExpr` e.g. `[α, 3, β, 2, γ]`, `getEvalPos`
  returns a list of pairs `ℕ × ℕ` related to indices which are numbers.
  The second element of each pair is the number corresponding to that index.
  The first element is the position of that number in the list of indices when
  all other numbered indices before it are removed. Thus for the example given
  `getEvalPos` outputs `[(1, 3), (2, 2)]`. -/
def getEvalPos (ind : List (TSyntax `indexExpr)) : TermElabM (List (ℕ × ℕ)) := do
  let indEnum := ind.zipIdx
  let evals := indEnum.filter (fun x => indexExprIsNum x.1)
  let evals2 ← (evals.mapM (fun x => indexToNum x.1))
  let pos := evalAdjustPos (evals.map (fun x => x.2))
  return List.zip pos evals2

/-- For list of `indexExpr` e.g. `[α, 3, β, 2, [γ]]`, `getEvalPos`
  returns a list of pairs `ℕ × Term` related to indices which are evaluated
  e.g. `[μ]`.
  The second element of each pair is the value corresponding to that index.
  The first element is the position of that number in the list of indices when
  all other numbered indices before it are removed. Thus for the example given
  `getEvalBracketPos` outputs `[(4, γ)]`. -/
def getEvalBracketPos (ind : List (TSyntax `indexExpr)) : TermElabM (List (ℕ × Term)) := do
  let indEnum := ind.zipIdx
  let evals := indEnum.filter (fun x => indexExprIsBracketEval x.1)
  let evals2 ← (evals.mapM (fun x => indexToIdent x.1))
  let pos := evalAdjustPos (evals.map (fun x => x.2))
  return List.zip pos evals2

/-- For list of `indexExpr` e.g. `[α, 3, β, α, 2, γ]`, `getContrPos`
  first removes all indices which are numbers (e.g. `[α, β, α, γ]`).
  It then outputs pairs `(a, b)` in `ℕ × ℕ` of positions of this list with `a < b`
  such that the index at `a` is equal to the index at `b`. It checks whether or not
  an element is contracted more then once. -/
def getContrPos (ind : List (TSyntax `indexExpr)) : TermElabM (List (ℕ × ℕ)) := do
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x
    ∧ ¬ indexExprIsBracketEval x)
  let indEnum := indFilt.zipIdx
  let bind := List.flatMap (fun a => indEnum.map (fun b => (a, b))) indEnum
  let filt ← bind.filterMapM (fun x => indexPosEq x.1 x.2)
  if ¬ ((filt.map Prod.fst).Nodup ∧ (filt.map Prod.snd).Nodup) then
    throwError "To many contractions"
  return filt

/-- The list of indices after contraction or evaluation. -/
def withoutContrEval (ind : List (TSyntax `indexExpr)) : TermElabM (List (TSyntax `indexExpr)) := do
  let indFilt : List (TSyntax `indexExpr) := ind.filter (fun x => ¬ indexExprIsNum x)
  return indFilt.filter (fun x => indFilt.count x ≤ 1)

/-- Takes a list and puts consecutive elements into pairs.
  e.g. [0, 1, 2, 3] becomes [(0, 1), (2, 3)]. -/
def toPairs (l : List ℕ) : List (ℕ × ℕ) :=
  match l with
  | x1 :: x2 :: xs => (x1, x2) :: toPairs xs
  | [] => []
  | [x] => [(x, 0)]

/-- Adjusts a list `List (ℕ × ℕ)` by subtracting from each natural number the number
  of elements before it in the list which are less than itself. This is used
  to form a list of pairs which can be used for contracting indices. -/
def contrListAdjust (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (l.mapAccumr
    (fun (x : ℕ × ℕ) (prev : List ℕ) =>
      (x.1 :: x.2 :: prev,
        (x.1 - prev.countP (fun y => y < x.1), x.2 - prev.countP (fun y => y < x.2))))
    []).2

/-!

## Permutations of indices

-/

/-- Given two lists of indices, all of which are indent,
  returns the `List (ℕ)` representing the how one list
  permutes into the other. -/
def getPermutation (l1 l2 : List (TSyntax `indexExpr)) : TermElabM (List (ℕ)) := do
  /- Turn every index into an indent. -/
  let l1' ← l1.mapM (fun x => indexToIdent x)
  let l2' ← l2.mapM (fun x => indexToIdent x)
  /- For `l1 = [α, β, γ, δ]`, `l1enum` is `[(α, 0), (β, 1), (γ, 2), (δ, 3)]` -/
  let l1enum := l1'.zipIdx
  /- For `l2 = [γ, α, δ, β]`, `l2''` is `[(γ,2), (α, 0), (δ, 3), (β, 1)]` -/
  let l2'' := l2'.filterMap
    (fun x => l1enum.find? (fun y => Lean.TSyntax.getId y.1 = Lean.TSyntax.getId x))
  return l2''.map fun x => x.2

/-- The construction of an expression corresponding to the type of a given string once parsed. -/
def stringToTerm (str : String) : TermElabM Term := do
  let env ← getEnv
  let stx := Parser.runParserCategory env `term str
  match stx with
  | Except.error _ => throwError "Could not create type from string (stringToTerm). "
  | Except.ok stx =>
    match stx with
    | `(term| $e) => return e

/-!

## Syntax for tensor expressions.

-/

/-- A syntax category for tensor expressions. -/
declare_syntax_cat tensorExpr

/-- The syntax for a tensor node. -/
syntax term "|" (ppSpace indexExpr)* : tensorExpr

/-- Equality. -/
syntax:40 tensorExpr "=" tensorExpr:41 : tensorExpr

/-- The syntax for tensor prod two tensor nodes. -/
syntax:70 tensorExpr "⊗" tensorExpr:71 : tensorExpr

/-- The syntax for tensor addition. -/
syntax tensorExpr "+" tensorExpr : tensorExpr

/-- Allowing brackets to be used in a tensor expression. -/
syntax "(" tensorExpr ")" : tensorExpr

/-- Scalar multiplication for tensors. -/
syntax term "•ₜ" tensorExpr : tensorExpr

/-- group action for tensors. -/
syntax term "•ₐ" tensorExpr : tensorExpr

/-- Negation of a tensor tree. -/
syntax "-" tensorExpr : tensorExpr

/-!

## Syntax of tensor expressions to indices.

-/

/-- For syntax of the form `T` where `T` is `Tensor S c` this returns
  the value of `TensorSpecies.numIndices T`. That is, the exact number of indices
  associated with that tensor. -/
def getNumIndicesExact (stx : Syntax) : TermElabM ℕ := do
  match stx with
  | `($t:term) =>
    let a ← elabTerm (← `(Tensorial.numIndices $t)) (some (mkConst ``Nat))
    let a' ← whnf a
    match a' with
    | Expr.lit (Literal.natVal n) =>
      return n
    |_ => throwError s!"Could not extract number of indices from tensor
      {stx} (getNoIndicesExact). "

/-- For syntax of the form `T | α β 2 β`, `getAllIndices` returns a list `[α, β, 2, β]`
  of all `indexExpr`. -/
def getAllIndices (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      let indices ← args.toList.mapM fun arg => do
        match arg with
        | `(indexExpr|$t:indexExpr) => pure t
      return indices
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesNode: {stx}"

/-- The function `getProdIndices` is defined for the following syntax:
1. For e.g. `T | α β 2 β`, it returns all uncontracted and unevaluated indices e.g.`[α]`
2. For e.g. `T1 | α β 2 β ⊗ T2 | α γ δ δ` it returns all unevaluated indices which
    are not contracted in either tensor e.g. `[α, α, γ]`.
3. For e.g. `(T1 | α β 2 β ⊗ T2 | α γ δ δ) ⊗ T3 | γ` it does `2` recursively e.g. `[γ, γ]`
-/
partial def getProdIndices (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      return (← withoutContrEval (← getAllIndices stx))
  | `(tensorExpr| $a:tensorExpr ⊗ $b:tensorExpr) => do
      let indicesA ← withoutContrEval (← getProdIndices a)
      let indicesB ← withoutContrEval (← getProdIndices b)
      return indicesA ++ indicesB
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← getProdIndices a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesProd: {stx}"

/-- Returns the remaining indices of a tensor expression after contraction and evaluation.
  Thus every index in the output of `getIndicesFull` is ident and there are no duplicates.
  Examples are:
1. `T | α β 2 β` gives `[α]`
2. `T1 | α β 2 β ⊗ T2 | α γ δ δ` gives `[γ]`
3. `(T1 | α β 2 β ⊗ T2 | α γ δ δ) ⊗ T3 | γ` gives `[]`
4. `T1 | α β 2 β + T2 | α 4 δ δ` gives `[α]`
-/
partial def getIndicesFull (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:term | $[$args]*) => do
      return (← withoutContrEval (← getAllIndices stx))
  | `(tensorExpr| $_:tensorExpr ⊗ $_:tensorExpr) => do
      return (← withoutContrEval (← getProdIndices stx))
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← getIndicesFull a)
  | `(tensorExpr| -$a:tensorExpr) => do
      return (← getIndicesFull a)
  | `(tensorExpr| $_:term •ₜ $a) => do
      return (← getIndicesFull a)
  | `(tensorExpr| $a:tensorExpr + $_:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesFull: {stx}"

/-- Gets the indices associated with the LHS of an addition. -/
def getIndicesLeft (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $a:tensorExpr + $_:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesLeft: {stx}"

/-- Gets the indices associated with the RHS of an addition. -/
def getIndicesRight (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:tensorExpr + $a:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesRight: {stx}"

/-- Gets the indices associated with the LHS of an equality. -/
def getIndicesLeftEq (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $a:tensorExpr = $_:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesLeftEq: {stx}"

/-- Gets the indices associated with the RHS of an equality. -/
def getIndicesRightEq (stx : Syntax) : TermElabM (List (TSyntax `indexExpr)) := do
  match stx with
  | `(tensorExpr| $_:tensorExpr = $a:tensorExpr) => do
      return (← getIndicesFull a)
  | _ =>
    throwError "Unsupported tensor expression syntax in getIndicesRightEq: {stx}"

/-!

## Modifying terms to tensor trees

-/
open TensorSpecies

/-- For a term of the form `T` where `T` is `Tensor S c`,
  `tensorTermToTensorTree` returns the term corresponding to the `tensorNode T` -/
def nodeTermMap (T : Term) : Term :=
  Syntax.mkApp (mkIdent ``Tensorial.toTensor) #[T]

/-- Given a list `l` of pairs `ℕ × ℕ` and a term `T` corresponding to a tensor tree,
  for each `(a, b)` in `l`, `evalSyntax` applies `TensorTree.eval a b` to `T` recursively.
  Here `a` is the position of the index to be evaluated and `b` is the value it is evaluated to.

  For example, if `l` is `[(1, 2), (1, 4)]` and `T` is a tensor tree then `evalSyntax l T`
  is `TensorTree.eval 1 4 (TensorTree.eval 1 2 T)`.

  The list `l` is expected to be the output of `getEvalPos`.
-/
def evalTermMap (l : List (ℕ × ℕ)) (T : Term) : Term :=
  l.foldl (fun T' (x1, x2) => Syntax.mkApp (mkIdent ``Tensor.evalT)
    #[Syntax.mkNumLit (toString x1), Syntax.mkNumLit (toString x2), T']) T

/-- Given a list `l` of pairs `ℕ × Term` and a term `T` corresponding to a tensor tree,
  for each `(a, b)` in `l`, `evalSyntax` applies `TensorTree.eval a b` to `T` recursively.
  Here `a` is the position of the index to be evaluated and
  `b` is the value it is evaluated to from the `[μ]` syntax.

  For example, if `l` is `[(1, μ), (1, ν)]` and `T` is a tensor tree then `evalSyntax l T`
  is `TensorTree.eval 1 ν (TensorTree.eval 1 μ T)`.

  The list `l` is expected to be the output of `getEvalBracketPos`.
-/
def evalTermBracketMap (l : List (ℕ × Term)) (T : Term) : Term :=
  l.foldl (fun T' (x1, x2) => Syntax.mkApp (mkIdent ``Tensor.evalT)
    #[Syntax.mkNumLit (toString x1), x2, T']) T

/-- For each element of `l : List (ℕ × ℕ)` applies `TensorTree.contr` to the given term. -/
def contrTermMap (n : ℕ) (l : List (ℕ × ℕ)) (T : Term) : Term :=
  let proofTerm := Syntax.mkApp (mkIdent ``Tensor.contrT_decide) #[mkIdent ``rfl]
  ((contrListAdjust l).reverse.foldl (fun (m, T') (x0, x1) =>
    (m + 2, Syntax.mkApp (mkIdent ``Tensor.contrT)
    #[Syntax.mkNumLit (toString (n - m)), Syntax.mkNumLit (toString x0),
    Syntax.mkNumLit (toString x1), proofTerm, T'])) ((2, T) : ℕ × Term)).2

/-- The syntax associated with a product of tensors. -/
def prodTermMap (T1 T2 : Term) : Term :=
  Syntax.mkApp (mkIdent ``Tensor.prodT) #[T1, T2]

/-- The syntax associated with negation of tensors. -/
def negTermMap (T1 : Term) : Term :=
  Syntax.mkApp (mkIdent ``Neg.neg) #[T1]

/-- The syntax associated with the scalar multiplication of tensors. -/
def smulTermMap (c T : Term) : Term :=
  Syntax.mkApp (mkIdent ``HSMul.hSMul) #[c, T]

/-- The syntax associated with the group action of tensors. -/
def actionTermMap (c T : Term) : Term :=
  Syntax.mkApp (mkIdent ``HSMul.hSMul) #[c, T]

/-- Whether `T1` and `T2` elaborate to tensors of definitionally equal colour (equal type).
  Used to decide whether an identity reindexing between them may be dropped: the bare,
  un-`permT`'d term is well typed exactly when the two colours agree by `rfl`. The check
  elaborates speculatively and restores the elaborator state afterwards. -/
def colorsDefEq (T1 T2 : Term) : TermElabM Bool := do
  let s ← saveState
  try
    let ty1 ← inferType (← elabTerm T1 none)
    let ty2 ← inferType (← elabTerm T2 none)
    let result ← Meta.isDefEq ty1 ty2
    s.restore
    return result
  catch _ =>
    s.restore
    return false

/-- Wraps `T` in the reindexing `permT ![lPerm] IsReindexing.auto`. -/
def permWrap (lPerm : List ℕ) (T : Term) : TermElabM Term := do
  let permString := "![" ++ String.intercalate ", " (lPerm.map toString) ++ "]"
  let P ← stringToTerm permString
  return Syntax.mkApp (mkIdent ``Tensor.permT) #[P, mkIdent ``IsReindexing.auto, T]

/-- The syntax for the addition of two tensor trees. The right-hand side is reindexed by the
  permutation `lPerm` relating the two index lists; the reindexing is dropped only when that
  permutation is the identity *and* the two colours already agree definitionally (so the bare
  sum is well typed, i.e. the identity reindexing is provably trivial by `rfl`). -/
def addTermMap (lPerm : List ℕ) (T1 T2 : Term) : TermElabM Term := do
  if lPerm = List.range lPerm.length then
    if ← colorsDefEq T1 T2 then
      return Syntax.mkApp (mkIdent ``HAdd.hAdd) #[T1, T2]
  return Syntax.mkApp (mkIdent ``HAdd.hAdd) #[T1, ← permWrap lPerm T2]

/-- The syntax for an equality of two tensor trees. The right-hand side is reindexed by the
  permutation `lPerm` relating the two index lists; the reindexing is dropped only when that
  permutation is the identity *and* the two colours already agree definitionally (so the bare
  equality is well typed, i.e. the identity reindexing is provably trivial by `rfl`). -/
def equalTermMap (lPerm : List ℕ) (T1 T2 : Term) : TermElabM Term := do
  if lPerm = List.range lPerm.length then
    if ← colorsDefEq T1 T2 then
      return Syntax.mkApp (mkIdent ``Eq) #[T1, T2]
  return Syntax.mkApp (mkIdent ``Eq) #[T1, ← permWrap lPerm T2]

/-!

## Syntax to tensor tree

-/

/-- Takes a syntax corresponding to a tensor expression and turns it into a
  term corresponding to a tensor tree. -/
partial def syntaxFull (stx : Syntax) : TermElabM Term := do
  match stx with
  | `(tensorExpr| $T:term | $[$args]*) =>
      let indices ← getAllIndices stx
      let rawIndex ← getNumIndicesExact T
      if indices.length ≠ rawIndex then
        throwError "The expected number of indices {rawIndex} does not match the tensor {T}."
      let tensorNodeSyntax := nodeTermMap T
      let evalSyntax := evalTermMap (← getEvalPos indices) tensorNodeSyntax
      let evalBracketSyntax := evalTermBracketMap (← getEvalBracketPos indices) evalSyntax
      let contrSyntax := contrTermMap indices.length (← getContrPos indices) evalBracketSyntax
      return contrSyntax
  | `(tensorExpr| $a:tensorExpr ⊗ $b:tensorExpr) => do
      let prodSyntax := prodTermMap (← syntaxFull a) (← syntaxFull b)
      let contrSyntax := contrTermMap (← getProdIndices stx).length
        (← getContrPos (← getProdIndices stx)) prodSyntax
      return contrSyntax
  | `(tensorExpr| ($a:tensorExpr)) => do
      return (← syntaxFull a)
  | `(tensorExpr| -$a:tensorExpr) => do
      return negTermMap (← syntaxFull a)
  | `(tensorExpr| $c:term •ₜ $a:tensorExpr) => do
      return smulTermMap c (← syntaxFull a)
  | `(tensorExpr| $c:term •ₐ $a:tensorExpr) => do
      return actionTermMap c (← syntaxFull a)
  | `(tensorExpr| $a + $b) => do
      let indicesLeft ← getIndicesLeft stx
      let indicesRight ← getIndicesRight stx
      let lPerm ← getPermutation indicesLeft indicesRight
      let addSyntax ← addTermMap lPerm (← syntaxFull a) (← syntaxFull b)
      return addSyntax
  | `(tensorExpr| $a:tensorExpr = $b:tensorExpr) => do
      let indicesLeft ← getIndicesLeftEq stx
      let indicesRight ← getIndicesRightEq stx
      let lPerm ← getPermutation indicesLeft indicesRight
      let equalSyntax ← equalTermMap lPerm (← syntaxFull a) (← syntaxFull b)
      return equalSyntax
  | _ =>
    throwError "Unsupported tensor expression syntax in elaborateTensorNode: {stx}"

/-!

## Elaboration

-/

/-- Removes redundant `Tensorial.toTensor` coercions from an elaborated tensor expression:
  every subterm `Tensorial.toTensor t` whose `Tensorial` instance is the canonical instance
  on `S.Tensor c` (`Tensorial.self`) is replaced by `t` itself, since there the coercion is
  the identity. Coercions coming from genuine tensorial instances (e.g. on Lorentz vectors)
  carry real information and are left untouched. -/
def stripToTensorSelf (e : Expr) : Expr :=
  e.replace fun s => do
    guard (s.isAppOf ``DFunLike.coe)
    guard (s.getAppNumArgs ≥ 2)
    let f := s.appFn!.appArg!
    guard (f.isAppOf ``Tensorial.toTensor)
    guard (f.appArg!.isAppOf ``Tensorial.self)
    return s.appArg!

/-- Takes a syntax corresponding to a tensor expression and turns it into an
  expression corresponding to a tensor tree. The redundant `Tensorial.toTensor` coercions
  inserted for bare `S.Tensor` terms are removed via `stripToTensorSelf`. -/
def elaborateTensorNode (stx : Syntax) : TermElabM Expr := do
  let tensorExpr ← elabTerm (← syntaxFull stx) none
  return stripToTensorSelf (← instantiateMVars tensorExpr)

/-- The tensor tree corresponding to a tensor expression. -/
syntax (name := tensorExprSyntax) "{" tensorExpr "}ᵀ" : term

elab_rules (kind:=tensorExprSyntax) : term
  | `(term| {$e:tensorExpr}ᵀ) => do
    let tensorTree ← elaborateTensorNode e
    return tensorTree

/-!

## Test cases

We pin the elaboration of the `{ … }ᵀ` notation for each construct it supports: bare tensor
nodes, a genuine `Tensorial` instance, negation, evaluation, scalar multiplication, the group
action, products, contractions, addition and equality. Together these check that the elaborator
inserts neither a redundant `Tensorial.toTensor` wrapper on a bare `S.Tensor` term nor an
identity `permT` when the two sides already align, while keeping the `toTensor` coercion of a
genuine `Tensorial` instance and a genuine `permT` for a real reindexing.

-/
section Tests
variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}
    {c : Fin 2 → C} {t t' : S.Tensor c} (a : k) (g : G) (y : basisIdx (c 0))
    {c1 c2 c3 : C} {u : S.Tensor ![c1, c2]} {u' : S.Tensor ![c2, c1]}
    {w : S.Tensor ![c3]} {td : S.Tensor ![S.τ c1, S.τ c2]}
    {M : Type} [AddCommMonoid M] [Module k M] [Tensorial S c M] (m : M)

-- A bare `S.Tensor` carries no redundant `Tensorial.toTensor` wrapper.
/-- info: t : S.Tensor c -/
#guard_msgs in
#check {t | α β}ᵀ

-- A genuine `Tensorial` instance (here the abstract `m : M`) keeps its `toTensor` coercion.
/-- info: Tensorial.toTensor m : S.Tensor c -/
#guard_msgs in
#check {m | α β}ᵀ

-- Negation of a tensor expression.
/-- info: -t : S.Tensor c -/
#guard_msgs in
#check {-(t | α β)}ᵀ

-- Evaluation of an index at a basis value `[y]`.
/-- info: (evalT 0 y) t : S.Tensor (c ∘ Fin.succAbove 0) -/
#guard_msgs in
#check {t | [y] β}ᵀ

-- Scalar multiplication `•ₜ`.
/-- info: a • t : S.Tensor c -/
#guard_msgs in
#check {a •ₜ t | α β}ᵀ

-- Group action `•ₐ`.
/-- info: g • t : S.Tensor c -/
#guard_msgs in
#check {g •ₐ t | α β}ᵀ

-- Tensor product of two tensors with no shared indices.
/-- info: (prodT u) w : S.Tensor (Fin.append ![c1, c2] ![c3]) -/
#guard_msgs in
#check {u | α β ⊗ w | γ}ᵀ

-- Contraction of both index pairs of a product.
/--
info: (contrT 0 0 1 ⋯) ((contrT 2 1 3 ⋯) ((prodT u) td)) :
  S.Tensor ((Fin.append ![c1, c2] ![S.τ c1, S.τ c2] ∘ Fin.succSuccAbove 1 3) ∘
  Fin.succSuccAbove 0 1)
-/
#guard_msgs (whitespace := lax) in
#check {u | α β ⊗ td | α β}ᵀ

-- Addition with aligned indices: no redundant identity `permT` (nor `toTensor`).
/-- info: t + t' : S.Tensor c -/
#guard_msgs in
#check ({t | α β + t' | α β}ᵀ)

-- Equality with aligned indices: no redundant identity `permT`.
/-- info: t = t' : Prop -/
#guard_msgs in
#check ({t | α β = t' | α β}ᵀ : Prop)

-- Equality with reordered indices: a genuine `permT` reindexing is inserted.
/-- info: u = (permT ![1, 0] ⋯) u' : Prop -/
#guard_msgs in
#check ({u | α β = u' | β α}ᵀ : Prop)

end Tests

end Tensor

end TensorSpecies
