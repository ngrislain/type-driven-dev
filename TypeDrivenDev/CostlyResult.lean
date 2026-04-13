-- TypeDrivenDev.CostlyResult — Compile-time cost tracking via a graded monad
--
-- `Costly α n` carries a value of type `α` tagged with computation cost `n : Nat`
-- at the type level. The type checker enforces cost budgets with zero runtime overhead.

namespace CostlyResult

-- ============================================================================
-- Part 1: Core Graded Monad
-- ============================================================================

/-- A value of type `α` tagged with compile-time cost `cost : Nat`. -/
structure Costly (α : Type) (cost : Nat) where
  val : α
deriving Repr

/-- Wrap a value with zero cost. -/
def Costly.pure (a : α) : Costly α 0 := ⟨a⟩

/-- Sequence two costly computations; costs add at the type level. -/
def Costly.bind (ma : Costly α ca) (f : α → Costly β cb) : Costly β (ca + cb) :=
  ⟨(f ma.val).val⟩

/-- Burn `n` units of cost budget without computing anything. -/
def Costly.burn (n : Nat) : Costly Unit n := ⟨()⟩

/-- Reconcile a bind-chain sum with a clean formula (proved by `omega`). -/
def Costly.cast (c : Costly α n) (h : n = m) : Costly α m := h ▸ c

/-- Lift a pure function over a costly value (no extra cost). -/
def Costly.map (ma : Costly α c) (f : α → β) : Costly β c := ⟨f ma.val⟩

/-- Widen the cost bound: `Costly α n` fits in any budget `m ≥ n`.
    The proof is filled automatically by `omega`. -/
def Costly.relax (c : Costly α n) (_h : n ≤ m := by first | omega | exact Nat.le_refl _) : Costly α m := ⟨c.val⟩

-- ============================================================================
-- Part 2: cdo Notation
-- ============================================================================

/-  `cdo` is a do-like notation for the graded `Costly` monad.
    It reuses Lean's `doSeq` parser for indentation-sensitive blocks,
    then desugars into `Costly.bind` / `Costly.pure` instead of `Bind.bind` / `Pure.pure`.

    Supported:
    - `let x ← e`    →  `Costly.bind e (fun x => ...)`
    - `let x := e`    →  `let x := e; ...`
    - `return e`      →  `Costly.pure e`
    - bare `e`        →  (last line) returned as-is, or (middle) `Costly.bind e (fun _ => ...)`
    - `if`/`match`    →  passed through (both branches must have same cost type)
-/

open Lean in
syntax (name := cdoNotation) "cdo " doSeq : term

section CdoImpl
open Lean

private def cdoGetElem (item : Syntax) : Syntax :=
  let args := item.getArgs
  if h : 0 < args.size then args[0] else item

private def cdoKind (s : Syntax) : String := s.getKind.toString

private def cdoGetExprTerm (doExpr : Syntax) : Syntax :=
  doExpr[0]!

private def cdoGetReturnVal (doReturn : Syntax) : Syntax :=
  let opt := if doReturn.getNumArgs >= 2 then doReturn[1]! else Syntax.missing
  if opt.getNumArgs >= 2 then opt[1]! else if opt.getNumArgs == 1 then opt[0]! else opt

private def cdoGetLetArrowParts (doLetArrow : Syntax) : Syntax × Syntax :=
  let decl := doLetArrow[2]!
  let ident := decl[0]!
  let rhsDoExpr := decl[3]!
  let rhs := cdoGetExprTerm rhsDoExpr
  (ident, rhs)

private def cdoGetLetParts (doLet : Syntax) : Syntax × Syntax :=
  let letDecl := doLet[2]!
  let lid := letDecl[0]!
  let ident := lid[0]![0]!
  let val := lid.getArgs.back!
  (ident, val)

private partial def cdoProcessLast (elem : Syntax) : MacroM Syntax := do
  let k := cdoKind elem
  if k.endsWith "doReturn" then
    let val : TSyntax `term := ⟨cdoGetReturnVal elem⟩
    `(Costly.pure $val)
  else if k.endsWith "doExpr" then
    return cdoGetExprTerm elem
  else
    return elem

private partial def cdoProcessMiddle (elem rest : Syntax) : MacroM Syntax := do
  let k := cdoKind elem
  let rest : TSyntax `term := ⟨rest⟩
  if k.endsWith "doLetArrow" then
    let (identStx, rhsStx) := cdoGetLetArrowParts elem
    let ident : TSyntax `ident := ⟨identStx⟩
    let rhs : TSyntax `term := ⟨rhsStx⟩
    `(Costly.bind $rhs fun $ident => $rest)
  else if k.endsWith "doLet" then
    let (identStx, valStx) := cdoGetLetParts elem
    let ident : TSyntax `ident := ⟨identStx⟩
    let val : TSyntax `term := ⟨valStx⟩
    `((fun $ident => $rest) $val)
  else if k.endsWith "doExpr" then
    let expr : TSyntax `term := ⟨cdoGetExprTerm elem⟩
    `(Costly.bind $expr fun _ => $rest)
  else if k.endsWith "doReturn" then
    let val : TSyntax `term := ⟨cdoGetReturnVal elem⟩
    `(Costly.pure $val)
  else
    let e : TSyntax `term := ⟨elem⟩
    `(Costly.bind $e fun _ => $rest)

private partial def cdoProcessItems : List Syntax → MacroM Syntax
  | [] => Macro.throwError "empty cdo block"
  | [item] => cdoProcessLast (cdoGetElem item)
  | item :: rest => do
    let restSyntax ← cdoProcessItems rest
    cdoProcessMiddle (cdoGetElem item) restSyntax

private def cdoExpandSeq (seq : Syntax) : MacroM Syntax := do
  let inner := if seq.getNumArgs >= 3 then seq[1]! else seq[0]!
  let items := inner.getArgs
  cdoProcessItems items.toList

@[macro cdoNotation] def expandCdo : Macro := fun stx => do
  let body ← cdoExpandSeq stx[1]!
  let body : TSyntax `term := ⟨body⟩
  `(Costly.relax $body)

end CdoImpl

-- ============================================================================
-- Part 3: Costly Arithmetic (add/sub = 1, mul = 100)
-- ============================================================================

/-- Costly integer addition: cost 1. -/
def costlyAdd (a b : Int) : Costly Int 1 := ⟨a + b⟩

/-- Costly integer subtraction: cost 1. -/
def costlySub (a b : Int) : Costly Int 1 := ⟨a - b⟩

/-- Costly integer multiplication: cost 100. -/
def costlyMul (a b : Int) : Costly Int 100 := ⟨a * b⟩

-- Mixed-type instances (Int×Nat, Nat×Int) are non-scoped since they don't
-- conflict with stdlib (which only defines HAdd T T T for same types).
-- These handle the common case of `x + 5` where x:Int comes from a bind.
instance : HAdd Int Nat (Costly Int 1) where hAdd a b := costlyAdd a ↑b
instance : HAdd Nat Int (Costly Int 1) where hAdd a b := costlyAdd ↑a b
instance : HSub Int Nat (Costly Int 1) where hSub a b := costlySub a ↑b
instance : HSub Nat Int (Costly Int 1) where hSub a b := costlySub ↑a b
instance : HMul Int Nat (Costly Int 100) where hMul a b := costlyMul a ↑b
instance : HMul Nat Int (Costly Int 100) where hMul a b := costlyMul ↑a b

-- Same-type instances (Int×Int, Nat×Nat) are scoped because they conflict
-- with stdlib (HAdd Int Int Int, etc.) due to HAdd's outParam.
-- Open `CostlyOps` when you need `a * b` where both are Int or both Nat.
namespace CostlyOps
scoped instance : HAdd Int Int (Costly Int 1) where hAdd := costlyAdd
scoped instance : HSub Int Int (Costly Int 1) where hSub := costlySub
scoped instance : HMul Int Int (Costly Int 100) where hMul := costlyMul
scoped instance : HAdd Nat Nat (Costly Int 1) where hAdd a b := costlyAdd ↑a ↑b
scoped instance : HSub Nat Nat (Costly Int 1) where hSub a b := costlySub ↑a ↑b
scoped instance : HMul Nat Nat (Costly Int 100) where hMul a b := costlyMul ↑a ↑b
end CostlyOps

-- ============================================================================
-- Part 4: Simple Examples
-- ============================================================================

-- `section` scopes the `open CostlyOps` so it doesn't leak to Part 5
section SimpleExamples
open CostlyOps

-- A single multiplication costs 100
def example1 : Costly Int 100 := 3 * 5

-- Two adds cost 1 + 1 = 2
def example2 : Costly Int 2 := cdo
  let x ← 10 + 20
  x + 5

-- `return` desugars to `Costly.pure`
def example2' : Costly Int 2 := cdo
  let x ← 10 + 20
  let y ← x + 5
  return y

-- Mixed chain: mul then add = 100 + 1 = 101
def example3 : Costly Int 101 := cdo
  let x ← 3 * 5
  x + 1

-- Dot product: (a*b) + (c*d) = 100 + 100 + 1 = 201
def dotProduct2 (a b c d : Int) : Costly Int 201 := cdo
  let ab ← a * b
  let cd ← c * d
  ab + cd

-- `let :=` for pure (cost-free) bindings
def withPureLet : Costly Int 101 := cdo
  let offset := (42 : Int)
  let x ← 3 * 5
  x + offset

-- `burn` consumes budget without computing anything
def paddedAdd : Costly Int 101 := cdo
  let x ← 3 + 5
  Costly.burn 100
  return x

-- Bare expression as sequencing (binds to _)
def withSequencing : Costly Int 101 := cdo
  Costly.burn 100
  3 + 5

-- Conditionals: both branches must have the same cost type
def conditionalExample (flag : Bool) : Costly Int 1 :=
  if flag then 1 + 2 else 10 - 3

-- Cost inference: Lean computes the exact cost automatically
def inferredCost := cdo
  let x ← 3 * 5
  x + 1
-- inferredCost : Costly Int 101

-- Budget relaxation: `cdo` auto-relaxes into any budget ≥ actual cost
abbrev CheapBinOp := Int → Int → Costly Int 5

-- Three additions cost 3, which fits in budget 5 — no `burn` needed
def threeAdds : CheapBinOp := fun a b => cdo
  let s ← a + b
  let d ← s + a
  let r ← d + b
  return r

-- Relaxation also works outside `cdo` via `.relax`
def relaxedAdd : Costly Int 10 := (costlyAdd 3 5).relax

-- A single mul (cost 100) does NOT fit in CheapBinOp (cost 5).
-- Uncomment to see the type error:
-- def tooExpensive : CheapBinOp := fun a b => a * b

end SimpleExamples

-- ============================================================================
-- Part 5: Costly Matrices
-- ============================================================================

/-- An n×m matrix of integers. -/
structure Matrix (n m : Nat) where
  get : Fin n → Fin m → Int

/-- Display a matrix. -/
def Matrix.toString (M : Matrix n m) : String :=
  let rows := (List.range n).map fun i =>
    if hi : i < n then
      let cols := (List.range m).map fun j =>
        if hj : j < m then
          let v := M.get ⟨i, hi⟩ ⟨j, hj⟩
          s!"{v}"
        else ""
      "  " ++ ", ".intercalate cols
    else ""
  "[\n" ++ "\n".intercalate rows ++ "\n]"

instance : ToString (Matrix n m) where toString := Matrix.toString

/-- Dot product of two length-k vectors. Cost: 101 * k.
    Uses explicit bind so that Lean's definitional reduction of `Nat.mul`
    (which recurses on the second argument) handles the cost equality:
    101 * (k+1) ≡ 101 * k + 101 ≡ 101 * k + (100 + 1). -/
def costlyDot : (k : Nat) → (Fin k → Int) → (Fin k → Int) → Costly Int (101 * k)
  | 0, _, _ => Costly.pure 0
  | k+1, a, b =>
    (costlyDot k (fun i => a i.castSucc) (fun i => b i.castSucc)).bind fun rest =>
    (costlyMul (a (Fin.last k)) (b (Fin.last k))).bind fun prod =>
    costlyAdd rest prod

/-- Apply a costly function at each index, collecting results. Cost: c * n.
    Uses explicit bind: c * (n+1) ≡ c * n + c ≡ c * n + (c + 0). -/
def costlyTabulate : (n : Nat) → (Fin n → Costly α c) → Costly (Fin n → α) (c * n)
  | 0, _ => Costly.pure Fin.elim0
  | n+1, f =>
    (costlyTabulate n (fun i => f i.castSucc)).bind fun init =>
    (f (Fin.last n)).bind fun last =>
    Costly.pure (fun i : Fin (n + 1) => if h : i.val < n then init ⟨i.val, h⟩ else last)

/-- Matrix multiplication: A(n×k) · B(k×m) = C(n×m).
    Cost: ((101 * k) * m) * n — one dot product per element. -/
def costlyMatMul (A : Matrix n k) (B : Matrix k m)
    : Costly (Matrix n m) (((101 * k) * m) * n) :=
  (costlyTabulate n fun i =>
    costlyTabulate m fun j =>
      costlyDot k (A.get i) (fun l => B.get l j)).map Matrix.mk

-- `*` on matrices returns a costly result
instance : HMul (Matrix n k) (Matrix k m) (Costly (Matrix n m) (((101 * k) * m) * n)) where
  hMul := costlyMatMul

-- Example matrices
private def matA : Matrix 2 3 := ⟨fun i j =>
  #[#[(1 : Int), 2, 3], #[4, 5, 6]][i.val]![j.val]!⟩

private def matB : Matrix 3 2 := ⟨fun i j =>
  #[#[(7 : Int), 8], #[9, 10], #[11, 12]][i.val]![j.val]!⟩

-- 2×3 · 3×2 = 2×2, cost = ((101 * 3) * 2) * 2 = 1212
def matMulExample : Costly (Matrix 2 2) (((101 * 3) * 2) * 2) := matA * matB

-- Matrix multiplication composes in cdo blocks
def chainedMatMul (A : Matrix n k) (B : Matrix k m) (C : Matrix m p)
    : Costly (Matrix n p) (((101 * k) * m) * n + ((101 * m) * p) * n) := cdo
  let AB ← A * B
  AB * C

-- ============================================================================
-- Part 6: Main Demo
-- ============================================================================

def main : IO Unit := do
  IO.println "=== CostlyResult: Compile-Time Cost Tracking ==="
  IO.println ""

  IO.println "--- Basic operations (cdo notation) ---"
  IO.println s!"costlyMul 3 5          = {example1.val}  (cost: 100)"
  IO.println s!"add 10 20, then add 5  = {example2.val}  (cost: 2)"
  IO.println s!"same with return       = {example2'.val}  (cost: 2)"
  IO.println s!"mul 3 5, then add 1    = {example3.val}  (cost: 101)"
  IO.println ""

  IO.println "--- Dot product: a*b + c*d ---"
  IO.println s!"dotProduct2 2 3 4 5    = {(dotProduct2 2 3 4 5).val}  (cost: 201)"
  IO.println ""

  IO.println "--- Pure let, burn, and sequencing ---"
  IO.println s!"withPureLet            = {withPureLet.val}  (cost: 101)"
  IO.println s!"add 3 5 + burn 100     = {paddedAdd.val}  (cost: 101)"
  IO.println s!"burn 100 then add 3 5  = {withSequencing.val}  (cost: 101)"
  IO.println ""

  IO.println "--- Conditionals ---"
  IO.println s!"conditional true       = {(conditionalExample true).val}  (cost: 1)"
  IO.println s!"conditional false      = {(conditionalExample false).val}  (cost: 1)"
  IO.println ""

  IO.println "--- Budget constraint: CheapBinOp = Int -> Int -> Costly Int 5 ---"
  IO.println s!"threeAdds 10 20        = {(threeAdds 10 20).val}  (cost: 5)"
  IO.println "costlyMul would need cost 100 — does NOT type-check as CheapBinOp!"
  IO.println ""

  IO.println "--- Matrix multiplication: (2×3) · (3×2) → (2×2) ---"
  IO.println s!"A (2×3) ={matA}"
  IO.println s!"B (3×2) ={matB}"
  IO.println s!"A · B   ={matMulExample.val}  (cost: {((101 * 3) * 2) * 2})"
  IO.println ""

  IO.println "All costs are enforced at compile time. Zero runtime overhead."

end CostlyResult
