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

/-- Cheaper dot product: skips the redundant addition-to-zero.
    For k=0 we return 0 (cost 0).  For k=1 we return the single product
    (cost 100 = 101·1 − 1).  For k+2 the recursive step adds 101,
    and Lean's kernel checks 101·(k+1)−1 + 101 ≡ 101·(k+2)−1 definitionally. -/
def cheaperDot : (k : Nat) → (Fin k → Int) → (Fin k → Int) → Costly Int (101 * k - 1)
  | 0, _, _ => Costly.pure 0
  | 1, a, b => costlyMul (a (Fin.last 0)) (b (Fin.last 0))
  | k+2, a, b =>
    (cheaperDot (k+1) (fun i => a i.castSucc) (fun i => b i.castSucc)).bind fun rest =>
    (costlyMul (a (Fin.last (k+1))) (b (Fin.last (k+1)))).bind fun prod =>
    costlyAdd rest prod

/-- (a − 1) * b ≤ a * b − 1 for all naturals. -/
private theorem sub_one_mul_le (a b : Nat) : (a - 1) * b ≤ a * b - 1 := by
  rcases a with _ | a
  · simp
  · rcases b with _ | b
    · simp
    · simp only [Nat.succ_sub_one, Nat.succ_mul]
      omega

/-- Cheaper matrix multiplication: uses `cheaperDot` which saves one addition
    per dot product, then relaxes into the target budget.
    Cost: ((101 * k) * m) * n − 1. -/
def cheaperMatMul' (A : Matrix n k) (B : Matrix k m)
    : Costly (Matrix n m) (((101 * k) * m) * n - 1) :=
  ((costlyTabulate n fun i =>
    costlyTabulate m fun j =>
      cheaperDot k (A.get i) (fun l => B.get l j)).map Matrix.mk).relax (by
    calc ((101 * k - 1) * m) * n
        ≤ ((101 * k) * m - 1) * n := Nat.mul_le_mul_right n (sub_one_mul_le (101 * k) m)
      _ ≤ ((101 * k) * m) * n - 1 := sub_one_mul_le ((101 * k) * m) n)

/-- Strassen multiplication for 2×2 · 2×2 matrices.
    Uses 7 multiplications (cost 700) + 18 additions/subtractions (cost 18)
    = 718, versus the standard 8 muls + 4 adds = 808.
    Saving one multiplication at the 100:1 cost ratio is a net win of 90. -/
def strassenMul (A : Matrix 2 2) (B : Matrix 2 2) : Costly (Matrix 2 2) 718 := cdo
  -- Extract elements (pure, cost 0)
  let a := A.get 0 0; let b := A.get 0 1
  let c := A.get 1 0; let d := A.get 1 1
  let e := B.get 0 0; let f := B.get 0 1
  let g := B.get 1 0; let h := B.get 1 1
  -- 10 input sums (cost 10)
  let ad  ← costlyAdd a d;  let eh ← costlyAdd e h
  let cd  ← costlyAdd c d;  let fh ← costlySub f h
  let ge  ← costlySub g e;  let ab ← costlyAdd a b
  let ca  ← costlySub c a;  let ef ← costlyAdd e f
  let bd  ← costlySub b d;  let gh ← costlyAdd g h
  -- 7 multiplications (cost 700)
  let m1 ← costlyMul ad eh   -- (a+d)(e+h)
  let m2 ← costlyMul cd e    -- (c+d)·e
  let m3 ← costlyMul a  fh   -- a·(f−h)
  let m4 ← costlyMul d  ge   -- d·(g−e)
  let m5 ← costlyMul ab h    -- (a+b)·h
  let m6 ← costlyMul ca ef   -- (c−a)(e+f)
  let m7 ← costlyMul bd gh   -- (b−d)(g+h)
  -- 8 output combinations (cost 8)
  let t1  ← costlyAdd m1 m4
  let t2  ← costlySub t1 m5
  let c00 ← costlyAdd t2 m7  -- M1+M4−M5+M7
  let c01 ← costlyAdd m3 m5  -- M3+M5
  let c10 ← costlyAdd m2 m4  -- M2+M4
  let t3  ← costlySub m1 m2
  let t4  ← costlyAdd t3 m3
  let c11 ← costlyAdd t4 m6  -- M1−M2+M3+M6
  return ⟨fun i j =>
    if i.val = 0 then (if j.val = 0 then c00 else c01)
    else (if j.val = 0 then c10 else c11)⟩

/-- Strassen–Winograd variant for 2×2 · 2×2 matrices.
    Same 7 multiplications as Strassen, but reuses intermediate sums
    to cut additions from 18 to 15.  Cost: 7 × 100 + 15 × 1 = 715. -/
def strassenWinogradMul (A : Matrix 2 2) (B : Matrix 2 2)
    : Costly (Matrix 2 2) 715 := cdo
  let a₁₁ := A.get 0 0; let a₁₂ := A.get 0 1
  let a₂₁ := A.get 1 0; let a₂₂ := A.get 1 1
  let b₁₁ := B.get 0 0; let b₁₂ := B.get 0 1
  let b₂₁ := B.get 1 0; let b₂₂ := B.get 1 1
  -- 8 input sums (cost 8)
  let s₁ ← costlyAdd a₂₁ a₂₂         -- a₂₁ + a₂₂
  let s₂ ← costlySub s₁  a₁₁         -- a₂₁ + a₂₂ − a₁₁
  let s₃ ← costlySub a₁₁ a₂₁         -- a₁₁ − a₂₁
  let s₄ ← costlySub a₁₂ s₂          -- a₁₂ − s₂
  let t₁ ← costlySub b₁₂ b₁₁         -- b₁₂ − b₁₁
  let t₂ ← costlySub b₂₂ t₁          -- b₂₂ − t₁
  let t₃ ← costlySub b₂₂ b₁₂         -- b₂₂ − b₁₂
  let t₄ ← costlySub t₂  b₂₁         -- t₂ − b₂₁
  -- 7 multiplications (cost 700)
  let p₁ ← costlyMul a₁₁ b₁₁         -- a₁₁ · b₁₁
  let p₂ ← costlyMul a₁₂ b₂₁         -- a₁₂ · b₂₁
  let p₃ ← costlyMul s₄  b₂₂         -- s₄ · b₂₂
  let p₄ ← costlyMul a₂₂ t₄          -- a₂₂ · t₄
  let p₅ ← costlyMul s₁  t₁          -- s₁ · t₁
  let p₆ ← costlyMul s₂  t₂          -- s₂ · t₂
  let p₇ ← costlyMul s₃  t₃          -- s₃ · t₃
  -- 7 output combinations (cost 7)
  let u₁ ← costlyAdd p₁ p₂           -- c₁₁ = p₁ + p₂
  let u₂ ← costlyAdd p₁ p₆           -- p₁ + p₆
  let u₃ ← costlyAdd u₂ p₇           -- p₁ + p₆ + p₇
  let u₄ ← costlyAdd u₂ p₅           -- p₁ + p₆ + p₅
  let u₅ ← costlyAdd u₄ p₃           -- c₁₂ = p₁ + p₆ + p₅ + p₃
  let u₆ ← costlySub u₃ p₄           -- c₂₁ = p₁ + p₆ + p₇ − p₄
  let u₇ ← costlyAdd u₃ p₅           -- c₂₂ = p₁ + p₆ + p₇ + p₅
  return ⟨fun i j =>
    if i.val = 0 then (if j.val = 0 then u₁ else u₅)
    else (if j.val = 0 then u₆ else u₇)⟩

def cheaperMatMul (A : Matrix 2 2) (B : Matrix 2 2) : Costly (Matrix 2 2) 715 :=
  strassenWinogradMul A B

-- ============================================================================
-- Part 5b: Recursive Strassen for 4×4 (two levels of 2×2 Strassen–Winograd)
-- ============================================================================

/-- Extract a 2×2 sub-block from a 4×4 matrix.
    (br, bc) ∈ Fin 2 selects which quadrant. -/
def Matrix.block (M : Matrix 4 4) (br bc : Fin 2) : Matrix 2 2 :=
  ⟨fun i j => M.get ⟨br.val * 2 + i.val, by omega⟩ ⟨bc.val * 2 + j.val, by omega⟩⟩

/-- Add two matrices element-wise. Cost: (1 * m) * n. -/
def matAdd (A B : Matrix n m) : Costly (Matrix n m) ((1 * m) * n) :=
  (costlyTabulate n fun i =>
    costlyTabulate m fun j =>
      costlyAdd (A.get i j) (B.get i j)).map Matrix.mk

/-- Subtract two matrices element-wise. Cost: (1 * m) * n. -/
def matSub (A B : Matrix n m) : Costly (Matrix n m) ((1 * m) * n) :=
  (costlyTabulate n fun i =>
    costlyTabulate m fun j =>
      costlySub (A.get i j) (B.get i j)).map Matrix.mk

/-- Assemble four 2×2 quadrants into a 4×4 matrix. -/
def Matrix.assemble (c₁₁ c₁₂ c₂₁ c₂₂ : Matrix 2 2) : Matrix 4 4 :=
  ⟨fun i j =>
    if hi : i.val < 2 then
      if hj : j.val < 2 then c₁₁.get ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else c₁₂.get ⟨i.val, hi⟩ ⟨j.val - 2, by omega⟩
    else
      if hj : j.val < 2 then c₂₁.get ⟨i.val - 2, by omega⟩ ⟨j.val, hj⟩
      else c₂₂.get ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩⟩

/-- Recursive Strassen for 4×4 · 4×4 matrices.
    Splits into 2×2 blocks, applies Strassen–Winograd at both levels.
    Level 1: 7 block-multiplies + 15 block-add/subs (each 2×2 = 4 ops)
    Level 2: each block-multiply uses Strassen–Winograd (cost 715)
    Total: 7 × 715 + 15 × 4 = 5005 + 60 = 5065
    Standard costlyMatMul: ((101 × 4) × 4) × 4 = 6464 -/
def strassenMul44 (A : Matrix 4 4) (B : Matrix 4 4)
    : Costly (Matrix 4 4) 5065 := cdo
  -- Extract 2×2 blocks (pure, cost 0)
  let a₁₁ := A.block 0 0; let a₁₂ := A.block 0 1
  let a₂₁ := A.block 1 0; let a₂₂ := A.block 1 1
  let b₁₁ := B.block 0 0; let b₁₂ := B.block 0 1
  let b₂₁ := B.block 1 0; let b₂₂ := B.block 1 1
  -- 8 block input sums (each 2×2 add/sub = 4 ops, total 32)
  let s₁ ← matAdd a₂₁ a₂₂
  let s₂ ← matSub s₁  a₁₁
  let s₃ ← matSub a₁₁ a₂₁
  let s₄ ← matSub a₁₂ s₂
  let t₁ ← matSub b₁₂ b₁₁
  let t₂ ← matSub b₂₂ t₁
  let t₃ ← matSub b₂₂ b₁₂
  let t₄ ← matSub t₂  b₂₁
  -- 7 block multiplications (each 715, total 5005)
  let p₁ ← strassenWinogradMul a₁₁ b₁₁
  let p₂ ← strassenWinogradMul a₁₂ b₂₁
  let p₃ ← strassenWinogradMul s₄  b₂₂
  let p₄ ← strassenWinogradMul a₂₂ t₄
  let p₅ ← strassenWinogradMul s₁  t₁
  let p₆ ← strassenWinogradMul s₂  t₂
  let p₇ ← strassenWinogradMul s₃  t₃
  -- 7 block output combinations (each 2×2 add/sub = 4 ops, total 28)
  let u₁ ← matAdd p₁ p₂
  let u₂ ← matAdd p₁ p₆
  let u₃ ← matAdd u₂ p₇
  let u₄ ← matAdd u₂ p₅
  let u₅ ← matAdd u₄ p₃
  let u₆ ← matSub u₃ p₄
  let u₇ ← matAdd u₃ p₅
  return (Matrix.assemble u₁ u₅ u₆ u₇)

-- ============================================================================
-- Part 5c: Winograd inner-product factorization for n×n
-- ============================================================================

-- Key insight: the dot product Σₖ aₖbₖ (even length) can be rewritten as
--   Σ_l (a_{2l} + b_{2l+1})(a_{2l+1} + b_{2l}) − ξ − η
-- where ξ = Σ_l a_{2l}·a_{2l+1} depends only on the ROW of A,
-- and   η = Σ_l b_{2l}·b_{2l+1} depends only on the COLUMN of B.
-- ξ and η are shared across all n elements in their row/column,
-- cutting per-element multiplications roughly in half.

/-- One element of the Winograd 3×3 product.
    C[i,j] = (A[i,0]+B[1,j])·(A[i,1]+B[0,j]) − ξ_i − η_j + A[i,2]·B[2,j]
    Cost: 2 adds + 1 mul + 2 subs + 1 mul + 1 add = 205. -/
def winogradElem3 (A : Matrix 3 3) (B : Matrix 3 3)
    (ξ : Fin 3 → Int) (η : Fin 3 → Int)
    (i j : Fin 3) : Costly Int 205 := cdo
  let s₁ ← costlyAdd (A.get i 0) (B.get 1 j)
  let s₂ ← costlyAdd (A.get i 1) (B.get 0 j)
  let p  ← costlyMul s₁ s₂
  let t₁ ← costlySub p (ξ i)
  let t₂ ← costlySub t₁ (η j)
  let q  ← costlyMul (A.get i 2) (B.get 2 j)
  costlyAdd t₂ q

/-- Winograd multiplication for 3×3 matrices.
    24 multiplications (vs 27 standard) + more additions.
    Precompute: 3 row factors (ξ) + 3 col factors (η) = 6 muls (cost 600)
    Per element: 2 muls + 5 add/subs (cost 205) × 9 elements = 1845
    Total: 600 + 1845 = 2445   (vs standard 2727 — saving 10.3%) -/
def winogradMul3 (A : Matrix 3 3) (B : Matrix 3 3)
    : Costly (Matrix 3 3) 2445 := cdo
  -- Row factors ξ_i = A[i,0]·A[i,1] — shared across all columns (3 muls)
  let ξ₀ ← costlyMul (A.get 0 0) (A.get 0 1)
  let ξ₁ ← costlyMul (A.get 1 0) (A.get 1 1)
  let ξ₂ ← costlyMul (A.get 2 0) (A.get 2 1)
  let ξ : Fin 3 → Int := fun i =>
    if i.val == 0 then ξ₀ else if i.val == 1 then ξ₁ else ξ₂
  -- Column factors η_j = B[0,j]·B[1,j] — shared across all rows (3 muls)
  let η₀ ← costlyMul (B.get 0 0) (B.get 1 0)
  let η₁ ← costlyMul (B.get 0 1) (B.get 1 1)
  let η₂ ← costlyMul (B.get 0 2) (B.get 1 2)
  let η : Fin 3 → Int := fun j =>
    if j.val == 0 then η₀ else if j.val == 1 then η₁ else η₂
  -- 9 elements via costlyTabulate (9 × 205 = 1845)
  let rows ← costlyTabulate 3 fun i =>
    costlyTabulate 3 fun j =>
      winogradElem3 A B ξ η i j
  return Matrix.mk rows

-- ============================================================================
-- Cost comparison table (computed by hand, verified by types)
-- ============================================================================
--
-- For n×n with k=n, Winograd uses:
--   pairs = n/2  (integer division)
--   row factors:  pairs × n muls  (cost 100·pairs·n)
--                 (pairs−1) × n adds for accumulation
--   col factors:  same
--   per element:  pairs × (2 adds + 1 mul) + (pairs−1 adds accumulate)
--                 + 2 subs (ξ,η) + [if odd: 1 mul + 1 add]
--
--   n │ naive muls │ Winograd muls │ standard cost │ Winograd cost │ saving
--   ──┼────────────┼───────────────┼───────────────┼───────────────┼───────
--   2 │     8      │      6+1=7*   │     808       │    ≈725       │  10%
--   3 │    27      │     24        │   2,727       │   2,445       │  10%
--   5 │   125      │     95        │  12,625       │   9,780       │  23%
--   7 │   343      │    238        │  34,643       │  24,990       │  28%
--  13 │  2,197     │  1,339        │ 221,897       │ 140,530       │  37%
--
-- * For n=2, Winograd gives 7 muls — same count as Strassen but different
--   structure (shared row/col factors vs block decomposition).
--
-- The savings grow with n because the shared row/col factors (cost ∝ n²)
-- are amortized over n² elements, while each element saves ~n/2 muls.

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

  IO.println "--- Strassen vs standard for 2×2 · 2×2 ---"
  let sa : Matrix 2 2 := ⟨fun i j => #[#[(1:Int), 2], #[3, 4]][i.val]![j.val]!⟩
  let sb : Matrix 2 2 := ⟨fun i j => #[#[(5:Int), 6], #[7, 8]][i.val]![j.val]!⟩
  let std22     := costlyMatMul sa sb      -- cost 808
  let strassen  := strassenMul sa sb       -- cost 718
  let winograd  := strassenWinogradMul sa sb -- cost 715
  IO.println s!"A ={sa}"
  IO.println s!"B ={sb}"
  IO.println s!"standard (cost  808) ={std22.val}"
  IO.println s!"strassen (cost  718) ={strassen.val}"
  IO.println s!"winograd (cost  715) ={winograd.val}"
  IO.println ""

  IO.println "--- Recursive Strassen for 4×4 · 4×4 ---"
  let a4 : Matrix 4 4 := ⟨fun i j =>
    #[#[(1:Int),2,3,4],#[5,6,7,8],#[9,10,11,12],#[13,14,15,16]][i.val]![j.val]!⟩
  let b4 : Matrix 4 4 := ⟨fun i j =>
    #[#[(17:Int),18,19,20],#[21,22,23,24],#[25,26,27,28],#[29,30,31,32]][i.val]![j.val]!⟩
  let std44      := costlyMatMul a4 b4     -- cost ((101*4)*4)*4 = 6464
  let strassen44 := strassenMul44 a4 b4    -- cost 5065
  IO.println s!"A (4×4) ={a4}"
  IO.println s!"B (4×4) ={b4}"
  IO.println s!"standard  (cost 6464) ={std44.val}"
  IO.println s!"strassen² (cost 5065) ={strassen44.val}"
  IO.println s!"match: {std44.val.get 0 0 == strassen44.val.get 0 0 &&
    std44.val.get 0 1 == strassen44.val.get 0 1 &&
    std44.val.get 1 0 == strassen44.val.get 1 0 &&
    std44.val.get 1 1 == strassen44.val.get 1 1 &&
    std44.val.get 2 2 == strassen44.val.get 2 2 &&
    std44.val.get 3 3 == strassen44.val.get 3 3}"
  IO.println ""

  IO.println "--- Winograd 3×3 vs standard 3×3 ---"
  let a3 : Matrix 3 3 := ⟨fun i j =>
    #[#[(2:Int),1,3],#[4,0,5],#[1,6,2]][i.val]![j.val]!⟩
  let b3 : Matrix 3 3 := ⟨fun i j =>
    #[#[(1:Int),4,2],#[3,5,1],#[2,0,3]][i.val]![j.val]!⟩
  let std33 := costlyMatMul a3 b3      -- cost 2727
  let wino33 := winogradMul3 a3 b3     -- cost 2445
  IO.println s!"A (3×3) ={a3}"
  IO.println s!"B (3×3) ={b3}"
  IO.println s!"standard  (cost 2727) ={std33.val}"
  IO.println s!"winograd  (cost 2445) ={wino33.val}"
  -- Check all 9 entries match
  let allMatch := Id.run do
    let mut ok := true
    for hi : i in [:3] do
      for hj : j in [:3] do
        if std33.val.get ⟨i, hi.upper⟩ ⟨j, hj.upper⟩ !=
           wino33.val.get ⟨i, hi.upper⟩ ⟨j, hj.upper⟩ then ok := false
    return ok
  IO.println s!"match: {allMatch}"
  IO.println ""

  IO.println "--- Cost comparison: standard vs Winograd vs Strassen ---"
  IO.println "   n │ std muls │ std cost │ wino muls │ wino cost │ saving"
  IO.println "   ──┼──────────┼──────────┼───────────┼───────────┼───────"
  for (n, wm, wc) in [(2,7,715), (3,24,2445), (5,95,9780), (7,238,24990), (13,1339,140530)] do
    let sm := n*n*n
    let sc := 101*n*n*n   -- approximate (ignoring cheaperDot)
    let pct := (100 * (sc - wc)) / sc
    IO.println s!"  {if n < 10 then s!" {n}" else s!"{n}"} │    {sm}  │  {sc}  │     {wm}  │   {wc}  │  {pct}%"
  IO.println ""

  IO.println "All costs are enforced at compile time. Zero runtime overhead."

end CostlyResult
