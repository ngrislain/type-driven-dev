-- TensorSearch — Systematic search for low-rank decompositions of the
-- matrix multiplication tensor ⟨n,n,n⟩.
--
-- The matrix multiplication tensor T(n) encodes the bilinear map
-- (A, B) ↦ A·B for n×n matrices.  A rank-r decomposition of T(n)
-- yields an algorithm that computes n×n matrix multiplication using
-- exactly r scalar multiplications (plus additions).
--
-- Strassen's result: rank(T(2)) = 7, giving exponent log₂(7) ≈ 2.807.
-- Open question: can we find rank(T(3)) < 23?  (Best known: 23, Laderman 1976.)
-- To beat Strassen's exponent at block size 3, we need rank ≤ 21.

-- ============================================================================
-- Part 1: Tensor representation
-- ============================================================================

/-- A triple (u, v, w) representing one rank-1 term of the decomposition.
    u[i,k] v[k,j] w[i,j] means: multiply (Σᵢₖ uᵢₖ·Aᵢₖ) by (Σₖⱼ vₖⱼ·Bₖⱼ)
    and add the result scaled by wᵢⱼ to Cᵢⱼ.
    Coefficients are -1, 0, or 1 to keep things simple. -/
structure TrilinearTerm (n : Nat) where
  u : Fin n → Fin n → Int  -- coefficients for A
  v : Fin n → Fin n → Int  -- coefficients for B
  w : Fin n → Fin n → Int  -- coefficients for C (output routing)

/-- A decomposition of the matrix multiplication tensor into r terms. -/
structure TensorDecomp (n r : Nat) where
  terms : Fin r → TrilinearTerm n

-- Helper to make terms from nested lists
def mkTerm (n : Nat) (u v w : List (List Int)) : TrilinearTerm n :=
  { u := fun i k => (u.getD i.val []).getD k.val 0
    v := fun k j => (v.getD k.val []).getD j.val 0
    w := fun i j => (w.getD i.val []).getD j.val 0 }

-- ============================================================================
-- Part 2: Verification
-- ============================================================================

/-- Compute how many of the n⁶ tensor entries are correctly reproduced.
    The tensor T(n) has T[i,k,k',j,i',j'] = δ(i,i')·δ(j,j')·δ(k,k').
    A decomposition contributes: Σ_t u_t[i,k] · v_t[k',j] · w_t[i',j']. -/
def TensorDecomp.score (d : TensorDecomp n r) : Nat := Id.run do
  let mut correct : Nat := 0
  for hi : i in [:n] do
    for hj : j in [:n] do
      for hk : k in [:n] do
        for hk' : k' in [:n] do
          for hi' : i' in [:n] do
            for hj' : j' in [:n] do
              let target : Int := if i == i' && j == j' && k == k' then 1 else 0
              let mut sum : Int := 0
              for ht : t in [:r] do
                let term := d.terms ⟨t, ht.upper⟩
                sum := sum + term.u ⟨i, hi.upper⟩ ⟨k, hk.upper⟩ *
                            term.v ⟨k', hk'.upper⟩ ⟨j, hj.upper⟩ *
                            term.w ⟨i', hi'.upper⟩ ⟨j', hj'.upper⟩
              if sum == target then correct := correct + 1
  return correct

def TensorDecomp.isCorrect (d : TensorDecomp n r) : Bool :=
  d.score == n ^ 6

-- ============================================================================
-- Part 3: Known decompositions
-- ============================================================================

/-- Standard 2×2 multiplication: 8 terms (one per scalar multiply). -/
def standardDecomp2 : TensorDecomp 2 8 :=
  { terms := fun t =>
      let (i, k, j) := match t.val with
        | 0 => (0,0,0) | 1 => (0,0,1) | 2 => (0,1,0) | 3 => (0,1,1)
        | 4 => (1,0,0) | 5 => (1,0,1) | 6 => (1,1,0) | _ => (1,1,1)
      { u := fun r c => if r.val == i && c.val == k then 1 else 0
        v := fun r c => if r.val == k && c.val == j then 1 else 0
        w := fun r c => if r.val == i && c.val == j then 1 else 0 } }

/-- Strassen decomposition: 7 terms for 2×2 multiplication.
    M1=(a+d)(e+h), M2=(c+d)e, M3=a(f-h), M4=d(g-e),
    M5=(a+b)h, M6=(c-a)(e+f), M7=(b-d)(g+h)
    C₁₁=M1+M4-M5+M7, C₁₂=M3+M5, C₂₁=M2+M4, C₂₂=M1-M2+M3+M6 -/
def strassenDecomp : TensorDecomp 2 7 :=
  let t := mkTerm 2
  { terms := fun idx => match idx.val with
      -- C₁₁=M1+M4-M5+M7, C₁₂=M3+M5, C₂₁=M2+M4, C₂₂=M1-M2+M3+M6
      | 0 => t [[1,0],[0,1]]  [[1,0],[0,1]]   [[1,0],[0,1]]    -- M1 → C₁₁+, C₂₂+
      | 1 => t [[0,0],[1,1]]  [[1,0],[0,0]]   [[0,0],[1,-1]]   -- M2 → C₂₁+, C₂₂−
      | 2 => t [[1,0],[0,0]]  [[0,1],[0,-1]]  [[0,1],[0,1]]    -- M3 → C₁₂+, C₂₂+
      | 3 => t [[0,0],[0,1]]  [[-1,0],[1,0]]  [[1,0],[1,0]]    -- M4
      | 4 => t [[1,1],[0,0]]  [[0,0],[0,1]]   [[-1,1],[0,0]]   -- M5
      | 5 => t [[-1,0],[1,0]] [[1,1],[0,0]]   [[0,0],[0,1]]    -- M6
      | _ => t [[0,1],[0,-1]] [[0,0],[1,1]]   [[1,0],[0,0]] }  -- M7

-- ============================================================================
-- Part 4: Random search
-- ============================================================================

/-- Simple LCG random number generator. -/
structure RNG where
  state : UInt64

def RNG.next (rng : RNG) : RNG × UInt64 :=
  let s := rng.state * 6364136223846793005 + 1442695040888963407
  (⟨s⟩, s)

def RNG.randCoeff (rng : RNG) : RNG × Int :=
  let (rng', v) := rng.next
  let r := v.toNat % 3
  (rng', if r == 0 then -1 else if r == 1 then 0 else 1)

/-- Generate a random decomposition. -/
def randomDecomp (n r : Nat) (rng : RNG) : RNG × TensorDecomp n r := Id.run do
  let mut rng := rng
  let mut allTerms : Array (Array (Array Int)) := #[]  -- r × 3 × n²
  for _ in [:r] do
    let mut matrices : Array (Array Int) := #[]
    for _ in [:3] do  -- u, v, w
      let mut coeffs : Array Int := #[]
      for _ in [:n * n] do
        let (rng', c) := rng.randCoeff; rng := rng'
        coeffs := coeffs.push c
      matrices := matrices.push coeffs
    allTerms := allTerms.push matrices
  let decomp : TensorDecomp n r :=
    { terms := fun idx =>
        let data := allTerms.getD idx.val #[]
        let uData := data.getD 0 #[]
        let vData := data.getD 1 #[]
        let wData := data.getD 2 #[]
        { u := fun i k => uData.getD (i.val * n + k.val) 0
          v := fun k j => vData.getD (k.val * n + j.val) 0
          w := fun i j => wData.getD (i.val * n + j.val) 0 } }
  (rng, decomp)

-- ============================================================================
-- Part 5: Main
-- ============================================================================

def main : IO Unit := do
  IO.println "=== TensorSearch: Matrix Multiplication Tensor Decompositions ==="
  IO.println ""

  IO.println "--- Verifying standard 2×2 decomposition (8 muls) ---"
  IO.println s!"  correct: {standardDecomp2.isCorrect}  (score: {standardDecomp2.score}/64)"

  IO.println "--- Verifying Strassen 2×2 decomposition (7 muls) ---"
  IO.println s!"  correct: {strassenDecomp.isCorrect}  (score: {strassenDecomp.score}/64)"
  IO.println ""

  -- Random search for 6-mul 2×2 decomposition (known impossible)
  IO.println "--- Random search: 2×2 with 6 muls (Winograd proved impossible) ---"
  let mut rng : RNG := ⟨42⟩
  let mut bestScore6 : Nat := 0
  let trials := 100000
  for _ in [:trials] do
    let (rng', decomp) := randomDecomp 2 6 rng
    rng := rng'
    let s := decomp.score
    if s > bestScore6 then bestScore6 := s
  IO.println s!"  best score after {trials} trials: {bestScore6}/64  (need 64 for correct)"
  IO.println ""

  -- Random search for 7-mul 2×2 decomposition
  IO.println "--- Random search: 2×2 with 7 muls ---"
  let mut bestScore7 : Nat := 0
  let mut found7 : Nat := 0
  for _ in [:trials] do
    let (rng', decomp) := randomDecomp 2 7 rng
    rng := rng'
    let s := decomp.score
    if s > bestScore7 then bestScore7 := s
    if s == 64 then found7 := found7 + 1
  IO.println s!"  best score after {trials} trials: {bestScore7}/64"
  IO.println s!"  found correct: {found7}"
  IO.println ""

  -- Random search for 22-mul 3×3 (to beat Laderman's 23)
  IO.println "--- Random search: 3×3 with 22 muls (best known: 23, Laderman) ---"
  let mut bestScore22 : Nat := 0
  let trials3 := 10000
  for _ in [:trials3] do
    let (rng', decomp) := randomDecomp 3 22 rng
    rng := rng'
    let s := decomp.score
    if s > bestScore22 then bestScore22 := s
  IO.println s!"  best score after {trials3} trials: {bestScore22}/729  (need 729)"
  IO.println ""

  IO.println "--- Theoretical bounds ---"
  IO.println "  rank(T(2)) = 7   (Strassen 1969, optimal by Winograd 1971)"
  IO.println "  rank(T(3)) ≤ 23  (Laderman 1976, lower bound ≥ 19)"
  IO.println ""
  IO.println "  To beat Strassen's exponent log₂(7) ≈ 2.807:"
  IO.println "    block 3: need rank ≤ 21  → log₃(21) ≈ 2.771"
  IO.println "    block 4: need rank ≤ 48  → log₄(48) ≈ 2.795"
  IO.println "    block 5: need rank ≤ 91  → log₅(91) ≈ 2.804"
  IO.println ""
  IO.println "  Random search over {-1,0,1} coefficients is far too naive —"
  IO.println "  search space is 3^(3·n²·r), e.g., 3^(3·9·22) ≈ 10^283 for 3×3."
