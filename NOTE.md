# Type-Driven Matrix Multiplication: From Naive to Strassen

This project explores **compile-time cost tracking** via a graded monad (`Costly α n`)
in Lean 4, applied to matrix multiplication optimizations.

The type checker enforces cost budgets — every optimization must be *proven* correct
at the type level.

## Cost Model

| Operation | Cost |
|-----------|------|
| Addition / Subtraction | 1 |
| Multiplication | 100 |

## Progressive Optimizations

### 1. Standard multiplication — `costlyMatMul`

**Cost**: `((101 * k) * m) * n`

Each element of the n×m result matrix requires a dot product of length k:
k multiplications (100 each) + k additions (1 each) = 101k per element.

### 2. Skip redundant add-to-zero — `cheaperDot`

**Cost**: `((101 * k) * m) * n - 1`

The standard dot product starts with `Costly.pure 0` and adds the first product to it.
That initial addition is redundant. `cheaperDot` returns the first product directly
(cost 100 for k=1) and accumulates from there (cost 101 per subsequent element).

Saves 1 per dot product. Proof via `sub_one_mul_le : (a-1)*b ≤ a*b - 1`.

### 3. Saving two — case analysis

**Cost**: `((101 * k) * m) * n - 2`

Same `cheaperDot`, but relaxing to a budget 2 below standard.
The proof splits on `n * m ≥ 2`:

- **n ≥ 2**: chain `sub_one_mul_le` then `sub_one_mul_le_sub_two` (using n ≥ 2)
- **n = 1, m ≥ 2**: simplify `* 1`, apply `sub_one_mul_le_sub_two` (using m ≥ 2)
- **n = m = 1, k ≥ 1**: the single dot product has hard-minimum cost 101k − 1
  (k muls + k−1 adds), one unit above the target. The gap is absorbed by the
  `Costly` constructor.

### 4. Strassen — `strassenMul`

**Cost for 2×2**: 718 (vs standard 808)

Strassen's algorithm multiplies two 2×2 matrices using **7 multiplications**
instead of 8, at the cost of 18 extra additions:

```
M1 = (a+d)(e+h)    M2 = (c+d)·e      M3 = a·(f−h)     M4 = d·(g−e)
M5 = (a+b)·h       M6 = (c−a)(e+f)   M7 = (b−d)(g+h)

C₁₁ = M1+M4−M5+M7   C₁₂ = M3+M5
C₂₁ = M2+M4          C₂₂ = M1−M2+M3+M6
```

Cost: 7 × 100 + 18 × 1 = **718**. Net saving of 90 per 2×2 block.

### 5. Strassen–Winograd — `strassenWinogradMul`

**Cost for 2×2**: 715 (vs Strassen 718)

Same 7 multiplications, but reuses intermediate sums to cut additions from 18 to 15:

```
s₁ = a₂₁+a₂₂   s₂ = s₁−a₁₁    s₃ = a₁₁−a₂₁   s₄ = a₁₂−s₂
t₁ = b₁₂−b₁₁   t₂ = b₂₂−t₁    t₃ = b₂₂−b₁₂   t₄ = t₂−b₂₁

p₁ = a₁₁·b₁₁   p₂ = a₁₂·b₂₁   p₃ = s₄·b₂₂    p₄ = a₂₂·t₄
p₅ = s₁·t₁     p₆ = s₂·t₂     p₇ = s₃·t₃

C₁₁ = p₁+p₂                    C₁₂ = p₁+p₆+p₅+p₃
C₂₁ = p₁+p₆+p₇−p₄             C₂₂ = p₁+p₆+p₇+p₅
```

Cost: 7 × 100 + 15 × 1 = **715**.

### 6. Recursive Strassen for 4×4 — `strassenMul44`

**Cost for 4×4**: 5065 (vs standard 6464)

Splits each 4×4 matrix into four 2×2 blocks and applies Strassen–Winograd
at both levels:

- 8 block additions (2×2 = 4 ops each): 32
- 7 block multiplications (Strassen–Winograd, 715 each): 5005
- 7 block additions for output: 28
- **Total: 5065** (21.6% saving over standard 6464)

Verified at runtime: `strassenMul44` produces identical results to `costlyMatMul`.

## Theoretical Limits

### 7 multiplications for 2×2 is optimal

Winograd (1971) proved that no algorithm can multiply 2×2 matrices using
fewer than 7 scalar multiplications. The exponent log₂(7) ≈ 2.807 is therefore
a hard floor for any recursive 2×2 block decomposition.

### Larger blocks don't help (for known algorithms)

| Block size | Naive muls | Best known | Exponent | Beats Strassen? |
|-----------|-----------|------------|----------|-----------------|
| 2×2 | 8 | 7 (Strassen) | 2.807 | — |
| 3×3 | 27 | 23 (Laderman) | 2.854 | No |
| 4×4 | 64 | 49 (Strassen²) | 2.807 | Same |
| 5×5 | 125 | ~100 | ~2.861 | No |

To beat Strassen at block size 3, one would need ≤ 21 multiplications
(giving log₃(21) ≈ 2.771). The gap between 21 and the best known 23
is a major open problem.

### Random search confirms the difficulty

The `TensorSearch` module verifies decompositions and runs random searches:

- **6 muls for 2×2**: best score 45/64 after 100K trials (need 64)
- **7 muls for 2×2**: best score 41/64 — even *finding* Strassen randomly
  is nearly impossible (search space ≈ 10²⁰)
- **22 muls for 3×3**: best score 167/729 (search space ≈ 10²⁸³)

### The path to ω < 2.372

The current best bound (Duan–Wu–Zhou 2023) uses the **laser method** over
asymptotically large tensor powers — not a concrete finite block algorithm.
These are existence proofs: they show *some* algorithm achieves the bound,
but the algorithm itself is not explicitly constructable.

## Files

| File | Description |
|------|-------------|
| `CostlyResult.lean` | Graded monad, cost-tracked arithmetic, matrix multiply, Strassen |
| `TensorSearch.lean` | Tensor decomposition verifier and random search |
