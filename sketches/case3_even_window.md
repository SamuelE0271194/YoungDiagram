# Case 3, Even Rank: Window Inequality Proof

**Context:** We are in Case 3 (`2 ≤ X(g₁)`), inside the window `i ∈ {g₁.rank - 1, g₁.rank, g₁.rank + 1}`, and `g₁.rank` is even. The goal is `sigma Z i ≤ sigma Y i`. We know `Z = Pi.Y2 + rest` and `X.1 = Pi.X2 + rest`, so `sigma Z - sigma X = sigma(Pi.Y2) - sigma(Pi.X2)`, which is given by the window formula from `sigma_type2_same_rank`.

Since `g₁.rank` is even, `g₁.rank - 1` is odd, so `negOnePow(g₁.rank - 1) = -1`, giving `g₁.type = Negative` (by `hε₁`). The window differences are therefore:

| index | diff `sigma Z - sigma X` |
|---|---|
| `g₁.rank - 1` | `(1, 0)` |
| `g₁.rank`     | `(1, 1)` |
| `g₁.rank + 1` | `(0, 1)` |

---

## Step 1: Auxiliary inequalities for the .1 component

We need `a_i < c_i` (i.e. `(sigma X).1 < (sigma Y).1`) at `i = g₁.rank` and `i = g₁.rank - 1`. This uses the chain:

`c₁ - c_i ≤ d₀ - d_{i-1} ≤ b₀ - b_{i-1} = a₁ - a_i`

combined with `hstrict : d₀ - d₁ < b₀ - b₁` and `a₀ = c₀`.

```lean
-- c₁ - c_i ≤ d₀ - d_{i-1}  (from Sigma.a1_ai_le_b0_bi_1)
have hc1_ci_rank  := Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
have hc1_ci_rank1 := Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)

-- d₀ - d_{i-1} ≤ b₀ - b_{i-1}  (from sigma_zero equality + dominance at i-1)
have hd0_di_rank  : ... := by linarith [sigma_zero_snd_eq, hXY.le at (rank-1)]
have hd0_di_rank1 : ... := by linarith [sigma_zero_snd_eq, hXY.le at (rank-2)]

-- b₀ - b_{j-1} = a₁ - a_j  (from x_actual_negative_prefix_equalities)
have hb0_bi : ∀ j, 1 ≤ j → j ≤ g₁.rank → ... := x_actual_negative_prefix_equalities ...
have hb0_bi_rank  := hb0_bi g₁.rank ...
have hb0_bi_rank1 := hb0_bi (g₁.rank - 1) ...

-- Conclude a_i < c_i
have ha_lt_c_rank  : (sigma X g₁.rank).1     < (sigma Y g₁.rank).1     := by linarith [...]
have ha_lt_c_rank1 : (sigma X (g₁.rank-1)).1 < (sigma Y (g₁.rank-1)).1 := by linarith [...]
```

---

## Step 2: Auxiliary inequalities for the .2 component

We need `b_i < d_i` at `i = g₁.rank` and `i = g₁.rank + 1`. This uses the chain:

`d₂ - d_{i+1} ≤ c₁ - c_{i-1} ≤ d₀ - d_{i-2} ≤ b₀ - b_{i-2} = b₂ - b_{i+1}`

combined with `hd2_gt_b2 : b₂ < d₂`.

```lean
-- d₂ - d_{i+1} ≤ c₁ - c_i  (from Sigma.b2_bi_2_le_a1_ai)
have hd2_c1_rank  := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 hg₁_ge2
have hd2_c1_rank1 : ... -- by_cases on rank = 2, else b2_bi_2_le_a1_ai

-- chain to d₀ - d_{i-2}
have hd2_di1_rank  := hd2_c1_rank.trans  hc1_ci_rank
have hd2_di1_rank1 := hd2_c1_rank1.trans hc1_ci_rank1

-- a₁ - a_j = b₂ - b_{j+1}  (from x_actual_negative_prefix_equalities2)
have hb0_bi' : ∀ j, 2 ≤ j → j ≤ g₁.rank → ... := x_actual_negative_prefix_equalities2 ...
have ha1_ai_rank  := hb0_bi' g₁.rank ...
have ha1_ai_rank1 : ... -- by_cases on rank = 2

-- b₀ - b_{i-2} = b₂ - b_{i+1}
have hb0_b2_rank  := hb0_bi_rank.trans  ha1_ai_rank
have hb0_b2_rank1 := hb0_bi_rank1.trans ha1_ai_rank1

-- Conclude b_i < d_i
have hb_lt_d_rank  : (sigma X g₁.rank).2     < (sigma Y g₁.rank).2     := by linarith [...]
have hb_lt_d_rank1 : (sigma X (g₁.rank+1)).2 < (sigma Y (g₁.rank+1)).2 := by linarith [...]
```

---

## Step 3: Window difference formula

The difference `sigma Z i - sigma X i` equals `sigma(Pi.Y2) i - sigma(Pi.X2) i` (rest cancels). Apply `hwindow` from `sigma_type2_same_rank`, then simplify using `g₁.type ≠ Positive` (which follows from `heven` and `hε₁` via `Int.even_coe_nat`).

```lean
have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
    if i = g₁.rank then (1, 1)
    else if i = g₁.rank - 1 then (1, 0)
    else (0, 1) := by
  rw [hZ_split, hX_split, add_sub_add_right_eq_sub]
  have hibounds : g₁.rank - 1 ≤ i ∧ i ≤ g₁.rank + 1 := by
    rcases hi_range with rfl | rfl | rfl <;> omega
  rw [hwindow i hibounds.1 hibounds.2]
  have htype_neg : g₁.type ≠ .Positive := by
    intro h; apply hε₁
    have h_odd : ¬ Even ((g₁.rank : ℤ) - 1) := by
      simp [Int.even_sub, Int.even_coe_nat, heven]
    simp only [GeneType.negOnePow_smul, GeneType.neg_negative,
               GeneType.neg_positive, if_neg h_odd, h]
  simp [if_neg htype_neg]
```

---

## Step 4: Three sub-cases

For each `i`, simplify `hZX_diff`, derive `sigma Z = sigma X + diff` via component-wise `ext`, rewrite the goal, then close each component.

### i = g₁.rank - 1  (diff = (1, 0))

The `.1` component gets a `+1`, handled by `ha_lt_c_rank1` and `sigma_isNat` integrality. The `.2` component gets `+0`, handled by `hXY_i.2`.

```lean
-- diff simplifies to (1, 0)
simpa [show g₁.rank - 1 ≠ g₁.rank from by omega] using hZX_diff
-- .1: (sigma X).1 + 1 ≤ (sigma Y).1
exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank1)
-- .2: (sigma X).2 + 0 ≤ (sigma Y).2
linarith [hXY_i.2]
```

### i = g₁.rank  (diff = (1, 1))

Both components get `+1`; use `ha_lt_c_rank` for `.1` and `hb_lt_d_rank` for `.2`.

```lean
-- diff simplifies to (1, 1)
simpa using hZX_diff
-- .1: exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank)
-- .2: exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank)
```

### i = g₁.rank + 1  (diff = (0, 1))

The `.1` component gets `+0`, handled by `hXY_i.1`. The `.2` component gets `+1`, handled by `hb_lt_d_rank1`.

```lean
-- diff simplifies to (0, 1)
simpa [show g₁.rank + 1 ≠ g₁.rank from by omega,
       show g₁.rank + 1 ≠ g₁.rank - 1 from by omega] using hZX_diff
-- .1: linarith [hXY_i.1]
-- .2: exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank1)
```
