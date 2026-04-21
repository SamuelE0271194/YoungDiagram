# Case 1 Proof Framework — §15.10 of Djoković (line 497)

## Hypotheses available at line 497

| Name | Type |
|------|------|
| `g₁ : Gene` | Gene of minimal rank `m := g₁.rank` in X |
| `hε₁` | `g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative` |
| `hXg₁pos` | `0 < X.1.val g₁` |
| `hg₁min` | `∀ x' ∈ X.1.val.support, g₁.rank ≤ x'.rank` |
| `g₂ : Gene` | A gene with ofRankAlt-Positive type in X |
| `hg₂type` | `g₂.type = Int.negOnePow (g₂.rank - 1) • GeneType.Positive` |
| `hg₂pos` | `0 < X.1.val g₂` |
| `ha` | `(Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1` |
| `hXY` | `X.1 < Y.1` |
| `hcommon` | no gene appears in both X and Y |
| `hsigeq` | ∀ k ≥ 1 with `prime^[k] Y.1.val ≠ 0`, `Sigma.sigma X.1 k ≠ Sigma.sigma Y.1 k` |
| `hXpn` | X has no Positive-Negative pair at the same rank |

Write `m := g₁.rank` and `k := g₂.rank`.

---

## Shared setup (before odd/even split)

### Step 1 — m ≤ k

```lean
have hle : g₁.rank ≤ g₂.rank :=
  hg₁min g₂ (Finsupp.mem_support_iff.mpr hg₂pos.ne')
```

### Step 2 — Gene → Chromosome conversion

```lean
have hg₁chr : Gene.ofRankAlt m .Negative = Finsupp.single g₁ 1 := by
  rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
  congr 1; exact Gene.ext rfl hε₁.symm

have hg₂chr : Gene.ofRankAlt k .Positive = Finsupp.single g₂ 1 := by
  rw [Gene.ofRankAlt_eq_gene g₂.rank_pos]
  congr 1; exact Gene.ext rfl hg₂type.symm
```

### Step 3 — g₁ ≠ g₂

When `m = k`, their types differ: `negOnePow(m-1) • .Negative ≠ negOnePow(m-1) • .Positive`
(one is Positive iff the other is Negative by the negOnePow sign flip).
When `m < k`, ranks differ.

```lean
have hne : g₁ ≠ g₂ := by
  intro heq
  have htype := congr_arg Gene.type heq
  rw [hε₁, hg₂type] at htype
  -- negOnePow(m-1) • .Negative = negOnePow(m-1) • .Positive is impossible
  cases GeneType.negOnePow_smul (g₁.rank - 1 : ℤ) GeneType.Negative <;>
  cases GeneType.negOnePow_smul (g₁.rank - 1 : ℤ) GeneType.Positive <;>
  simp_all [GeneType.neg_positive, GeneType.neg_negative]
```

### Step 4 — Construct the type-3 primitive mutation pair (X3 → Y3)

The paper's Case 1 uses the type-3 mutation with `ε = Negative`, ranks `m` and `k`:
```
X3 = Gene.ofRankAlt m .Negative + Gene.ofRankAlt k .Positive
   ↓  Pi.Primitive.type3
Y3 = Gene.ofRankAlt (m−1) .Positive + Gene.ofRankAlt (k+1) .Negative
```

```lean
let X3 : Pi := Pi.X3 (hε := by decide) hle g₁.rank_pos
let Y3 : Pi := Pi.Y3 (hε := by decide) hle g₁.rank_pos
-- X3.val = Gene.ofRankAlt m .Negative + Gene.ofRankAlt k .Positive  (Pi.X3_eq)
-- Y3.val = Gene.ofRankAlt (m−1) .Positive + Gene.ofRankAlt (k+1) .Negative  (Pi.Y3_eq)
have hX3_val : X3.val = Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
  rw [Pi.X3_eq, hg₁chr, hg₂chr]
```

### Step 5 — Decompose X into X3 + rest

```lean
let rest : Chromosome := X.1.val - Finsupp.single g₁ 1 - Finsupp.single g₂ 1
have hrest_Pi : rest ∈ Pi := by
  rw [mem_Pi_iff, IsPolarized_def']
  intro g hg
  apply IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g
  rw [Finsupp.mem_support_iff] at hg ⊢
  intro hX0; apply hg
  simp only [rest, Finsupp.tsub_apply, Finsupp.single_apply, hX0]; omega
let rest_pi : Pi := ⟨rest, hrest_Pi⟩
-- X3.val + rest = X.1.val  (analogous to X_eq_X1_add_rest)
have hX_eq : X3.val + rest = X.1.val := by
  rw [hX3_val]
  ext g'
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases h1 : g₁ = g'
  · subst h1; simp [if_neg hne]; omega
  · by_cases h2 : g₂ = g'
    · subst h2; simp [if_neg hne.symm]; omega
    · simp [if_neg h1, if_neg h2]
```

### Step 6 — Construct Z and produce the mutation step

```lean
have hprim : Pi.Primitive X3 Y3 :=
  Pi.Primitive.type3 GeneType.Negative (by decide) hle g₁.rank_pos
let Z : Pi := ⟨Y3.val + rest, add_mem Y3.2 hrest_Pi⟩
have hstep_raw : Pi.Step (X3 + rest_pi) (Y3 + rest_pi) :=
  Pi.Step.mk X3 Y3 rest_pi hprim
have hX_sub : X3 + rest_pi = X.1 := Subtype.ext hX_eq
refine ⟨Z, hX_sub ▸ hstep_raw, ?_⟩
```

### Step 7 — Verify Z ≤ Y: sigma dominance

**Goal:** `Z ≤ Y`, i.e. for every level `j ≥ 0`, `σ(Z, j) ≤ σ(Y, j)`.

Since `Z = Y3 + rest` and `X = X3 + rest`, the goal unfolds to showing

```
σ(Y3, j) + σ(rest, j)  ≤  σ(Y, j)  for all j.
```

Two standing facts are set up once:

- **Decomposition:** `σ(X, j) = σ(X3, j) + σ(rest, j)` (because X = X3 + rest).
- **Dominance:** `σ(X, j) ≤ σ(Y, j)` for all j (from the hypothesis X < Y).

```lean
have hdecomp : ∀ j, Sigma.sigma X3.val j + Sigma.sigma rest j = Sigma.sigma X.1.val j := by
  intro j; rw [← Sigma.sigma_add, hX_eq]
have hdom : ∀ j, Sigma.sigma X.1.val j ≤ Sigma.sigma Y.1.val j :=
  Pi.le_iff_sigma_le.mp (le_of_lt hXY)
```

The proof then splits on the parity of `k = g₂.rank`:

```lean
rcases Nat.even_or_odd g₂.rank with ⟨r, hr⟩ | ⟨r, hr⟩
```

---

#### Branch A — k even (`g₂.rank = 2 * r`)

```lean
· -- k = 2 * r
  sorry
```

---

#### Branch B — k odd (`g₂.rank = 2 * r + 1`)

Using the paper's notation `(cₙ, dₙ) := σ(Y, n)` (i.e. `c` = first component, `d` = second component of Y's sigma):

**Step 1 (`hcd`): `c_{k-1} - c_k ≤ d_{k-2} - d_{k-1}`.**
Since k is odd, k−2 is also odd. Condition 15.6 at level k−2 (odd branch) gives this directly.

**Step 2 (`hdc`): `d_{k-2} - d_{k-1} ≤ c_{k-3} - c_{k-2}`.**
Since k is odd, k−3 is even. Condition 15.6 at level k−3 (even branch) gives this. (Note: despite the earlier prompt, this is 15.6 not 15.7.)

**Step 3 (`htwo_step` + `hchain`): the full chain.**
Steps 1 and 2 exhibit a repeating pattern — at any even level 2n, `c_{2n} - c_{2n+1} ≤ c_{2n-2} - c_{2n-1}`. Inducting on j from r down to 0 gives the full chain `c_{k-1} - c_k ≤ d_{k-2} - d_{k-1} ≤ c_{k-3} - c_{k-2} ≤ … ≤ c_0 - c_1`.

**Consequence (`hkey`): `c_{k-1} - c_k ≤ c_0 - c_1`.**
Instantiate `hchain` at `j = r` and use `k = 2r+1` to match indices.

```lean
· -- k = 2 * r + 1
  have hkm2_odd : ¬Even (g₂.rank - 2) := by omega
  have hkm3_even : Even (g₂.rank - 3) := by omega
  -- c_{k-1} - c_k ≤ d_{k-2} - d_{k-1}
  -- uses cond_15_6 at level k-2 (odd branch, since k-2 = 2r-1 is odd)
  have hcd : (Sigma.sigma Y.1.val (g₂.rank - 1)).1 - (Sigma.sigma Y.1.val g₂.rank).1 ≤
             (Sigma.sigma Y.1.val (g₂.rank - 2)).2 - (Sigma.sigma Y.1.val (g₂.rank - 1)).2 := by
    have h := Sigma.cond_15_6 (X := Y.1.val) (k := g₂.rank - 2) Y.1.2
    simp only [if_neg hkm2_odd] at h
    convert h using 2 <;> omega
  -- d_{k-2} - d_{k-1} ≤ c_{k-3} - c_{k-2}
  -- NOTE: this uses cond_15_6 at level k-3 (even branch, since k-3 = 2r-2 is even),
  -- not cond_15_7 — please verify which is intended
  have hdc : (Sigma.sigma Y.1.val (g₂.rank - 2)).2 - (Sigma.sigma Y.1.val (g₂.rank - 1)).2 ≤
             (Sigma.sigma Y.1.val (g₂.rank - 3)).1 - (Sigma.sigma Y.1.val (g₂.rank - 2)).1 := by
    have h := Sigma.cond_15_6 (X := Y.1.val) (k := g₂.rank - 3) Y.1.2
    simp only [if_pos hkm3_even] at h
    convert h using 2 <;> omega
  -- Full chain: c_{k-1} - c_k ≤ d_{k-2} - d_{k-1} ≤ c_{k-3} - c_{k-2} ≤ ... ≤ c_0 - c_1
  -- Strategy: package the two-step drop c_{2n} - c_{2n+1} ≤ c_{2n-2} - c_{2n-1},
  -- then induct on r (since k = 2r+1 → c_{k-1} - c_k = c_{2r} - c_{2r+1}).
  have htwo_step : ∀ n : ℕ, 1 ≤ n →
      (Sigma.sigma Y.1.val (2*n)).1 - (Sigma.sigma Y.1.val (2*n+1)).1 ≤
      (Sigma.sigma Y.1.val (2*n-2)).1 - (Sigma.sigma Y.1.val (2*n-1)).1 := by
    intro n hn
    have h1 : (Sigma.sigma Y.1.val (2*n)).1 - (Sigma.sigma Y.1.val (2*n+1)).1 ≤
              (Sigma.sigma Y.1.val (2*n-1)).2 - (Sigma.sigma Y.1.val (2*n)).2 := by
      have h := Sigma.cond_15_6 (X := Y.1.val) (k := 2*n-1) Y.1.2
      simp only [if_neg (by omega : ¬Even (2*n-1))] at h
      convert h using 2 <;> omega
    have h2 : (Sigma.sigma Y.1.val (2*n-1)).2 - (Sigma.sigma Y.1.val (2*n)).2 ≤
              (Sigma.sigma Y.1.val (2*n-2)).1 - (Sigma.sigma Y.1.val (2*n-1)).1 := by
      have h := Sigma.cond_15_6 (X := Y.1.val) (k := 2*n-2) Y.1.2
      simp only [if_pos (by omega : Even (2*n-2))] at h
      convert h using 2 <;> omega
    exact h1.trans h2
  have hchain : ∀ j ≤ r,
      (Sigma.sigma Y.1.val (2*j)).1 - (Sigma.sigma Y.1.val (2*j+1)).1 ≤
      (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
    intro j hj
    induction j with
    | zero => le_refl _
    | succ n ih => exact (htwo_step (n+1) (by omega)).trans (ih (by omega))
  -- Consequence: c_{k-1} - c_k ≤ c_0 - c_1
  have hkey : (Sigma.sigma Y.1.val (g₂.rank - 1)).1 - (Sigma.sigma Y.1.val g₂.rank).1 ≤
              (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
    have := hchain r le_rfl
    simp only [hr]; convert this using 2 <;> omega
```

**Step 5 (`hc0c1_lt`): `c_0 - c_1 < a_0 - a_1`.**

Here `a_j` denotes `σ(Z, j).1` (first component of Z's sigma). The hypothesis `ha₀_eq_c₀` (proved for X and Y via `sigma_zero_fst_eq`) gives `σ(X, 0).1 = σ(Y, 0).1`; to use it for Z we need `σ(Z, 0).1 = σ(X, 0).1` (flagged as TODO). Similarly `ha : σ(X, 1).1 < σ(Y, 1).1` requires `σ(Z, 1).1 = σ(X, 1).1`. Assuming those, `c_0 - c_1 = a_0 - c_1 < a_0 - a_1`.

```lean
  -- NOTE: ha and ha₀_eq_c₀ are about X; for Z ≤ Y need σ(Z,0).1 = σ(X,0).1 and σ(Z,1).1 = σ(X,1).1
  have hc0c1_lt : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                  (Sigma.sigma Z.1 0).1 - (Sigma.sigma Z.1 1).1 := by
    linarith [ha, ha₀_eq_c₀]  -- TODO: adapt ha and ha₀_eq_c₀ to Z once σ(Z,j) = σ(X,j) is established
```

**Step 6: Equality chain from equal endpoints.**

Here `a_j = σ(Z, j).1` and `b_j = σ(Z, j).2`. `cond_15_6` (applied to Z, which is a valid Pi element) gives the non-increasing chain `a_0 - a_1 ≥ b_1 - b_2 ≥ a_2 - a_3 ≥ … ≥ a_{k-1} - a_k`. The endpoints are equal because k is minimal among alt-Positive genes in Z (flagged: g₂ ∉ Z after the mutation, so the minimality argument needs to identify the minimal alt-Positive gene of Z). With equal endpoints, every term is squeezed to `a_0 - a_1`.

```lean
  -- NOTE: uses Z's sigma throughout (goal is Z ≤ Y); cond_15_6 holds for Z since Z is a Pi element
  let chain : ℕ → ℚ := fun j =>
    if Even j then (Sigma.sigma Z.1 j).1 - (Sigma.sigma Z.1 (j+1)).1
              else (Sigma.sigma Z.1 j).2 - (Sigma.sigma Z.1 (j+1)).2
  -- One step: cond_15_6 at level j gives chain (j+1) ≤ chain j
  have hZ_one_step : ∀ j, j + 1 < g₂.rank → chain (j + 1) ≤ chain j := by
    intro j hj
    have h := Sigma.cond_15_6 (X := Z.1) (k := j) Z.1.2
    rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
    · simp only [chain, if_pos (show Even j from ⟨m, hm⟩),
                 if_neg (show ¬Even (j+1) by omega),
                 if_pos (show Even j from ⟨m, hm⟩)] at h ⊢; linarith
    · simp only [chain, if_neg (show ¬Even j by omega),
                 if_pos (show Even (j+1) from ⟨m+1, by omega⟩),
                 if_neg (show ¬Even j by omega)] at h ⊢; linarith
  -- Full chain monotone: j₁ ≤ j₂ → chain j₂ ≤ chain j₁
  have hZ_chain_mono : ∀ j₁ j₂, j₂ < g₂.rank → j₁ ≤ j₂ → chain j₂ ≤ chain j₁ := by
    intro j₁ j₂ hj₂ hle
    induction hle with
    | refl => le_refl _
    | @step p _ ih => exact (hZ_one_step p (by omega)).trans (ih (by omega))
  -- Equal endpoints for Z's chain.
  -- NOTE: g₂ ∉ Z (the mutation removed it from X3 to form Z = Y3 + rest); check which
  -- alt-Positive gene is minimal in Z and whether the minimality argument still gives rank k.
  have hend_eq : chain 0 = chain (g₂.rank - 1) := sorry
  -- All terms equal σ(Z,0).1 - σ(Z,1).1
  have hZ_chain_even : ∀ n, 2 * n < g₂.rank →
      (Sigma.sigma Z.1 (2*n)).1 - (Sigma.sigma Z.1 (2*n+1)).1 =
      (Sigma.sigma Z.1 0).1 - (Sigma.sigma Z.1 1).1 := by
    intro n hn
    have hle := hZ_chain_mono 0 (2*n) hn (Nat.zero_le _)
    have hge := hZ_chain_mono (2*n) (g₂.rank - 1) (by omega) (by omega)
    simp only [chain, if_pos (show Even (2*n) from ⟨n, rfl⟩),
               if_pos (show Even 0 from ⟨0, rfl⟩),
               if_pos (show Even (g₂.rank - 1) from by rw [hr]; omega)] at hle hge hend_eq
    linarith
  have hZ_chain_odd : ∀ n, 2 * n + 1 < g₂.rank →
      (Sigma.sigma Z.1 (2*n+1)).2 - (Sigma.sigma Z.1 (2*n+2)).2 =
      (Sigma.sigma Z.1 0).1 - (Sigma.sigma Z.1 1).1 := by
    intro n hn
    have hle := hZ_chain_mono 0 (2*n+1) hn (Nat.zero_le _)
    have hge := hZ_chain_mono (2*n+1) (g₂.rank - 1) (by omega) (by omega)
    simp only [chain, if_neg (show ¬Even (2*n+1) by omega),
               if_pos (show Even 0 from ⟨0, rfl⟩),
               if_pos (show Even (g₂.rank - 1) from by rw [hr]; omega)] at hle hge hend_eq
    linarith
  sorry
```

**Step 7: Combine into the full chain.**

The Y chain gives `c_{k-1} - c_k ≤ c_0 - c_1` (from `hkey`). The level-0 comparison gives `c_0 - c_1 < a_0 - a_1` where `a_j = σ(Z, j).1` (from `hc0c1_lt`). The Z equality chain gives `a_0 - a_1 = a_{k-1} - a_k` (from `hZ_chain_even` at `n = r`). Chaining these three gives `c_{k-1} - c_k < a_{k-1} - a_k`.

```lean
  have hlt : (Sigma.sigma Y.1.val (g₂.rank - 1)).1 - (Sigma.sigma Y.1.val g₂.rank).1 <
             (Sigma.sigma Z.1 (g₂.rank - 1)).1 - (Sigma.sigma Z.1 g₂.rank).1 := by
    have hZ_end := hZ_chain_even r (by omega : 2 * r < g₂.rank)
    simp only [hr] at hZ_end
    linarith [hkey, hc0c1_lt]
  sorry
```

**Step 8: `a_k < c_k`.**

Here `a_j = σ(Z, j).1`. Rearranging `hlt` gives `a_k - c_k < a_{k-1} - c_{k-1}`. `hdom (k-1)` gives `σ(X, k-1).1 ≤ σ(Y, k-1).1`; we use this as a proxy for `a_{k-1} ≤ c_{k-1}`, which requires `σ(Z, k-1).1 = σ(X, k-1).1` (flagged). So `a_k < c_k`.

```lean
  -- NOTE: hdom gives σ(X, k-1) ≤ σ(Y, k-1); using it here requires σ(Z, k-1) = σ(X, k-1)
  have hak_lt_ck : (Sigma.sigma Z.1 g₂.rank).1 < (Sigma.sigma Y.1.val g₂.rank).1 := by
    have h_le := (Prod.le_def.mp (hdom (g₂.rank - 1))).1
    linarith [hlt]
  sorry
```

**Step 9: `b_{k-1} < d_{k-1}`.**

Here `b_j = σ(Z, j).2`. From `hdc` and `hchain (r-1)`, the Y odd term `d_{k-2} - d_{k-1}` is bounded above by `c_0 - c_1`. From `hZ_chain_odd (r-1)`, the Z odd term `b_{k-2} - b_{k-1} = a_0 - a_1`. Since `c_0 - c_1 < a_0 - a_1`, we get `d_{k-2} - d_{k-1} < b_{k-2} - b_{k-1}`. Then `hdom (k-2)` gives `σ(X, k-2).2 ≤ σ(Y, k-2).2`, used as a proxy for `b_{k-2} ≤ d_{k-2}` (requires `σ(Z, k-2).2 = σ(X, k-2).2`, flagged). The same rearrangement as Step 8 gives `b_{k-1} < d_{k-1}`.

```lean
  have hlt2 : (Sigma.sigma Y.1.val (g₂.rank - 2)).2 - (Sigma.sigma Y.1.val (g₂.rank - 1)).2 <
              (Sigma.sigma Z.1 (g₂.rank - 2)).2 - (Sigma.sigma Z.1 (g₂.rank - 1)).2 := by
    have hY_le : (Sigma.sigma Y.1.val (g₂.rank - 2)).2 - (Sigma.sigma Y.1.val (g₂.rank - 1)).2 ≤
                 (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 :=
      le_trans hdc (hchain (r-1) (by omega))
    have hZ_eq := hZ_chain_odd (r-1) (by omega : 2*(r-1)+1 < g₂.rank)
    linarith [hc0c1_lt]
  -- NOTE: hdom gives σ(X, k-2) ≤ σ(Y, k-2); requires σ(Z, k-2) = σ(X, k-2)
  have hbk_lt_dk : (Sigma.sigma Z.1 (g₂.rank - 1)).2 < (Sigma.sigma Y.1.val (g₂.rank - 1)).2 := by
    have h_le := (Prod.le_def.mp (hdom (g₂.rank - 2))).2
    linarith [hlt2]
  sorry
```

