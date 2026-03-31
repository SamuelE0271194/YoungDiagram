# Detailed Plan: Case 1 of Sub-case 2b (15.10), `a_k < c_k` branch

**File**: [Theorem_6_Claude.lean](YoungDiagram/Theorem_6_Claude.lean), line 801.

## Setting

We are at the `sorry` after `obtain ⟨k, hkpos, hYkne, hak⟩ := ha`, inside:
- Sub-case 2b (`hsigeq` active): for every `j ≥ 1` with `prime^[j] Y ≠ 0`, `σ X j ≠ σ Y j`.
- (15.10) branch (`hXpn` negated, renamed): X has **no** same-rank pos-neg pair.
- `ha` branch: there exists `k ≥ 1` with `prime^[k] Y ≠ 0` and `a_k < c_k`.

**Case 1 hypothesis** (to be assumed at the top of this case branch):
```
∃ gpos gneg : Gene,
    gpos.type = .Positive ∧ gneg.type = .Negative ∧
    gpos.rank < gneg.rank ∧ gpos.rank ≤ k ∧
    0 < X.val gpos ∧ 0 < X.val gneg
```
Extracted as `gpos, gneg, hgpos, hgneg, hrlt, hrlek, hXgpos, hXgneg`.

Set `r := gpos.rank` (so `r ≤ k`, `r ≥ 1` from `gpos.rank_pos`) and `s := gneg.rank`
(so `s > r`). X1 = g⁺(r) + g⁻(s), Y1 = g⁻(r−1) + g⁺(s+1).

**Goal**: `∃ Z : Variety.Pi, Pi.Step X Z ∧ Z ≤ Y`.

---

## Overview

Construct `Z := Y1 + rest` where `restval := X.val − single gpos 1 − single gneg 1`.
Show `Pi.Step X Z` and `Z ≤ Y`. The proof of `Z ≤ Y` splits into four level ranges:

| Range | Sig change | Argument |
|-------|-----------|----------|
| `j < r` | `sig(Y1^j) = sig(X1^j)` | `mutation_type1_iterate_signature_eq` |
| `r ≤ j ≤ s` | `sig(Y1^j) = sig(X1^j) + (1,0)` | uses `hak` at `j = k`; uses conditions 15.4–15.7 elsewhere |
| `j > s` | both vanish | both zero, use `X ≤ Y` |

---

## Step 1 — Deduce gene properties

```lean
have hr    : 1 ≤ r  := gpos.rank_pos
have hrlt  : r < s  := hrlt  -- s > r
have hrles : r ≤ s  := Nat.le_of_lt hrlt
have hrlek : r ≤ k  := hrlek
have hspos : 1 ≤ s  := Nat.one_le_iff_ne_zero.mpr (by omega)
```

From `hXpn`: `X` has no pair `(gpos, gneg)` with the **same** rank, so `gpos.rank ≠ gneg.rank`,
i.e. `r ≠ s`. Combined with `r ≤ s`: `r < s`. ✓ (already in `hrlt`).

```lean
have hgpos_eq : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) :=
  Gene.ofRank_eq_gene (g := gpos) -- after rewriting gpos.type
have hgneg_eq : Gene.ofRank s .Negative = (Finsupp.single gneg 1 : Chromosome) :=
  Gene.ofRank_eq_gene (g := gneg) -- after rewriting gneg.type and gneg.rank = s
have hne : gpos ≠ gneg := fun h => absurd (congrArg Gene.type h) (by rw [hgpos, hgneg]; decide)
```

---

## Step 2 — Construct the gene pair and rest

```lean
let ε : GeneType := .Positive
have hε : ε ≠ .NonPolarized := by decide
```

```lean
let restval := X.val - Finsupp.single gpos 1 - Finsupp.single gneg 1
```

**`rest_mem : restval ∈ Pi`**: same argument as lines 590–598 of the existing code.
Support of `restval` ⊆ support of `X.val`, which is polarized. Use `mem_Pi_iff` +
`IsPolarized_def'`.

**`hX_eq : X1.val + restval = X.val`**: same `Finsupp.ext` argument as lines 600–614.
Each of `gpos` and `gneg` appears with multiplicity ≥ 1 in `X.val` (`hXgpos`, `hXgneg`),
and `gpos ≠ gneg` (`hne`), so the equation holds pointwise.

---

## Step 3 — Define X1, Y1, Z and construct `Pi.Step X Z`

```lean
let X1 : Pi := Pi.X1 hε hrles hr     -- g⁺(r) + g⁻(s)
let Y1 : Pi := Pi.Y1 hε hrles hr     -- g⁻(r−1) + g⁺(s+1)
let rest_pi : Pi := ⟨restval, rest_mem⟩
```

```lean
have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
  rw [Pi.X1_eq, GeneType.neg_positive, hgpos_eq, hgneg_eq]
```

```lean
have hX_eq : X1.val + restval = X.val := by rw [hX1_val]; exact hX_eq_of _ _ rfl rfl
```

```lean
let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
have hprim : Pi.Primitive X1 Y1 := Pi.Primitive.type1 ε hε hrles hr
have hstep_raw : Pi.Step (X1 + rest_pi) (Y1 + rest_pi) := Pi.Step.mk X1 Y1 rest_pi hprim
have hX_sub : X1 + rest_pi = X := Subtype.ext hX_eq
refine ⟨Z, hX_sub ▸ hstep_raw, ?_⟩
```

---

## Step 4 — Prove `Z ≤ Y`

```lean
change Y1.val + restval ≤ Y.val
rw [le_iff_dominates]
intro j
rw [iterate_map_add, map_add]
have hdecomp : signature (Chromosome.prime^[j] X.val) =
    signature (Chromosome.prime^[j] X1.val) +
    signature (Chromosome.prime^[j] restval) := by
  rw [← hX_eq, iterate_map_add, map_add]
have hXYj : signature (Chromosome.prime^[j] X.val) ≤ signature (Chromosome.prime^[j] Y.val) :=
  le_iff_dominates.mp hXY.le j
```

Case split:

```lean
rcases lt_or_le j r with hjr | hjr
· -- Case j < r
  ...
· rcases lt_or_le j s with hjs | hjs
  · -- Case r ≤ j ≤ s (j < s from hjs, but need to split j = s too)
    rcases lt_or_eq_of_le hjs with hjlts | rfl
    · -- Sub-case r ≤ j < s
      ...
    · -- Sub-case j = s
      ...
  · -- Case j > s
    ...
```

### Sub-case j < r

**Key lemma**:
```lean
mutation_type1_iterate_signature_eq hε (by omega : 1 ≤ s - r) le_rfl j (r - 1) (by omega : j ≤ r - 1)
```

This has the form (with `m = 1`, `n = s - r`, `k = r - 1`):
```
sig(prime^[j](g⁺(1 + (r−1)) + g⁻((s−r) + (r−1)))) =
sig(prime^[j](g⁻((r−1)) + g⁺((s−r) + (r−1) + 1)))
```
which simplifies (using `1 + (r−1) = r`, `(s−r) + (r−1) = s−1`, `s−1+1 = s`) to:
```
sig(prime^[j](g⁺(r) + g⁻(s))) = sig(prime^[j](g⁻(r−1) + g⁺(s+1)))
```

After unfolding `X1` and `Y1` via `Pi.X1_eq`, `Pi.Y1_eq`:
```lean
have hY1X1_j : signature (Chromosome.prime^[j] Y1.val) =
    signature (Chromosome.prime^[j] X1.val) := by
  rw [Pi.Y1_eq, Pi.X1_eq, hgpos_eq.symm, hgneg_eq.symm]
  exact (mutation_type1_iterate_signature_eq hε (by omega) le_rfl j (r - 1) (by omega)).symm
```

Then:
```lean
rw [hY1X1_j, ← hdecomp]; exact hXYj
```

### Sub-case r ≤ j ≤ s (the critical intermediate range)

**Computed signatures**:

```lean
have hX1j : signature (Chromosome.prime^[j] X1.val) = signature (Gene.ofRank (s - j) .Negative) := by
  rw [Pi.X1_eq, iterate_map_add, map_add, prime_iterate_ofRank, prime_iterate_ofRank]
  simp only [show r - j = 0 from by omega, Gene.ofRank_zero, map_zero, zero_add]
  -- gene of rank (s - j) .Negative remains (s ≥ j since j ≤ s)
```

```lean
have hY1j : signature (Chromosome.prime^[j] Y1.val) =
    signature (Gene.ofRank (s + 1 - j) .Positive) := by
  rw [Pi.Y1_eq, iterate_map_add, map_add, prime_iterate_ofRank, prime_iterate_ofRank]
  simp only [show r - 1 - j = 0 from by omega, Gene.ofRank_zero, map_zero, zero_add]
  -- gene of rank (s + 1 - j) .Positive remains (s + 1 > j since j ≤ s → s + 1 > j)
```

Note that for `j = s`:
- `g⁻(s − s) = g⁻(0) = 0`, so `hX1j` gives 0.
- `g⁺(s + 1 − s) = g⁺(1)`.

**Key numerical identity** (gain = (1, 0)):

For any `t : ℕ` with `t ≥ 0`:
```lean
have hgain : signature (Gene.ofRank (t + 1) .Positive) =
    signature (Gene.ofRank t .Negative) + (1, 0) := by
  simp only [signature_ofRank_eq, signature_ofRank_neg_eq]  -- or unfold via sig_ofRank_pos/neg
  -- ⌈(t+1)/2⌉ = ⌊t/2⌋ + 1  and  ⌊(t+1)/2⌋ = ⌈t/2⌉
  -- These follow from the floor/ceil lemmas in Mathlib.
```

Setting `t = s - j` (with `j ≤ s`): `sig(g⁺(s+1−j)) = sig(g⁻(s−j)) + (1, 0)`.

Therefore `sig(Y1^(j)) = sig(X1^(j)) + (1, 0)`.

**The critical inequality**: need `sig(X^(j)) + (1, 0) ≤ sig(Y^(j))`, i.e.
```
a_j + 1 ≤ c_j    (Prod.fst component)
b_j     ≤ d_j    (Prod.snd component)
```

The second follows from `hXYj.2`. For the first: **`a_j < c_j`**.

**How `a_j < c_j` is established**:

This is the key difficulty. We know `a_k < c_k` from `hak`. For the other levels
`j ∈ [r, s]` with `j ≠ k`, the argument uses conditions 15.4–15.7.

**Sub-case `j = k`** (in the range `[r, s]` since `r ≤ k ≤ s`, to be shown):

```lean
-- hak : (Sigma.sigma X k).1 < (Sigma.sigma Y k).1
-- i.e., a_k < c_k
obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.2 (k := j))
obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.2 (k := j))
-- Use: a_k < c_k → (nX.1 : ℚ) < nY.1 → nX.1 + 1 ≤ nY.1 (Nat)
-- Then a_k + 1 ≤ c_k via Nat.add_one_le_iff.mpr + Nat.cast_le
```

**Sub-case `j ∈ [r, s]` with `j < k`** (if `r < k`):

```lean
-- Need a_j < c_j for r ≤ j < k.
-- Argument: use cond_15_6 and cond_15_7 (inequality chains on sigma differences).
```

Conditions 15.6/15.7 (available from `Sigma.lean`):
```lean
Sigma.cond_15_6 (hX : X ∈ Variety.Pi) :
  if Even k then b X (k+1) - b X (k+2) ≤ a X k - a X (k+1)
            else a X (k+1) - a X (k+2) ≤ b X k - b X (k+1)
Sigma.cond_15_7 (hX : X ∈ Variety.Pi) :
  if Even k then a X (k+1) - a X (k+2) ≤ b X k - b X (k+1)
            else b X (k+1) - b X (k+2) ≤ a X k - a X (k+1)
```

Applied simultaneously to X and Y with the excess `(c_j - a_j)`, these provide chains of
inequalities relating `(c_j - a_j)` at adjacent indices. In particular, if `a_k < c_k`, then
the alternating differences propagate to give `a_j < c_j` (or `b_j < d_j`) at levels j ≤ k.

**The precise chain** (this is the core computation from the paper):

Let `Δa_j := c_j - a_j` and `Δb_j := d_j - b_j`. From `X ≤ Y`: `Δa_j ≥ 0`, `Δb_j ≥ 0`.

From conditions 15.6 for X and Y:
- `b X (j+1) - b X (j+2) ≤ a X j - a X (j+1)` (if j even)
- `c Y (j+1) - c Y (j+2) ≤ ??? ` — actually 15.6 says `b Y(j+1) - b Y(j+2) ≤ a Y j - a Y(j+1)`.

Taking the DIFFERENCE (Y minus X):
```
(d_{j+1} - b_{j+1}) - (d_{j+2} - b_{j+2}) ≥ (c_j - a_j) - (c_{j+1} - a_{j+1})
Δb_{j+1} - Δb_{j+2} ≥ Δa_j - Δa_{j+1}   (j even)
```

This gives a recurrence on the excesses `Δa` and `Δb`. Combined with `hsigeq`
(`Δa_j + Δb_j > 0` for all `j ≥ 1` with `prime^[j] Y ≠ 0`) and `Δa_k ≥ 1` (from `hak`):

The precise propagation to show `Δa_j ≥ 1` for all `j ≤ k` (resp. even `j`) follows from
the alternating inequality chain:
```
Δa_k ≥ 1 → Δb_{k-1} ≥ 1 (from cond_15_7) → Δa_{k-2} ≥ 1 (from cond_15_6) → …
```
depending on the parity of k. The details of this propagation are specified in the paper's
"Case 1" (which assumes k is odd or even with ε₁ specific).

**Lemma to prove inline** (critical helper):

```lean
have ha_chain : ∀ j ∈ Finset.Icc r s, (Sigma.sigma X j).1 < (Sigma.sigma Y j).1 := by
  intro j hj
  -- Use hak, hsigeq, cond_15_6 (X.2), cond_15_6 (Y.2), cond_15_7 (X.2), cond_15_7 (Y.2),
  -- and the antitone conditions (cond_15_2, cond_15_3) to propagate Δa_k ≥ 1 down to j.
  sorry -- key sub-goal from paper's Case 1 chain
```

With `ha_chain`, the critical inequality at `j ∈ [r, s]` follows immediately:
```lean
have haj_lt : (Sigma.sigma X j).1 < (Sigma.sigma Y j).1 := ha_chain j (by simp; omega)
```

**Proof of `Z ≤ Y` at this level**:

```lean
rw [hY1j, hgain (s - j), hX1j, ← hdecomp, hXYj]
-- Goal: sig(X^j) + sig(X1^j) − sig(X1^j) + (1,0) ≤ sig(Y^j)
-- = sig(X^j) + (1,0) ≤ sig(Y^j)
obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.2 (k := j))
obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.2 (k := j))
constructor
· -- a_j + 1 ≤ c_j
  simp only [Prod.fst_add, show (1 : ℚ×ℚ).1 = 1 from rfl]
  rw [hnX, hnY] at haj_lt ⊢
  exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp haj_lt)
· -- b_j ≤ d_j (from hXYj.2, since second component of (1,0) is 0)
  simp only [Prod.snd_add, show (1 : ℚ×ℚ).2 = 0 from rfl, add_zero]
  exact hXYj.2
```

### Sub-case `j > s`

```lean
have hX1j_zero : signature (Chromosome.prime^[j] X1.val) = 0 := by
  rw [Pi.X1_eq, iterate_map_add, map_add, prime_iterate_ofRank, prime_iterate_ofRank]
  simp only [show r - j = 0 from by omega, show s - j = 0 from by omega,
             Gene.ofRank_zero, map_zero, add_zero]
have hY1j_zero : signature (Chromosome.prime^[j] Y1.val) = 0 := by
  rw [Pi.Y1_eq, iterate_map_add, map_add, prime_iterate_ofRank, prime_iterate_ofRank]
  simp only [show r - 1 - j = 0 from by omega, show s + 1 - j = 0 from by omega,
             Gene.ofRank_zero, map_zero, add_zero]
have hrestj : signature (Chromosome.prime^[j] restval) =
    signature (Chromosome.prime^[j] X.val) := by rw [hdecomp, hX1j_zero, zero_add]
rw [hY1j_zero, zero_add, hrestj]; exact hXYj
```

---

## Step 5 — The `ha_chain` lemma (key sub-goal)

This is the main new proof obligation not present in the existing code (lines 616–791).

### What is needed

```lean
ha_chain : ∀ j ∈ Finset.Icc r s,
    (Sigma.sigma X j).1 < (Sigma.sigma Y j).1
```

where `r ≤ k ≤ s`.

### Available tools

| Lemma | Statement | Use |
|-------|-----------|-----|
| `Sigma.cond_15_6 X.2` | Alternating-difference inequality for X's sigma | Propagate `Δa` down from k |
| `Sigma.cond_15_6 Y.2` | Same for Y | Propagate `Δa` down from k |
| `Sigma.cond_15_7 X.2` | Other alternating-difference inequality | Propagate `Δa` down from k |
| `Sigma.cond_15_7 Y.2` | Same for Y | |
| `Sigma.cond_15_2`, `cond_15_3` | Antitone: `a_{j+1} ≤ a_j`, `b_{j+1} ≤ b_j` | Bound excesses from above |
| `Sigma.cond_15_4`, `cond_15_5` | Interleaving: if k even, `b_{k+1} ≤ a_k` etc. | |
| `hsigeq` | `σ X j ≠ σ Y j` for all `j ≥ 1` with `prime^[j] Y ≠ 0` | Ensures excess > 0 |
| `hak` | `a_k < c_k` | Base of chain |
| `hXY.le` | `X ≤ Y`: `a_j ≤ c_j`, `b_j ≤ d_j` for all j | Bounds throughout |
| `hYkne` | `prime^[k] Y ≠ 0` | Needed for hsigeq at k |

### Strategy

**Step 5a**: Show `prime^[j] Y ≠ 0` for all `j ∈ [r, s]`.

Since `X.val gneg > 0` (from `hXgneg`) and `gneg.rank = s`, we have:
```lean
have hgneg_in_X : 0 < X.val gneg := hXgneg
-- prime^[j](single gneg 1) ≠ 0 for j ≤ s (since gneg has rank s > j)
-- X.val ≥ single gneg 1 pointwise, so prime^[j] X ≠ 0 for j ≤ s
-- X ≤ Y implies prime^[j] Y ≠ 0 for j ≤ s (nonneg sig ≤ sig Y → sig Y ≥ 0 and nonzero)
```

More precisely: `(prime^[j] X)(gene(s-j, .Negative)) = X.val gneg > 0`, so `prime^[j] X ≠ 0`,
and hence `sig(prime^[j] X).2 > 0`. From X ≤ Y: `sig(prime^[j] Y).2 ≥ sig(prime^[j] X).2 > 0`,
so `prime^[j] Y ≠ 0`.

**Step 5b**: From Step 5a and `hsigeq`: for every `j ∈ [r, s]` (and `j ≥ 1` since `r ≥ 1`),
`(a_j, b_j) ≠ (c_j, d_j)`. Together with `(a_j, b_j) ≤ (c_j, d_j)`:
either `a_j < c_j` or `b_j < d_j`.

**Step 5c**: Propagation from `j = k` to all `j ∈ [r, s]` using conditions 15.6/15.7.

The conditions 15.6/15.7, applied to **both** X and Y and then differenced, give inequalities
on `Δa_j := c_j - a_j` and `Δb_j := d_j - b_j`. For example, from `cond_15_6`:

For **j even**:
```
b_X(j+1) - b_X(j+2) ≤ a_X(j) - a_X(j+1)         (from X)
b_Y(j+1) - b_Y(j+2) ≤ a_Y(j) - a_Y(j+1)         (from Y)
Subtracting: Δb(j+1) - Δb(j+2) ≥ Δa(j) - Δa(j+1)
```

For **j odd** (using `cond_15_7`):
```
a_X(j+1) - a_X(j+2) ≤ b_X(j) - b_X(j+1)
a_Y(j+1) - a_Y(j+2) ≤ b_Y(j) - b_Y(j+1)
Subtracting: Δa(j+1) - Δa(j+2) ≥ Δb(j) - Δb(j+1)
```

Starting from `Δa_k ≥ 1` (i.e., `a_k < c_k`), and using `Δa_j + Δb_j ≥ 1` (from Step 5b), the
alternating recurrence propagates the strict inequality:
- If k is even: `Δa_k ≥ 1` → (from cond_15_7 applied backwards) `Δb_{k-1} ≥ 1` → `Δa_{k-2} ≥ 1` → …
- If k is odd: `Δa_k ≥ 1` → `Δa_{k-1} ≥ ?` via the recurrence.

**Note**: The exact form of this chain (and which parity gives `Δa_j ≥ 1` at all j ∈ [r, s]) is
what the paper's "Case 1" specifies precisely. The condition "k odd" (resp. "ε₁ = −") in
Djoković's Case 1 likely ensures that the interleaving goes the right way so that `Δa_j ≥ 1`
holds (rather than `Δb_j ≥ 1`) for all j ∈ [r, s].

### Lean proof skeleton for `ha_chain`

```lean
have ha_chain : ∀ j, r ≤ j → j ≤ s → (Sigma.sigma X j).1 < (Sigma.sigma Y j).1 := by
  -- Step 5a: prime^[j] Y ≠ 0 for j ∈ [r, s]
  have hYj_ne : ∀ j ≤ s, Chromosome.prime^[j] Y.val ≠ 0 := by
    intro j hjs
    have : 0 < (Chromosome.prime^[j] X.val) ⟨s - j, .Negative, by omega⟩ := by
      simp only [Chromosome.prime, ...]
      -- (prime^[j] X)(gene(s-j, -)) = X(gneg) > 0
      exact_mod_cast hXgneg
    intro hzero
    have hle := le_iff_dominates.mp hXY.le j
    simp [hzero, map_zero] at hle
    -- sig(prime^[j] X) ≤ (0,0) but sig.2 > 0: contradiction
    linarith [signature_nonneg (Chromosome.prime^[j] X.val)]
  -- Step 5b: for j ≥ 1 in [r, s]: σ X j ≠ σ Y j
  have hsigeq_j : ∀ j, r ≤ j → j ≤ s → (Sigma.sigma X j) ≠ (Sigma.sigma Y j) := by
    intro j hrj hjs
    exact hsigeq j (by omega : 0 < j) (hYj_ne j hjs)
  -- Step 5c: propagation using cond_15_6/15_7
  intro j hrj hjs
  -- By induction from k downwards, or by direct use of excess chain
  -- ... (key proof body)
  -- Base: j = k: hak
  -- Step: given Δa_{j+1} ≥ 1 (or Δb_{j+1} ≥ 1), derive Δa_j ≥ 1 using 15.6/15.7 + hsigeq_j
  sorry  -- sub-goal: propagation chain from Djoković §15 Case 1
```

---

## Step 6 — Summary of the required `hgain` sub-lemma

```lean
lemma signature_ofRank_pos_eq_neg_plus_one (t : ℕ) :
    signature (Gene.ofRank (t + 1) .Positive : Chromosome) =
    signature (Gene.ofRank t .Negative : Chromosome) + (1, 0) := by
  cases t with
  | zero =>
    simp [Gene.ofRank_zero, signature_ofRank_one_positive]
  | succ t =>
    rw [signature_ofRank_eq, signature_ofRank_eq] -- using signature_ofRank_eq or ofRank_pos/neg
    -- ⌈(t+2)/2⌉ = ⌊(t+1)/2⌋ + 1  and  ⌊(t+2)/2⌋ = ⌈(t+1)/2⌉
    simp [Nat.ceil_div_two, Nat.floor_div_two, Prod.ext_iff]
    omega
```

This may already follow from existing lemmas (`signature_ofRank_one_positive`,
`signature_ofRank_one_negative`, `signature_ofRank_eq`, `signature_ofRank_eq₂`); check first.

---

## Summary of new proof obligations vs existing code

| Obligation | Status | Note |
|------------|--------|------|
| `rest_mem` | Identical to existing code lines 590–598 | Copy verbatim |
| `hX_eq` | Identical to existing code lines 600–614 | Copy verbatim |
| `Pi.Step X Z` | Identical structure to lines 632–637 | Same with `r < s` instead of `r = r` |
| `Z ≤ Y`, j < r | Same as existing sub-case "j < r" | Adjust lemma parameters: `m=1, n=s-r, k'=r-1` |
| `Z ≤ Y`, j > s | Same as existing sub-case "j > r" | Straightforward |
| `Z ≤ Y`, j ∈ [r, s], j = k | Same pattern as existing `j = r` case | Use `hak` for `.1` component |
| `Z ≤ Y`, j ∈ [r, s], j ≠ k | **NEW** | Requires `ha_chain` + propagation from §15 |
| `ha_chain` propagation | **NEW** | Core argument from Djoković §15 Case 1 |
| `hgain` identity | **Possibly new** | `sig(g⁺(t+1)) = sig(g⁻(t)) + (1,0)` |
| Show `r ≤ k ≤ s` | **NEW** | Need gpos.rank ≤ k (from Case 1 hyp.) and s ≥ k |

**Note on `s ≥ k`**: The Case 1 hypothesis has `gpos.rank ≤ k` but does not directly state
`gneg.rank ≥ k`. If `gneg.rank < k`, then the intermediate range [r, s] lies entirely below k,
and `hak` is only used implicitly (level k is outside [r, s]). In that case, the proof of
`Z ≤ Y` at levels `j ∈ [r, s]` (all < k) uses conditions 15.6/15.7 applied backwards from k.

For the sub-case `s < k`, we still need `a_j < c_j` for j ∈ [r, s], but now k > s so hak
is not directly used. The argument would use the chain from k downward to level s, then to r.
Djoković's proof handles this via the same chain but starting from k and going down.

---

## Open questions

1. **Is `k ≤ s` guaranteed?** If Case 1 is specifically for gpos.rank ≤ k with gneg.rank > k
   (both chosen relative to k), then yes. The Lean case split would explicitly require
   `gneg.rank ≥ k` in the hypothesis of Case 1.

2. **Parity of k**: Djoković's "Case 1: ε₁ = −, k odd" might impose `k` is odd, in which case
   the chain from `Δa_k ≥ 1` goes: `Δa_k ≥ 1` → `Δb_{k-1} ≥ 1` → `Δa_{k-2} ≥ 1` → …
   This would use `cond_15_7` (odd levels) and `cond_15_6` (even levels) alternately.

3. **When `prime^[j] Y = 0` for some j ∈ [r, s]**: If this happens, `c_j = d_j = 0`, but from
   X ≤ Y we also have `a_j = b_j = 0`. Then `sig(X1^(j)) = 0` (no contribution from gneg since
   gneg.rank = s and prime^[j] g⁻(s) = g⁻(s-j) ≠ 0 for j < s — contradiction). So in fact
   prime^[j] Y ≠ 0 for all j ≤ s (shown in Step 5a).
