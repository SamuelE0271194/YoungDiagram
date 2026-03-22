# Plan: Sub-case 2a (line 283 of Theorem_6_Claude.lean)

## Goal

```
∃ Z : Variety.Pi, IsMutation X.val Z.val ∧ Z ≤ Y
```

## Available Hypotheses

| Name | Type |
|------|------|
| `m` | `ℕ` (so `n = m + 2`) |
| `ih` | Strong IH: `∀ r < m+2, ∀ A B : Pi, A ∈ Pi_n r → B ∈ Pi_n r → A < B → ∃ Z, IsMutation A.val Z.val ∧ Z ≤ B` |
| `hX`, `hY` | `X ∈ Pi_n (m+2)`, `Y ∈ Pi_n (m+2)` |
| `hXY` | `X < Y` in `Variety.Pi` |
| `hcommon` | `∀ g, 0 < X.val g → Y.val g ≤ 0` (disjoint supports, after `push_neg`) |
| `k` | `ℕ` |
| `hkpos` | `0 < k` |
| `hYkne` | `Chromosome.prime^[k] Y.val ≠ 0` |
| `hk` | `Sigma.sigma X k = Sigma.sigma Y k` (i.e. `signature (prime^[k] X.val) = signature (prime^[k] Y.val)`) |
| `hle_k` | `Chromosome.prime^[k] X.val ≤ Chromosome.prime^[k] Y.val` |
| `hdisj_k` | `∀ g', 0 < (prime^[k] X.val) g' → (prime^[k] Y.val) g' = 0` |
| `prime_iterate_coeff` | `∀ k' D h, (prime^[k'] D) h = D ⟨h.rank + k', h.type, _⟩` (proved locally) |
| `Xk` | `Variety.Pi := ⟨prime^[k] X.val, prime_mem_Pi_iterate X.2⟩` |
| `Yk` | `Variety.Pi := ⟨prime^[k] Y.val, prime_mem_Pi_iterate Y.2⟩` |

---

## Step 1 — `hXk_Yk_rank : Xk.val.rank = Yk.val.rank`

**From:** `hk : signature (prime^[k] X.val) = signature (prime^[k] Y.val)`

**How:**
```lean
have hXk_Yk_rank : Xk.val.rank = Yk.val.rank := by
  have := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) hk
  simp only [signature_sum_eq_rank] at this
  exact_mod_cast this
```

---

## Step 2 — `hXk_rank_lt : Xk.val.rank < m + 2`

**Idea:** Each application of `prime` to a nonzero chromosome reduces the rank by at least 1. Since `k > 0` and `prime^[k] Y.val ≠ 0`, we have `rank (prime^[k] Y.val) ≤ rank Y.val - k < rank Y.val = m + 2`. Since `rank Xk = rank Yk` (Step 1), done.

**Requires:** A lemma of the form:
```
rank_prime_lt : ∀ C : Chromosome, C ≠ 0 → rank (prime C) < rank C
```
or the iterated version. Check `SigmaAux.lean` for `max_rank_prime_minus1` or `sig_prime_le_sig`.

**Proof sketch:**
```lean
have hXk_rank_lt : Xk.val.rank < m + 2 := by
  rw [hXk_Yk_rank]
  -- rank (prime^[k] Y.val) < rank Y.val = m + 2
  -- by induction on k using prime_rank_lt and hYkne
  sorry
```

---

## Step 3 — `hlt_k : Xk < Yk`

Unfold to `Yk.val.Dominates Xk.val ∧ ¬Xk.val.Dominates Yk.val`.

### Component 1: `Yk.val.Dominates Xk.val`

Direct from `hle_k` via `le_iff_dominates`.

### Component 2: `¬Xk.val.Dominates Yk.val`

**Proof by contradiction:** Assume `hcontra : Xk.val.Dominates Yk.val`.
- Then `Xk ≤ Yk` (from `hle_k`) and `Yk ≤ Xk` (from `hcontra`).
- By **antisymmetry of the Pi preorder**: `Xk = Yk`.
- Since `hYkne : Yk.val ≠ 0`, there exists `g'` with `Yk.val g' > 0`.
- `Xk = Yk` implies `Xk.val g' > 0`.
- `hdisj_k g' (Xk.val g' > 0)` gives `Yk.val g' = 0`. Contradiction.

**Requires:** Pi preorder antisymmetry:
```
Pi_le_antisymm : X ≤ Y → Y ≤ X → X = Y
```
This follows from: equal signatures at all iterated-prime levels determine the chromosome uniquely. May need to be added as a lemma.

**Proof sketch:**
```lean
have hlt_k : Xk < Yk := by
  change Yk.val.Dominates Xk.val ∧ ¬Xk.val.Dominates Yk.val
  refine ⟨le_iff_dominates.mp hle_k, fun hcontra => ?_⟩
  have hXkYk_eq : Xk = Yk := le_antisymm hle_k (le_iff_dominates.mpr hcontra)
  obtain ⟨g', hg'⟩ : ∃ g', 0 < Yk.val g' := Finsupp.ne_iff_exists_pos.mp hYkne
  exact absurd (hdisj_k g' (hXkYk_eq ▸ hg')) (Nat.not_eq_zero_of_lt hg')
```

---

## Step 4 — Apply the Strong IH

```lean
obtain ⟨U, hU_mut, hU_le⟩ : ∃ U : Variety.Pi, IsMutation Xk.val U.val ∧ U ≤ Yk :=
  ih Xk.val.rank hXk_rank_lt Xk Yk rfl hXk_Yk_rank.symm hlt_k
```

Gives `U : Variety.Pi` with `IsMutation (prime^[k] X.val) U.val` and `U ≤ Yk`.

---

## Step 5 — Apply the Lifting Lemma

**Convert `IsMutation` to `Pi.Step`** (sorry: IH gives `IsMutation` but `mutation_lifting` needs `Pi.Step`; resolving requires restating the theorem conclusion with `Pi.Step`):
```lean
have hU_step : Variety.Pi.Step Xk U := by sorry
```

**Call `mutation_lifting`** to lift the step from `prime^[k] X` to `X`:
```lean
obtain ⟨Z, hZ, hZ_step, hZ_prime, hZ_sig⟩ :=
  mutation_lifting (0 : Fin 5) k X.2
    ((congrArg (U.val ∈ ·) (congrArg Label (@Label.prime_iterate_zero k))).mpr U.2)
    (by sorry)  -- type coercion: Step (Label.prime^[k] 0) ... from Pi.Step Xk U
                -- cannot be bridged without mutation_lifting_Pi being public
```

This gives:
- `hZ_step : Pi.Step ⟨X.val, X.2⟩ ⟨Z, hZ⟩`
- `hZ_prime : prime^[k] Z = U.val`
- `hZ_sig : ∀ i ≤ k, signature (prime^[i] X.val) = signature (prime^[i] Z)`

Then `Pi.Step.isMutation hZ_step : IsMutation X.val Z`.

---

## Step 6 — Prove `⟨Z, hZ⟩ ≤ Y`

```lean
refine ⟨⟨Z, hZ⟩, Pi.Step.isMutation hZ_step, ?_⟩
change Z ≤ Y.val
rw [le_iff_dominates]
intro j
by_cases hjk : j ≤ k
· -- j ≤ k: use signature equality from lifting, then X ≤ Y
  calc signature (prime^[j] Z)
      = signature (prime^[j] X.val) := (hZ_sig j hjk).symm
    _ ≤ signature (prime^[j] Y.val) := le_iff_dominates.mp hXY.le j
· -- j > k: prime^[j] Z = prime^[j-k] U.val, then use U ≤ Yk
  push_neg at hjk
  calc signature (prime^[j] Z)
      = signature (prime^[j - k] U.val) := by
          conv_lhs =>
            rw [show j = (j - k) + k from (Nat.sub_add_cancel hjk.le).symm,
                Function.iterate_add_apply, hZ_prime]
    _ ≤ signature (prime^[j - k] Yk.val) := le_iff_dominates.mp hU_le (j - k)
    _ = signature (prime^[j] Y.val) := by
          simp only [Yk]
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjk.le]
```

---

## Summary of Remaining Sorrys

| Step | Sorry | Resolution |
|------|-------|------------|
| Step 2 | `hXk_rank_lt` | Prove `rank (prime^[k] C) < rank C` for `C ≠ 0`, `k > 0`. Check `SigmaAux.lean` for `max_rank_prime_minus1`. |
| Step 3 | Antisymmetry of Pi order | Prove or find `le_antisymm` for `Variety.Pi`. Follows from: equal signature towers determine the chromosome. |
| Step 5a | `IsMutation → Pi.Step` | Restate theorem conclusion with `Pi.Step` instead of `IsMutation` so IH produces a `Pi.Step`. |
| Step 5b | `hMu` type coercion | `Label.prime^[k] 0 = 0` is propositional not definitional; `mutation_lifting` API cannot be called cleanly without `mutation_lifting_Pi` being public. |
