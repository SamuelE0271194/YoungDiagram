import YoungDiagram.Sigma_Claude

open Chromosome Variety

/-!
# Pi Chromosome Antisymmetry

The dominance preorder on Pi chromosomes is antisymmetric:
`A ≤ B → B ≤ A → A = B` for `A B : Chromosome` with `A, B ∈ Variety.Pi`.

This is used in Theorem_6_Claude.lean (line 363) to close the contradiction
in step 3 of sub-case 2a.

## Proof outline

From `A ≤ B` and `B ≤ A`, `sig(prime^[j] A) = sig(prime^[j] B)` for all `j`
(Step A). The sigma-tower determines a Pi chromosome uniquely via two routes:

**Sum route (Steps B–D):** from rank equality at all levels + telescoping, the
total gene count `A ⟨r, Pos⟩ + A ⟨r, Neg⟩` equals `B ⟨r, Pos⟩ + B ⟨r, Neg⟩`
at every rank `r`.

**Difference route (Steps E–F):** from `sig.1 − sig.2` at each level (only
odd-rank genes contribute), telescoping `D(j) − D(j+2)` recovers
`A ⟨r, Pos⟩ − A ⟨r, Neg⟩ = B ⟨r, Pos⟩ − B ⟨r, Neg⟩` at every rank `r`.

**Conclude (Step G):** adding and subtracting gives individual equality, then
`Finsupp.ext` closes the goal. NonPolarized genes are 0 in Pi by `IsPolarized_def'`.
-/

-- ============================================================
-- Auxiliary lemma 1: prime^[k] coefficient formula
-- ============================================================

/-- The coefficient of gene `g` in `prime^[k] C` equals `C` at the gene
of rank `g.rank + k` and the same type. -/
lemma prime_iterate_coeff' (k : ℕ) (C : Chromosome) (g : Gene) :
    (Chromosome.prime^[k] C) g = C ⟨g.rank + k, g.type, by linarith [g.rank_pos]⟩ := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id, Nat.add_zero]
  | succ k' ih =>
    rw [Function.iterate_succ_apply']
    simp only [Chromosome.prime, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Finsupp.sum_apply]
    -- prime(prime^[k'] C) g  =  ∑_{h} (prime^[k'] C) h • (primeGene h) g
    -- Only the gene h with primeGene h = g contributes, i.e. h = ⟨g.rank + 1, g.type, _⟩.
    -- Then (prime^[k'] C) h = C ⟨g.rank + 1 + k', g.type, _⟩  by the IH.
    sorry

-- ============================================================
-- Auxiliary lemma 2: rank decomposition under prime
-- ============================================================

/-- The rank of a chromosome decreases by the total gene count under `prime`. -/
lemma rank_prime_decomp' (C : Chromosome) :
    C.rank = (Chromosome.prime C).rank + C.sum (fun _ m => m) := by
  -- Proved as `hdecomp` inside prime_rank_lt in Theorem_6_Claude.lean.
  -- Proof: rank C = C.sum (g m => m * g.rank)
  --        rank (prime C) = C.sum (g m => m * (g.rank - 1))
  --        difference = C.sum (g m => m * (g.rank - (g.rank - 1))) = C.sum (g m => m)
  sorry

-- ============================================================
-- Auxiliary lemma 3: total count of prime^[j] C via rank-shift bijection
-- ============================================================

/-- The total gene count (sum of multiplicities) of `prime^[j] C` equals
the sum of multiplicities of `C` restricted to genes of rank `> j`.

Key: the map `g ↦ ⟨g.rank + j, g.type, _⟩` is a bijection from
`supp(prime^[j] C)` to `{h ∈ supp(C) | h.rank > j}`, by `prime_iterate_coeff'`. -/
lemma prime_iterate_total_count (j : ℕ) (C : Chromosome) :
    (Chromosome.prime^[j] C).sum (fun _ m => m) =
    C.sum (fun g m => if j < g.rank then m else 0) := by
  -- Proof strategy: `Finsupp.sum` reindexing via `Finset.sum_nbij`.
  -- The bijection: from g ∈ supp(prime^[j] C), map to ⟨g.rank + j, g.type, _⟩ ∈ supp(C).
  -- Injectivity: g.rank + j = h.rank + j → g.rank = h.rank, and same type.
  -- Surjectivity: h ∈ supp(C) with h.rank > j → preimage ⟨h.rank - j, h.type, _⟩.
  -- Value: (prime^[j] C) g = C ⟨g.rank + j, g.type, _⟩ by prime_iterate_coeff'.
  -- Proof sketch: use Finset.sum_nbij' with
  --   forward:  h ↦ ⟨h.rank + j, h.type, _⟩   ((prime^[j] C).support → filtered C.support)
  --   backward: g ↦ ⟨g.rank - j, g.type, _⟩   (filtered C.support → (prime^[j] C).support)
  -- after first rewriting RHS via Finset.sum_filter to restrict to {g | j < g.rank}.
  -- Value equality uses prime_iterate_coeff'.
  sorry

-- ============================================================
-- Step D: Total gene count agrees at each rank
-- ============================================================

/-- From sigma-tower equality, the total gene count at each rank `r` agrees:
`A ⟨r, Pos⟩ + A ⟨r, Neg⟩ = B ⟨r, Pos⟩ + B ⟨r, Neg⟩`. -/
lemma pi_sum_per_rank {A B : Chromosome}
    (hA : A ∈ Variety.Pi) (hB : B ∈ Variety.Pi)
    (hsig_eq : ∀ j, signature (Chromosome.prime^[j] A) =
                    signature (Chromosome.prime^[j] B))
    (r : ℕ) (hr : 0 < r) :
    A ⟨r, .Positive, hr⟩ + A ⟨r, .Negative, hr⟩ =
    B ⟨r, .Positive, hr⟩ + B ⟨r, .Negative, hr⟩ := by
  -- Step B: rank equality at every level j.
  have hrank_eq : ∀ j, (Chromosome.prime^[j] A).rank =
                        (Chromosome.prime^[j] B).rank := fun j => by
    have h := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) (hsig_eq j)
    simp only [signature_sum_eq_rank] at h
    exact_mod_cast h
  -- From rank_prime_decomp': rank(prime^[j] C) - rank(prime^[j+1] C) = total_count(prime^[j] C).
  -- From hrank_eq: total_count(prime^[j] A) = total_count(prime^[j] B) for all j.
  -- From prime_iterate_total_count: total_count(prime^[j] C) = C.sum (g m => if j < g.rank then m else 0).
  -- Telescoping (j = r-1 minus j = r):
  --   A.sum (g m => if g.rank = r then m else 0) = B.sum (g m => if g.rank = r then m else 0).
  -- For Pi chromosomes (no NonPolarized): the sum equals A ⟨r, Pos⟩ + A ⟨r, Neg⟩.
  sorry

-- ============================================================
-- Step E: The D formula — sig.1 − sig.2 at level j
-- ============================================================

/-- For a Pi chromosome `C`, the difference `sig(prime^[j] C).1 − sig(prime^[j] C).2`
equals the sum of `C g` (with sign +1 for Positive, −1 for Negative) over genes
`g` with `g.rank > j` and `(g.rank − j)` odd.

**Key fact:** `g.signature.1 − g.signature.2` equals `+1` (Positive, odd rank),
`−1` (Negative, odd rank), or `0` (even rank or NonPolarized). -/
lemma sig_diff_formula (j : ℕ) (C : Chromosome) (hC : C ∈ Variety.Pi) :
    (signature (Chromosome.prime^[j] C)).1 - (signature (Chromosome.prime^[j] C)).2 =
    C.sum (fun g m =>
      if j < g.rank ∧ (g.rank - j) % 2 = 1 then
        (m : ℚ) * (if g.type = .Positive then 1 else -1)
      else 0) := by
  -- Expand signature using signature_fst, signature_snd.
  -- Apply prime_iterate_coeff' to express (prime^[j] C) g = C ⟨g.rank + j, g.type, _⟩.
  -- The map g ↦ ⟨g.rank + j, g.type, _⟩ reindexes the sum (Finset.sum_nbij).
  -- Then g.signature.1 − g.signature.2 depends on g.rank (odd/even) and g.type.
  -- For Pi chromosomes: no NonPolarized genes, so the (−1) branch only hits Negative.
  sorry

-- ============================================================
-- Step F: Gene difference agrees at each rank by telescoping D(j) − D(j+2)
-- ============================================================

/-- From sigma-tower equality, the signed difference of gene counts at rank `r` agrees:
`A ⟨r, Pos⟩ − A ⟨r, Neg⟩ = B ⟨r, Pos⟩ − B ⟨r, Neg⟩` (in ℤ).

**Proof:** `D(j) − D(j+2)` telescopes to `C ⟨j+1, Pos⟩ − C ⟨j+1, Neg⟩`, since
terms with `g.rank > j+1` cancel between `D(j)` and `D(j+2)` (same parity class). -/
lemma pi_diff_per_rank {A B : Chromosome}
    (hA : A ∈ Variety.Pi) (hB : B ∈ Variety.Pi)
    (hsig_eq : ∀ j, signature (Chromosome.prime^[j] A) =
                    signature (Chromosome.prime^[j] B))
    (r : ℕ) (hr : 0 < r) :
    (A ⟨r, .Positive, hr⟩ : ℤ) - A ⟨r, .Negative, hr⟩ =
    (B ⟨r, .Positive, hr⟩ : ℤ) - B ⟨r, .Negative, hr⟩ := by
  -- Define D(j) := sig(prime^[j] C).1 - sig(prime^[j] C).2 for C = A and C = B.
  -- From hsig_eq: D_A(j) = D_B(j) for all j.
  -- Apply sig_diff_formula to get the Finsupp.sum expression for D(j).
  -- Telescoping: D(r-1) - D(r+1) = A ⟨r, Pos⟩ - A ⟨r, Neg⟩ (and same for B).
  -- Hence equal.
  sorry

-- ============================================================
-- Main theorem: Pi chromosome antisymmetry
-- ============================================================

/-- The dominance preorder on Pi chromosomes is antisymmetric. -/
theorem pi_chromosome_antisymm {A B : Chromosome}
    (hA : A ∈ Variety.Pi) (hB : B ∈ Variety.Pi)
    (hAB : A ≤ B) (hBA : B ≤ A) : A = B := by
  -- Step A: sig-tower equality from the two opposite inequalities.
  have hsig_eq : ∀ j, signature (Chromosome.prime^[j] A) =
                       signature (Chromosome.prime^[j] B) := fun j =>
    le_antisymm (le_iff_dominates.mp hAB j) (hBA j)
  -- Step G: pointwise equality by Finsupp.ext.
  apply Finsupp.ext
  intro g
  -- Case split on gene type.
  rcases hgt : g.type with _ | _ | _
  · -- NonPolarized: both A and B assign 0 (Pi = IsPolarized).
    have hAnp : A g = 0 := by
      by_contra h
      exact absurd hgt (IsPolarized_def'.mp (mem_Pi_iff.mp hA) g
        (Finsupp.mem_support_iff.mpr h))
    have hBnp : B g = 0 := by
      by_contra h
      exact absurd hgt (IsPolarized_def'.mp (mem_Pi_iff.mp hB) g
        (Finsupp.mem_support_iff.mpr h))
    simp [hAnp, hBnp]
  · -- Positive gene at rank g.rank.
    -- Rewrite g as ⟨g.rank, Positive, g.rank_pos⟩ using g.type = Positive.
    have hgeq : g = ⟨g.rank, .Positive, g.rank_pos⟩ := by cases g; simp_all
    rw [hgeq]
    have hS := pi_sum_per_rank hA hB hsig_eq g.rank g.rank_pos
    have hD := pi_diff_per_rank hA hB hsig_eq g.rank g.rank_pos
    -- hS (ℕ): A ⟨r, Pos⟩ + A ⟨r, Neg⟩ = B ⟨r, Pos⟩ + B ⟨r, Neg⟩
    -- hD (ℤ): A ⟨r, Pos⟩ - A ⟨r, Neg⟩ = B ⟨r, Pos⟩ - B ⟨r, Neg⟩
    -- Adding in ℤ: 2 * A ⟨r, Pos⟩ = 2 * B ⟨r, Pos⟩ → A ⟨r, Pos⟩ = B ⟨r, Pos⟩.
    omega
  · -- Negative gene at rank g.rank.
    have hgeq : g = ⟨g.rank, .Negative, g.rank_pos⟩ := by cases g; simp_all
    rw [hgeq]
    have hS := pi_sum_per_rank hA hB hsig_eq g.rank g.rank_pos
    have hD := pi_diff_per_rank hA hB hsig_eq g.rank g.rank_pos
    -- Subtracting hD from hS in ℤ: 2 * A ⟨r, Neg⟩ = 2 * B ⟨r, Neg⟩.
    omega
