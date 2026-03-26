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

/-- One-step coefficient formula: `(prime C) g = C ⟨g.rank + 1, g.type, _⟩`. -/
private lemma prime_coeff_step (C : Chromosome) (g : Gene) :
    (Chromosome.prime C) g = C ⟨g.rank + 1, g.type, by linarith [g.rank_pos]⟩ := by
  simp only [Chromosome.prime, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
             Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul,
             Chromosome.primeGene]
  rw [Finsupp.sum_eq_single (⟨g.rank + 1, g.type, by linarith [g.rank_pos]⟩ : Gene)]
  · -- The unique contributing gene is ⟨g.rank + 1, ...⟩
    have hrank_sub : (⟨g.rank + 1, g.type,
          by linarith [g.rank_pos]⟩ : Gene).rank - 1 = g.rank := by simp only; omega
    simp [hrank_sub, Gene.ofRank_eq_gene, Finsupp.single_eq_same]
  · -- All other genes contribute 0
    intro h _ hne
    simp only [Gene.ofRank_def]
    split_ifs with hZ
    · simp [Finsupp.zero_apply]
    · rw [Finsupp.single_apply]
      split_ifs with heq
      · exfalso; apply hne
        have hr := congr_arg Gene.rank heq
        have ht := congr_arg Gene.type heq
        obtain ⟨rg, tg, hrg⟩ := h
        simp only at *
        simp only [Gene.mk.injEq]
        exact ⟨by omega, ht⟩
      · simp
  · intro _; simp

/-- The coefficient of gene `g` in `prime^[k] C` equals `C` at the gene
of rank `g.rank + k` and the same type. -/
lemma prime_iterate_coeff' (k : ℕ) (C : Chromosome) (g : Gene) :
    (Chromosome.prime^[k] C) g = C ⟨g.rank + k, g.type, by linarith [g.rank_pos]⟩ := by
  revert C g
  induction k with
  | zero =>
    intros C g
    simp only [Function.iterate_zero, id, Nat.add_zero]
  | succ k' ih =>
    -- ih : ∀ C g, (prime^[k'] C) g = C ⟨g.rank + k', ...⟩
    intros C g
    rw [Function.iterate_succ_apply, ih, prime_coeff_step]
    congr

-- ============================================================
-- Auxiliary lemma 2: rank decomposition under prime
-- ============================================================

/-- The rank of a chromosome decreases by the total gene count under `prime`. -/
lemma rank_prime_decomp' (C : Chromosome) :
    C.rank = (Chromosome.prime C).rank + C.sum (fun _ m => m) := by
  have rank_ofRank : ∀ (n : ℕ) (typ : GeneType),
      Chromosome.rank (Gene.ofRank n typ) = n := by
    intro n typ
    simp only [Gene.ofRank_def]
    split_ifs with h
    · simp [h]
    · simp [Chromosome.rank, Finsupp.sum_single_index]
  have hrank_prime :
      (Chromosome.prime C).rank = C.sum (fun g m => m * (g.rank - 1)) := by
    simp only [Chromosome.prime, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
               Finsupp.sum, map_sum Chromosome.rank, map_nsmul, smul_eq_mul,
               Chromosome.primeGene, rank_ofRank]
  have hrank_C : C.rank = C.sum (fun g m => m * g.rank) := by
    simp only [Chromosome.rank, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul]
  rw [hrank_C, hrank_prime]
  simp only [Finsupp.sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have hg : g.rank - 1 + 1 = g.rank := Nat.succ_pred_eq_of_pos g.rank_pos
  calc C g * g.rank
      = C g * (g.rank - 1 + 1) := by rw [hg]
    _ = C g * (g.rank - 1) + C g := by ring

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
  -- Unfold Finsupp.sum on both sides; convert RHS to a filter sum.
  simp only [Finsupp.sum, ← Finset.sum_filter]
  -- Bijection: forward g ↦ ⟨g.rank+j, g.type, _⟩, backward h ↦ ⟨max 1 (h.rank-j), h.type, _⟩.
  -- The max-1 trick makes the backward map a pure Gene→Gene without membership proof.
  apply Finset.sum_nbij'
    (fun g => (⟨g.rank + j, g.type, by linarith [g.rank_pos]⟩ : Gene))
    (fun h => (⟨max 1 (h.rank - j), h.type, Nat.le_max_left 1 _⟩ : Gene))
  · -- Forward: g ∈ supp(prime^[j] C) → ⟨g.rank+j, …⟩ ∈ C.support.filter (j < ·.rank)
    intro g hg
    rw [Finset.mem_filter, Finsupp.mem_support_iff] at *
    exact ⟨prime_iterate_coeff' j C g ▸ hg, by linarith [g.rank_pos]⟩
  · -- Backward: h ∈ filter → ⟨max 1 (h.rank-j), …⟩ ∈ supp(prime^[j] C)
    intro h hh
    rw [Finset.mem_filter, Finsupp.mem_support_iff] at hh
    obtain ⟨hC_ne, hjh⟩ := hh
    rw [Finsupp.mem_support_iff, prime_iterate_coeff']
    -- Simplify the gene rank: max 1 (h.rank-j) = h.rank-j, then (h.rank-j)+j = h.rank
    have hmax : max 1 (h.rank - j) = h.rank - j := Nat.max_eq_right (by omega)
    simp only [hmax, Nat.sub_add_cancel (Nat.le_of_lt hjh)]
    exact hC_ne
  · -- Left inverse: backward(forward(g)) = g for g ∈ supp(prime^[j] C)
    intro g _
    simp only [Nat.add_sub_cancel_right, Nat.max_eq_right g.rank_pos]
  · -- Right inverse: forward(backward(h)) = h for h ∈ filter
    intro h hh
    rw [Finset.mem_filter] at hh
    have hjh : j < h.rank := hh.2
    have hmax : max 1 (h.rank - j) = h.rank - j := Nat.max_eq_right (by omega)
    simp only [hmax, Nat.sub_add_cancel (Nat.le_of_lt hjh)]
  · -- Values agree: (prime^[j] C) g = C ⟨g.rank+j, g.type, _⟩
    intro g _
    exact prime_iterate_coeff' j C g

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
  -- Step C: total gene count equality at every level j.
  have hcount_eq : ∀ j, (Chromosome.prime^[j] A).sum (fun _ m => m) =
                         (Chromosome.prime^[j] B).sum (fun _ m => m) := fun j => by
    have hd_A := rank_prime_decomp' (Chromosome.prime^[j] A)
    have hd_B := rank_prime_decomp' (Chromosome.prime^[j] B)
    -- hd_A/hd_B: rank(prime^[j] C) = rank(prime (prime^[j] C)) + count(prime^[j] C)
    have hj := hrank_eq j
    have hj1 : (Chromosome.prime (Chromosome.prime^[j] A)).rank =
               (Chromosome.prime (Chromosome.prime^[j] B)).rank := by
      have := hrank_eq (j + 1)
      simp only [Function.iterate_succ_apply'] at this
      exact this
    linarith
  -- Step C': translate to rank-filtered sums.
  have hrank_sum_eq : ∀ j,
      A.sum (fun g m => if j < g.rank then m else 0) =
      B.sum (fun g m => if j < g.rank then m else 0) := fun j => by
    rw [← prime_iterate_total_count, ← prime_iterate_total_count]
    exact hcount_eq j
  -- Step D prep: telescoping identity.
  have hdecomp : ∀ (C : Chromosome),
      C.sum (fun g m => if r - 1 < g.rank then m else 0) =
      C.sum (fun g m => if r < g.rank then m else 0) +
      C.sum (fun g m => if g.rank = r then m else 0) := fun C => by
    simp only [Finsupp.sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> omega
  -- Step D main: telescope at j = r - 1 and j = r.
  have hsum_rank :
      A.sum (fun g m => if g.rank = r then m else 0) =
      B.sum (fun g m => if g.rank = r then m else 0) := by
    have h1 := hrank_sum_eq (r - 1)
    have h2 := hrank_sum_eq r
    have hA := hdecomp A
    have hB := hdecomp B
    omega
  -- Step D conclude: for Pi chromosomes, the rank-r sum splits into Pos + Neg.
  have hpi_sum : ∀ (C : Chromosome) (hC : C ∈ Variety.Pi),
      C.sum (fun g m => if g.rank = r then m else 0) =
      C ⟨r, .Positive, hr⟩ + C ⟨r, .Negative, hr⟩ := fun C hC => by
    have hIsPol := mem_Pi_iff.mp hC
    rw [Finsupp.sum, ← Finset.sum_filter]
    -- The filter contains only Pos and Neg genes (NonPolarized genes have C g = 0 in Pi).
    have hsubset : C.support.filter (fun g => g.rank = r) ⊆
        ({⟨r, .Positive, hr⟩, ⟨r, .Negative, hr⟩} : Finset Gene) := by
      intro g hg
      simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have htype := IsPolarized_def'.mp hIsPol g (Finsupp.mem_support_iff.mpr hg.1)
      rcases g with ⟨rg, tg, hrg⟩
      simp only at htype hg
      obtain ⟨_, rfl⟩ := hg
      rcases tg with _ | _ | _
      · exact absurd rfl htype
      · left; rfl
      · right; rfl
    have hne : (⟨r, .Positive, hr⟩ : Gene) ≠ ⟨r, .Negative, hr⟩ := by
      simp [Gene.mk.injEq]
    calc ∑ g ∈ C.support.filter (fun g => g.rank = r), C g
        = ∑ g ∈ ({⟨r, .Positive, hr⟩, ⟨r, .Negative, hr⟩} : Finset Gene), C g :=
          Finset.sum_subset hsubset (fun g hg hng => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hg
            simp only [Finset.mem_filter, not_and] at hng
            rcases hg with rfl | rfl
            · exact not_not.mp (Finsupp.mem_support_iff.not.mp fun hs => absurd rfl (hng hs))
            · exact not_not.mp (Finsupp.mem_support_iff.not.mp fun hs => absurd rfl (hng hs)))
      _ = C ⟨r, .Positive, hr⟩ + C ⟨r, .Negative, hr⟩ := Finset.sum_pair hne
  linarith [hpi_sum A hA, hpi_sum B hB, hsum_rank]

-- ============================================================
-- Step E: The D formula — sig.1 − sig.2 at level j
-- ============================================================

/-- For a polarized gene, `sig.1 - sig.2 = ±1` (odd rank) or `0` (even rank). -/
private lemma gene_sig_diff_eq {g : Gene} (hpol : g.type ≠ .NonPolarized) :
    g.signature.1 - g.signature.2 =
    if g.rank % 2 = 1 then (if g.type = .Positive then (1 : ℚ) else -1) else 0 := by
  match hg : g.type with
  | .NonPolarized => exact absurd hg hpol
  | .Positive =>
    rw [Gene.signature_of_positive hg]
    by_cases he : Even g.rank
    · simp only [if_pos he, sub_self]
      rw [if_neg (by have := Nat.even_iff.mp he; omega)]
    · have hmod : g.rank % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he)
      simp only [if_neg he]
      -- After simp, g.type = .Positive is already resolved: RHS has `if True then 1 else -1`
      rw [if_pos hmod, if_true]; ring
  | .Negative =>
    rw [Gene.signature_of_negative hg]
    by_cases he : Even g.rank
    · simp only [if_pos he, sub_self]
      rw [if_neg (by have := Nat.even_iff.mp he; omega)]
    · have hmod : g.rank % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he)
      simp only [if_neg he]
      -- After simp, g.type = .Negative is resolved: RHS has
        --`if GeneType.Negative = GeneType.Positive then ...`
      rw [if_pos hmod, if_neg (show GeneType.Negative ≠ GeneType.Positive from by decide)]
      ring

/-- For a Pi chromosome `C`, the difference `sig(prime^[j] C).1 − sig(prime^[j] C).2`
equals the sum of `C g` (with sign +1 for Positive, −1 for Negative) over genes
`g` with `g.rank > j` and `(g.rank − j)` odd. -/
lemma sig_diff_formula (j : ℕ) (C : Chromosome) (hC : C ∈ Variety.Pi) :
    (signature (Chromosome.prime^[j] C)).1 - (signature (Chromosome.prime^[j] C)).2 =
    C.sum (fun g m =>
      if j < g.rank ∧ (g.rank - j) % 2 = 1 then
        (m : ℚ) * (if g.type = .Positive then 1 else -1)
      else 0) := by
  have hIsPol := mem_Pi_iff.mp hC
  -- Step 1: Expand LHS to a single Finset.sum
  simp only [signature_fst, signature_snd, Finsupp.sum, smul_eq_mul,
             ← Finset.sum_sub_distrib, ← mul_sub]
  -- Now: ∑ g ∈ (prime^[j] C).support, (prime^[j] C) g * (g.sig.1 - g.sig.2) = RHS
  -- Step 2: Convert RHS to filter form for the bijection
  have hrhs : ∑ h ∈ C.support, (if j < h.rank ∧ (h.rank - j) % 2 = 1 then
        (C h : ℚ) * (if h.type = .Positive then 1 else -1) else 0) =
      ∑ h ∈ C.support.filter (fun h => j < h.rank), (C h : ℚ) *
        (if (h.rank - j) % 2 = 1 then (if h.type = .Positive then 1 else -1) else 0) := by
    conv_lhs => rw [← Finset.sum_filter]
    conv_rhs =>
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_filter]
    apply Finset.sum_congr rfl; intro a _; split_ifs <;> ring
  rw [hrhs]
  -- Step 3: Apply bijection g ↦ ⟨g.rank + j, g.type, _⟩ (same as prime_iterate_total_count)
  apply Finset.sum_nbij'
    (fun g => (⟨g.rank + j, g.type, by linarith [g.rank_pos]⟩ : Gene))
    (fun h => (⟨max 1 (h.rank - j), h.type, Nat.le_max_left 1 _⟩ : Gene))
  · -- Forward: g ∈ supp(prime^j C) → i(g) ∈ C.support.filter (j < ·.rank)
    intro g hg
    simp only [Finsupp.mem_support_iff] at hg
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨prime_iterate_coeff' j C g ▸ hg, by linarith [g.rank_pos]⟩
  · -- Backward: h ∈ filter → j(h) ∈ supp(prime^j C)
    intro h hh
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hh
    simp only [Finsupp.mem_support_iff, prime_iterate_coeff']
    have hmax : max 1 (h.rank - j) = h.rank - j := Nat.max_eq_right (by omega)
    simp only [hmax, Nat.sub_add_cancel (Nat.le_of_lt hh.2)]
    exact hh.1
  · -- Left inverse
    intro g _; simp only [Nat.add_sub_cancel_right, Nat.max_eq_right g.rank_pos]
  · -- Right inverse
    intro h hh
    simp only [Finset.mem_filter] at hh
    have hmax : max 1 (h.rank - j) = h.rank - j := Nat.max_eq_right (by omega)
    simp only [hmax, Nat.sub_add_cancel (Nat.le_of_lt hh.2)]
  · -- Values agree: (prime^j C) g * (g.sig.1 - g.sig.2) = C i(g) * (if g.rank%2=1 then ...)
    intro g hg
    simp only [Finsupp.mem_support_iff] at hg
    rw [prime_iterate_coeff']
    have hpol : g.type ≠ .NonPolarized :=
      IsPolarized_def'.mp (mem_Pi_iff.mp (prime_mem_Pi_iterate hC)) g
        (Finsupp.mem_support_iff.mpr hg)
    simp only [Nat.add_sub_cancel_right]
    congr 1
    exact gene_sig_diff_eq hpol

-- ============================================================
-- Step F: Gene difference agrees at each rank by telescoping D(j) − D(j+2)
-- ============================================================

/-- Telescoping: `D_C(j) − D_C(j+2) = C ⟨j+1, Pos⟩ − C ⟨j+1, Neg⟩` (in ℚ). -/
private lemma sig_diff_telesc (C : Chromosome) (hC : C ∈ Variety.Pi) (j : ℕ) :
    ((signature (Chromosome.prime^[j] C)).1 - (signature (Chromosome.prime^[j] C)).2) -
    ((signature (Chromosome.prime^[j + 2] C)).1 - (signature (Chromosome.prime^[j + 2] C)).2) =
    (C ⟨j + 1, .Positive, Nat.succ_pos j⟩ : ℚ) -
    C ⟨j + 1, .Negative, Nat.succ_pos j⟩ := by
  have hIsPol := mem_Pi_iff.mp hC
  rw [sig_diff_formula j C hC, sig_diff_formula (j + 2) C hC]
  simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
  -- Each summand telescopes to the rank-(j+1) indicator
  have hcongr : ∀ g ∈ C.support,
      (if j < g.rank ∧ (g.rank - j) % 2 = 1 then
          (C g : ℚ) * (if g.type = .Positive then 1 else -1) else 0) -
      (if j + 2 < g.rank ∧ (g.rank - (j + 2)) % 2 = 1 then
          (C g : ℚ) * (if g.type = .Positive then 1 else -1) else 0) =
      if g.rank = j + 1 then (C g : ℚ) * (if g.type = .Positive then 1 else -1) else 0 := by
    intro g _
    by_cases hc3 : g.rank = j + 1
    · -- g.rank = j+1: first cond true, second false
      have h1 : j < g.rank ∧ (g.rank - j) % 2 = 1 := ⟨by omega, by omega⟩
      have h2 : ¬(j + 2 < g.rank ∧ (g.rank - (j + 2)) % 2 = 1) := by rintro ⟨h, _⟩; omega
      rw [if_pos h1, if_neg h2, if_pos hc3]; ring
    · rw [if_neg hc3]
      rcases Nat.lt_or_ge g.rank (j + 2) with hlt | hge
      · -- g.rank ≤ j: both conditions false
        have h1 : ¬(j < g.rank ∧ (g.rank - j) % 2 = 1) := by rintro ⟨h, _⟩; omega
        have h2 : ¬(j + 2 < g.rank ∧ (g.rank - (j + 2)) % 2 = 1) := by rintro ⟨h, _⟩; omega
        rw [if_neg h1, if_neg h2, sub_self]
      · rcases Nat.eq_or_lt_of_le hge with heq | hlt2
        · -- g.rank = j+2: first cond fails (parity 0), second fails (not strict)
          have h1 : ¬(j < g.rank ∧ (g.rank - j) % 2 = 1) := by rintro ⟨_, h⟩; omega
          have h2 : ¬(j + 2 < g.rank ∧ (g.rank - (j + 2)) % 2 = 1) := by rintro ⟨h, _⟩; omega
          rw [if_neg h1, if_neg h2, sub_self]
        · -- g.rank > j+2: parity same, so both conditions match → difference 0
          have hparity : (g.rank - j) % 2 = (g.rank - (j + 2)) % 2 := by omega
          rcases Classical.em (j < g.rank ∧ (g.rank - j) % 2 = 1) with h1 | h1
          · have h2 : j + 2 < g.rank ∧ (g.rank - (j + 2)) % 2 = 1 :=
                ⟨by omega, by rw [← hparity]; exact h1.2⟩
            rw [if_pos h1, if_pos h2, sub_self]
          · have h2 : ¬(j + 2 < g.rank ∧ (g.rank - (j + 2)) % 2 = 1) := by
                rintro ⟨_, h⟩; exact h1 ⟨by omega, by rw [hparity]; exact h⟩
            rw [if_neg h1, if_neg h2, sub_self]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_filter]
  -- Evaluate the rank-(j+1) sum: only Pos and Neg genes contribute in Pi
  have hr' : 0 < j + 1 := Nat.succ_pos j
  have hne : (⟨j + 1, .Positive, hr'⟩ : Gene) ≠ ⟨j + 1, .Negative, hr'⟩ := by
    simp [Gene.mk.injEq]
  have hsubset : C.support.filter (fun g => g.rank = j + 1) ⊆
      ({⟨j + 1, .Positive, hr'⟩, ⟨j + 1, .Negative, hr'⟩} : Finset Gene) := by
    intro g hg
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have htype := IsPolarized_def'.mp hIsPol g (Finsupp.mem_support_iff.mpr hg.1)
    rcases g with ⟨rg, tg, hrg⟩; simp only at htype hg; obtain ⟨_, rfl⟩ := hg
    rcases tg with _ | _ | _
    · exact absurd rfl htype
    · left; rfl
    · right; rfl
  calc ∑ g ∈ C.support.filter (fun g => g.rank = j + 1),
          (C g : ℚ) * (if g.type = .Positive then 1 else -1)
      = ∑ g ∈ ({⟨j + 1, .Positive, hr'⟩, ⟨j + 1, .Negative, hr'⟩} : Finset Gene),
          (C g : ℚ) * (if g.type = .Positive then 1 else -1) :=
        Finset.sum_subset hsubset (fun g hg hng => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hg
          simp only [Finset.mem_filter, not_and] at hng
          rcases hg with rfl | rfl
          · simp [not_not.mp (Finsupp.mem_support_iff.not.mp fun hs => absurd rfl (hng hs))]
          · simp [not_not.mp (Finsupp.mem_support_iff.not.mp fun hs => absurd rfl (hng hs))])
    _ = (C ⟨j + 1, .Positive, hr'⟩ : ℚ) - C ⟨j + 1, .Negative, hr'⟩ := by
        rw [Finset.sum_pair hne]
        have hNP : GeneType.Negative ≠ GeneType.Positive := by decide
        simp only [if_true, if_neg hNP]
        ring

/-- From sigma-tower equality, the signed difference of gene counts at rank `r` agrees:
`A ⟨r, Pos⟩ − A ⟨r, Neg⟩ = B ⟨r, Pos⟩ − B ⟨r, Neg⟩` (in ℤ). -/
lemma pi_diff_per_rank {A B : Chromosome}
    (hA : A ∈ Variety.Pi) (hB : B ∈ Variety.Pi)
    (hsig_eq : ∀ j, signature (Chromosome.prime^[j] A) =
                    signature (Chromosome.prime^[j] B))
    (r : ℕ) (hr : 0 < r) :
    (A ⟨r, .Positive, hr⟩ : ℤ) - A ⟨r, .Negative, hr⟩ =
    (B ⟨r, .Positive, hr⟩ : ℤ) - B ⟨r, .Negative, hr⟩ := by
  -- D(j) equality from sig-tower equality
  have hDeq : ∀ j,
      (signature (Chromosome.prime^[j] A)).1 - (signature (Chromosome.prime^[j] A)).2 =
      (signature (Chromosome.prime^[j] B)).1 - (signature (Chromosome.prime^[j] B)).2 := fun j => by
    have h := hsig_eq j; simp only [Prod.ext_iff] at h; linarith [h.1, h.2]
  -- Telescope at j = r - 1: D(r-1) - D(r-1+2) = C⟨r-1+1, ...⟩ - C⟨r-1+1, ...⟩
  have hTA := sig_diff_telesc A hA (r - 1)
  have hTB := sig_diff_telesc B hB (r - 1)
  -- D(j) equalities at the two levels
  have hD1 := hDeq (r - 1)
  have hD2 := hDeq (r - 1 + 2)
  -- Convert Gene index: ⟨r-1+1, t, _⟩ = ⟨r, t, hr⟩ (since r-1+1 = r)
  have hrec : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
  have hgpos : (⟨r - 1 + 1, .Positive, Nat.succ_pos (r - 1)⟩ : Gene) = ⟨r, .Positive, hr⟩ := by
    simp [hrec]
  have hgneg : (⟨r - 1 + 1, .Negative, Nat.succ_pos (r - 1)⟩ : Gene) = ⟨r, .Negative, hr⟩ := by
    simp [hrec]
  rw [hgpos, hgneg] at hTA hTB
  -- Conclude in ℚ, then cast to ℤ
  have hQ : (A ⟨r, .Positive, hr⟩ : ℚ) - A ⟨r, .Negative, hr⟩ =
            (B ⟨r, .Positive, hr⟩ : ℚ) - B ⟨r, .Negative, hr⟩ := by linarith
  exact_mod_cast hQ

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

/-- For a polarized gene, the second signature component is a natural number (as a ℚ value). -/
lemma Gene.signature_snd_isNat {g : Gene} (hg : g.type ≠ .NonPolarized) :
    ∃ n : ℕ, g.signature.2 = ↑n := by
  rcases Nat.even_or_odd g.rank with ⟨m, hm⟩ | ⟨m, hm⟩
  · have heven : Even g.rank := ⟨m, hm⟩
    cases h : g.type with
    | NonPolarized => exact absurd h hg
    | Positive =>
      exact ⟨m, by rw [Gene.signature_of_positive h, if_pos heven]; push_cast [hm]; ring⟩
    | Negative =>
      exact ⟨m, by rw [Gene.signature_of_negative h, if_pos heven]; push_cast [hm]; ring⟩
  · have hodd : ¬Even g.rank := fun ⟨k, hk⟩ => by omega
    cases h : g.type with
    | NonPolarized => exact absurd h hg
    | Positive =>
      exact ⟨m, by rw [Gene.signature_of_positive h, if_neg hodd]; push_cast [hm]; ring⟩
    | Negative =>
      exact ⟨m + 1, by rw [Gene.signature_of_negative h, if_neg hodd]; push_cast [hm]; ring⟩

/-- For a Pi chromosome, the second signature component is a natural number (as a ℚ value). -/
lemma signature_pi_snd_isNat {C : Chromosome} (hC : C ∈ Variety.Pi) :
    ∃ n : ℕ, (signature C).2 = ↑n := by
  -- Define the ℕ-valued version of g.signature.2 for any gene
  let sig2nat : Gene → ℕ := fun g =>
    match g.type with
    | .Negative => if Odd g.rank then (g.rank + 1) / 2 else g.rank / 2
    | _ => g.rank / 2
  -- For polarized g, g.signature.2 = ↑(sig2nat g)
  have hpol_eq : ∀ g : Gene, g.type ≠ .NonPolarized → g.signature.2 = ↑(sig2nat g) := by
    intro g hg
    simp only [sig2nat]
    cases h : g.type with
    | NonPolarized => exact absurd h hg
    | Positive =>
      rcases Nat.even_or_odd g.rank with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hdiv : g.rank / 2 = m := by omega
        rw [Gene.signature_of_positive h, if_pos ⟨m, hm⟩, hdiv]; push_cast [hm]; ring
      · rw [Gene.signature_of_positive h,
            if_neg (show ¬Even g.rank from fun ⟨k, hk⟩ => by omega)]
        have hdiv : g.rank / 2 = m := by omega
        rw [hdiv]; push_cast [hm]; ring
    | Negative =>
      rcases Nat.even_or_odd g.rank with ⟨m, hm⟩ | ⟨m, hm⟩
      · have heven : Even g.rank := ⟨m, hm⟩
        have hdiv : g.rank / 2 = m := by omega
        rw [Gene.signature_of_negative h, if_pos heven,
            if_neg (show ¬Odd g.rank from fun ⟨k, hk⟩ => by omega), hdiv]
        push_cast [hm]; ring
      · have hodd : Odd g.rank := ⟨m, hm⟩
        have hdiv : (g.rank + 1) / 2 = m + 1 := by omega
        rw [Gene.signature_of_negative h, if_neg (show ¬Even g.rank from fun ⟨k, hk⟩ => by omega),
            if_pos hodd, hdiv]
        push_cast [hm]; ring
  -- Express (signature C).2 as ↑ of a ℕ sum
  refine ⟨C.sum (fun g n => n * sig2nat g), ?_⟩
  rw [signature_snd, Nat.cast_finsupp_sum]
  simp only [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro g hg
  have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp hC) g hg
  rw [hpol_eq g hpol, smul_eq_mul, ← Nat.cast_mul]

/-- For a Pi chromosome, the first signature component is a natural number (as a ℚ value). -/
lemma signature_pi_fst_isNat {C : Chromosome} (hC : C ∈ Variety.Pi) :
    ∃ n : ℕ, (signature C).1 = ↑n := by
  let sig1nat : Gene → ℕ := fun g =>
    match g.type with
    | .Positive => if Odd g.rank then (g.rank + 1) / 2 else g.rank / 2
    | _ => g.rank / 2
  have hpol_eq : ∀ g : Gene, g.type ≠ .NonPolarized → g.signature.1 = ↑(sig1nat g) := by
    intro g hg
    simp only [sig1nat]
    cases h : g.type with
    | NonPolarized => exact absurd h hg
    | Positive =>
      rcases Nat.even_or_odd g.rank with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hdiv : g.rank / 2 = m := by omega
        rw [Gene.signature_of_positive h, if_pos ⟨m, hm⟩,
            if_neg (show ¬Odd g.rank from fun ⟨k, hk⟩ => by omega), hdiv]
        push_cast [hm]; ring
      · have hdiv : (g.rank + 1) / 2 = m + 1 := by omega
        rw [Gene.signature_of_positive h,
            if_neg (show ¬Even g.rank from fun ⟨k, hk⟩ => by omega),
            if_pos ⟨m, hm⟩, hdiv]
        push_cast [hm]; ring
    | Negative =>
      rcases Nat.even_or_odd g.rank with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hdiv : g.rank / 2 = m := by omega
        rw [Gene.signature_of_negative h, if_pos ⟨m, hm⟩, hdiv]
        push_cast [hm]; ring
      · have hdiv : g.rank / 2 = m := by omega
        rw [Gene.signature_of_negative h,
            if_neg (show ¬Even g.rank from fun ⟨k, hk⟩ => by omega), hdiv]
        push_cast [hm]; ring
  refine ⟨C.sum (fun g n => n * sig1nat g), ?_⟩
  rw [signature_fst, Nat.cast_finsupp_sum]
  simp only [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro g hg
  have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp hC) g hg
  rw [hpol_eq g hpol, smul_eq_mul, ← Nat.cast_mul]
