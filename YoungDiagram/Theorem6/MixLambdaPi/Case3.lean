import YoungDiagram.Theorem6.MixLambdaPi.Prelim

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-! ## Case 3: disjoint supports, X contains a positive/negative gene pair -/

/-- For `X ∈ Mix (Lambda, Pi)` with `0 < X g` and `g.type = .Positive`, the gene `g`
has odd rank (and so does the symmetric situation for `.Negative`). -/
private lemma rank_odd_of_polarized {X : Chromosome} (hX : X ∈ Mix (Lambda, Pi))
    {g : Gene} (hpol : g.type ≠ .NonPolarized) (hgX : 0 < X g) :
    Odd g.rank := by
  by_contra hnot
  rw [Nat.not_odd_iff_even] at hnot
  -- Since g.rank is even, g ∈ evenPart X.
  have hev : 0 < X.evenPart g := by
    rw [evenPart_eq, Finsupp.filter_apply, if_pos hnot]; exact hgX
  -- evenPart ∈ Lambda, so g.type = .NonPolarized
  have := IsNonPolarized_def'.mp (mem_Lambda_iff.mp hX.1) g
    (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hev))
  exact hpol this

/-- The polarized parts of two genes in `X ∈ Mix (Lambda, Pi)` with equal rank have
odd rank (= `2 * m + 1`). -/
private lemma rank_eq_two_mul_succ_of_pn {gpos gneg : Gene}
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hrank : gpos.rank = gneg.rank) {X : Chromosome}
    (hX : X ∈ Mix (Lambda, Pi)) (hXgpos : 0 < X gpos) (hXgneg : 0 < X gneg) :
    ∃ m : ℕ, gpos.rank = 2 * m + 1 := by
  have hodd : Odd gpos.rank :=
    rank_odd_of_polarized hX (by rw [hgpos]; decide) hXgpos
  rcases hodd with ⟨m, hm⟩
  exact ⟨m, by omega⟩

/-- Helper: for any chromosome `Z` with all genes of even rank in its support,
signature has equal components. -/
private lemma signature_eq_components_of_even_support {Z : Chromosome}
    (hev : ∀ g ∈ Z.support, Even g.rank) :
    (signature Z).1 = (signature Z).2 := by
  rw [signature_fst, signature_snd]
  apply Finset.sum_congr rfl
  intros g hg
  have hg_ev := hev g hg
  have hg_sig : g.signature.1 = g.signature.2 := by
    have h1 : g.signature = ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2) := by
      cases ht : g.type with
      | NonPolarized => exact Gene.signature_of_nonPolarized ht
      | Positive =>
        rw [Gene.signature_of_positive ht, if_pos hg_ev]
      | Negative =>
        rw [Gene.signature_of_negative ht, if_pos hg_ev]
    rw [h1]
  simp [hg_sig]

/-- Helper: for `W ∈ Lambda` (entire support is NonPolarized), signature has equal
components since all genes are NonPolarized. -/
private lemma signature_eq_components_of_mem_Lambda {W : Chromosome} (hW : W ∈ Lambda) :
    (signature W).1 = (signature W).2 := by
  rw [signature_fst, signature_snd]
  apply Finset.sum_congr rfl
  intros g hg
  have hg_NP : g.type = .NonPolarized :=
    IsNonPolarized_def'.mp (mem_Lambda_iff.mp hW) g hg
  have hg_sig : g.signature.1 = g.signature.2 := by
    rw [Gene.signature_of_nonPolarized hg_NP]
  simp [hg_sig]

/-- For `X ∈ Mix (Lambda, Pi)`, `prime^[j] X` at *odd* `j` lies in `Mix (Pi, Lambda)`,
so its signature has equal components. -/
lemma signature_prime_iterate_odd_eq_components
    {X : Chromosome} (hX : X ∈ Mix (Lambda, Pi)) {j : ℕ} (hj : Odd j) :
    (signature (Chromosome.prime^[j] X)).1 = (signature (Chromosome.prime^[j] X)).2 := by
  have hmem : Chromosome.prime^[j] X ∈ Mix (Pi, Lambda) := by
    have := Variety.prime_mem_Mix_Lambda_Pi_iterate hX j
    rwa [if_neg (Nat.not_even_iff_odd.mpr hj)] at this
  set Y := Chromosome.prime^[j] X with hY_def
  have hYev : Y.evenPart ∈ Pi := hmem.1
  have hYod : Y.oddPart ∈ Lambda := hmem.2
  have ev_eq : (signature Y.evenPart).1 = (signature Y.evenPart).2 := by
    apply signature_eq_components_of_even_support
    intros g hg
    have : Y.evenPart g ≠ 0 := Finsupp.mem_support_iff.mp hg
    by_contra hodd
    rw [evenPart_eq, Finsupp.filter_apply, if_neg hodd] at this
    exact this rfl
  have od_eq : (signature Y.oddPart).1 = (signature Y.oddPart).2 :=
    signature_eq_components_of_mem_Lambda hYod
  -- Y = Y.oddPart + Y.evenPart (parity_decomposition).
  have hY_decomp : Y = Y.oddPart + Y.evenPart := Y.parity_decomposition
  rw [hY_decomp, map_add, Prod.fst_add, Prod.snd_add, ev_eq, od_eq]

/-- Signature analog of `Pi.signature_type1_eq_before` for type 7 with `m = n`. -/
private lemma signature_type7_eq_before {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {m j : ℕ} (hj : j < 2 * m + 1) :
    signature (Chromosome.prime^[j] (Y7 (le_refl m)).1) =
      signature (Chromosome.prime^[j] (X7 (le_refl m) hε).1) := by
  rw [X7_eq, Y7_eq, iterate_map_add, iterate_map_add,
    prime_iterate_ofRank, prime_iterate_ofRank, prime_iterate_ofRank, prime_iterate_ofRank,
    map_add, map_add]
  have eq1 : 2 * m + 1 - j = 2 * m - j + 1 := by omega
  have eq2 : 2 * m + 1 - j = 2 * m + 2 - j - 1 := by omega
  have hn : 1 ≤ 2 * m + 2 - j := by omega
  have heven : Even (2 * m - j + (2 * m + 2 - j)) := by
    rw [Nat.even_iff]; omega
  have h := signature_ofRank_succ_add_pred_neg (m := 2 * m - j) (n := 2 * m + 2 - j)
    (ε := ε) hn heven
  rw [← eq1, ← eq2] at h
  exact h.symm

/-- At iterate `j = 2m+1 = r`, the type-7 source has zero signature. -/
private lemma signature_type7_source_self_eq_zero {ε : GeneType}
    (hε : ε ≠ .NonPolarized) {m : ℕ} :
    signature (Chromosome.prime^[2 * m + 1] (X7 (le_refl m) hε).1) = 0 := by
  rw [X7_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank]
  simp [Nat.sub_self, Gene.ofRank_zero]

/-- At iterate `j = 2m+1 = r`, the type-7 target has signature `(1/2, 1/2)`. -/
private lemma signature_type7_target_self_eq_half {m : ℕ} :
    signature (Chromosome.prime^[2 * m + 1] (Y7 (n := m) (le_refl m)).1) =
      ((1 : ℚ) / 2, (1 : ℚ) / 2) := by
  rw [Y7_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    show 2 * m - (2 * m + 1) = 0 from by omega,
    show 2 * m + 2 - (2 * m + 1) = 1 from by omega]
  simp [Gene.ofRank_zero, signature_ofRank_nonPolarized]

/-- For `j > r = 2m+1`, the type-7 source has zero signature. -/
private lemma signature_type7_source_after_eq_zero {ε : GeneType}
    (hε : ε ≠ .NonPolarized) {m j : ℕ} (hj : 2 * m + 1 < j) :
    signature (Chromosome.prime^[j] (X7 (le_refl m) hε).1) = 0 := by
  rw [X7_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    show 2 * m + 1 - j = 0 from by omega]
  simp [Gene.ofRank_zero]

/-- For `j > r = 2m+1`, the type-7 target has zero signature. -/
private lemma signature_type7_target_after_eq_zero {m j : ℕ}
    (hj : 2 * m + 1 < j) :
    signature (Chromosome.prime^[j] (Y7 (n := m) (le_refl m)).1) = 0 := by
  rw [Y7_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank,
    show 2 * m - j = 0 from by omega,
    show 2 * m + 2 - j = 0 from by omega]
  simp [Gene.ofRank_zero]

/-- `Y` has no gene of rank `r` when `X` contains a positive/negative pair of rank `r`
and `X`, `Y` have disjoint supports (only the polarized rank-`r` slots matter, because
`Y.oddPart ∈ Pi` so any rank-`r` gene in `Y` must be polarized). -/
private lemma Y_no_gene_of_rank_mix {X Y : Chromosome}
    (hYmem : Y ∈ Mix (Lambda, Pi))
    (hcommon : ∀ g, 0 < X g → Y g ≤ 0)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hXgpos : 0 < X gpos) (hXgneg : 0 < X gneg)
    {r : ℕ} (hrank_pos : gpos.rank = r) (hodd : Odd r)
    (g : Gene) (hgr : g.rank = r) : Y g = 0 := by
  by_contra hne
  have hgY : 0 < Y g := Nat.pos_of_ne_zero hne
  -- g has odd rank, so g ∈ Y.oddPart ∈ Pi, so g.type ≠ NonPolarized.
  have hgY_odd : 0 < Y.oddPart g := by
    rw [oddPart_eq, Finsupp.filter_apply, if_pos (hgr ▸ hodd)]; exact hgY
  have hg_pol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (mem_Pi_iff.mp hYmem.2) g
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgY_odd))
  cases ht : g.type with
  | NonPolarized => exact hg_pol ht
  | Positive =>
    have hgeq : g = gpos :=
      Gene.ext (hgr.trans hrank_pos.symm) (ht.trans hgpos.symm)
    subst hgeq
    have h := hcommon g hXgpos
    omega
  | Negative =>
    have hgeq : g = gneg :=
      Gene.ext (hgr.trans hrank_pos.symm |>.trans hrank) (ht.trans hgneg.symm)
    subst hgeq
    have h := hcommon g hXgneg
    omega

/-- After iterating `prime` past `r-1` levels, the result is zero. -/
lemma prime_iterate_no_gene_of_rank_mix {Y : Chromosome} {r : ℕ}
    (hY_no_gene : ∀ g : Gene, g.rank = r → Y g = 0)
    (j : ℕ) (hj : j ≤ r - 1) (h : Gene) (hh : h.rank = r - j) :
    (Chromosome.prime^[j] Y) h = 0 := by
  induction j generalizing h with
  | zero => exact hY_no_gene h (by omega)
  | succ j ihj =>
    simp only [Function.iterate_succ', Function.comp,
      prime_def, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    simp only [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro g hg
    have hg_ne : (Chromosome.prime^[j] Y) g ≠ 0 := Finsupp.mem_support_iff.mp hg
    by_cases hrk : g.rank - 1 = h.rank
    · exfalso
      have _ := g.rank_pos
      exact hg_ne (ihj (by omega) g (by omega))
    · simp only [Nat.mul_eq_zero]
      right
      simp only [primeGene, Gene.ofRank_def]
      split_ifs with h0
      · rfl
      · rw [Finsupp.single_apply, if_neg]
        intro heq
        exact hrk (congrArg Gene.rank heq)

lemma prime_ne_zero_of_Y_no_gene_mix {Y : Chromosome} {r : ℕ} (hr : 1 ≤ r)
    (hY_no_gene : ∀ g : Gene, g.rank = r → Y g = 0)
    (hYr_minus_one : Chromosome.prime^[r - 1] Y ≠ 0) :
    Chromosome.prime^[r] Y ≠ 0 := by
  have hr_eq : r = 1 + (r - 1) := by omega
  rw [hr_eq, Function.iterate_add_apply, Function.iterate_one]
  apply prime_ne_zero_of_rank_ge_two hYr_minus_one
  intro h hmem
  rw [Finsupp.mem_support_iff] at hmem
  by_contra! hlt
  have hh1 : h.rank = 1 := le_antisymm (by omega) h.rank_pos
  exact hmem (prime_iterate_no_gene_of_rank_mix hY_no_gene (r - 1) (by omega) h (by omega))

/-- For `X ∈ Mix (Lambda, Pi)`, if `X` contains a positive gene of rank `r`,
then `signature (prime^[r-1] X) .1 ≥ 1`. -/
lemma one_le_signature_fst_of_contains_positive_mix {X : Chromosome}
    (hX : X ∈ Mix (Lambda, Pi)) {gpos : Gene}
    (hgpos : gpos.type = .Positive) (hXgpos : 0 < X gpos) :
    1 ≤ (signature (Chromosome.prime^[gpos.rank - 1] X)).1 := by
  let r := gpos.rank
  have hr : 1 ≤ r := gpos.rank_pos
  have hgpos_single : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rw [hgpos] at h
    exact h
  have hprime_gpos : Chromosome.prime^[r - 1] (Finsupp.single gpos 1 : Chromosome) =
      Gene.ofRank 1 .Positive := by
    rw [← hgpos_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
  have hXeq : X = Finsupp.single gpos 1 + (X - Finsupp.single gpos 1) := by
    rw [add_comm, sub_single_add_single_eq hXgpos]
  calc (1 : ℚ)
      = (signature (Gene.ofRank 1 .Positive : Chromosome)).1 := by
        simp [signature_ofRank_one_positive]
    _ = (signature (Chromosome.prime^[r - 1] (Finsupp.single gpos 1 : Chromosome))).1 := by
        rw [hprime_gpos]
    _ ≤ (signature (Chromosome.prime^[r - 1] X)).1 := by
        conv_rhs => rw [hXeq]
        rw [iterate_map_add, map_add]
        exact le_add_of_nonneg_right (signature_nonneg _).1

lemma X_eq_X7_add_rest_mix {X : Chromosome} {gpos gneg : Gene}
    (hXgpos : 0 < X gpos) (hXgneg : 0 < X gneg) (hne : gpos ≠ gneg) :
    Finsupp.single gpos 1 + Finsupp.single gneg 1 +
      (X - Finsupp.single gpos 1 - Finsupp.single gneg 1) = X := by
  ext g'
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases h1 : gpos = g'
  · subst h1
    have h2 : gneg ≠ gpos := hne.symm
    simp [if_neg h2]
    omega
  · by_cases h2 : gneg = g'
    · subst h2
      simp [if_neg hne]
      omega
    · simp [if_neg h1, if_neg h2]

/-- Helper: for `X ∈ Mix (Lambda, Pi)` at odd r, 2 * signature(prime^[r] X).1 is a natural
number. This relies on the fact that 2 * (sig.1 + sig.2) = 2 * rank ∈ ℕ and sig.1 = sig.2. -/
lemma two_signature_fst_isNat_of_odd_iterate
    {X : Chromosome} (hX : X ∈ Mix (Lambda, Pi)) {r : ℕ} (hodd : Odd r) :
    ∃ n : ℕ, 2 * (signature (Chromosome.prime^[r] X)).1 = n := by
  set Z := Chromosome.prime^[r] X with hZ_def
  have hZeq : (signature Z).1 = (signature Z).2 :=
    signature_prime_iterate_odd_eq_components hX hodd
  -- (sig Z).1 + (sig Z).2 = Z.rank, so 2 * (sig Z).1 = Z.rank.
  have hsum : (signature Z).1 + (signature Z).2 = Z.rank :=
    signature_sum_eq_rank
  refine ⟨Z.rank, ?_⟩
  have : 2 * (signature Z).1 = (signature Z).1 + (signature Z).2 := by rw [hZeq]; ring
  rw [this, hsum]

/-- Sigma columns at level r (r odd) have equal components for elements of
`Mix (Lambda, Pi)`. Combined with strict inequality, the difference is at least 1/2 in
each component. -/
lemma half_le_sigma_diff_at_r {X Y : Chromosome}
    (hX : X ∈ Mix (Lambda, Pi)) (hY : Y ∈ Mix (Lambda, Pi))
    {r : ℕ} (hodd : Odd r)
    (hle : signature (Chromosome.prime^[r] X) ≤ signature (Chromosome.prime^[r] Y))
    (hne : signature (Chromosome.prime^[r] X) ≠ signature (Chromosome.prime^[r] Y)) :
    ((1 : ℚ) / 2, (1 : ℚ) / 2) + signature (Chromosome.prime^[r] X) ≤
      signature (Chromosome.prime^[r] Y) := by
  have hXeq := signature_prime_iterate_odd_eq_components hX hodd
  have hYeq := signature_prime_iterate_odd_eq_components hY hodd
  set sX := signature (Chromosome.prime^[r] X) with hsX
  set sY := signature (Chromosome.prime^[r] Y) with hsY
  obtain ⟨nX, hnX⟩ := two_signature_fst_isNat_of_odd_iterate hX hodd
  obtain ⟨nY, hnY⟩ := two_signature_fst_isNat_of_odd_iterate hY hodd
  change 2 * sX.1 = (nX : ℚ) at hnX
  change 2 * sY.1 = (nY : ℚ) at hnY
  have h_le_fst : sX.1 ≤ sY.1 := hle.1
  have h_ne : sX.1 ≠ sY.1 := by
    intro heq
    apply hne
    ext
    · exact heq
    · rw [← hXeq, ← hYeq]; exact heq
  have h_lt : sX.1 < sY.1 := lt_of_le_of_ne h_le_fst h_ne
  have hnatlt : (nX : ℚ) < nY := by linarith
  have h_nat_lt : nX < nY := by exact_mod_cast hnatlt
  have hnat_succ : (nX : ℚ) + 1 ≤ nY := by exact_mod_cast (Nat.succ_le_of_lt h_nat_lt)
  constructor
  · simp only [Prod.fst_add]
    linarith
  · simp only [Prod.snd_add]
    rw [← hXeq, ← hYeq]
    linarith

lemma exists_mutation_le_disjoint_pair {m : ℕ}
    (X Y : nMixLambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.1 g ∧ 0 < X.1.1 h) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hcommon hsigeq
  obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXgpos, hXgneg⟩ := hXpn
  -- gpos.rank is odd, so write it as 2 * mr + 1.
  have hodd_gpos : Odd gpos.rank :=
    rank_odd_of_polarized X.1.2 (by rw [hgpos]; decide) hXgpos
  obtain ⟨mr, hmr⟩ : ∃ mr : ℕ, gpos.rank = 2 * mr + 1 := by
    rcases hodd_gpos with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  let r := gpos.rank
  have hr : 1 ≤ r := gpos.rank_pos
  have hr_eq : r = 2 * mr + 1 := hmr
  have hr_odd : Odd r := hodd_gpos
  -- Y has no gene of rank r.
  have hY_no_gene : ∀ (g : Gene), g.rank = r → Y.1.1 g = 0 :=
    Y_no_gene_of_rank_mix Y.1.2 hcommon gpos gneg hrank hgpos hgneg hXgpos hXgneg
      (r := r) rfl hr_odd
  -- Show prime^[r] Y.1.1 ≠ 0 using positive-gene chasing.
  have h1a : 1 ≤ (signature (Chromosome.prime^[r - 1] X.1.1)).1 :=
    one_le_signature_fst_of_contains_positive_mix X.1.2 hgpos hXgpos
  have h1c : Chromosome.prime^[r - 1] Y.1.1 ≠ 0 := by
    intro heq
    have h1b : 1 ≤ (signature (Chromosome.prime^[r - 1] Y.1.1)).1 :=
      le_trans h1a ((le_iff_dominates.mp hXY.le (r - 1)).1)
    have : (signature (Chromosome.prime^[r - 1] Y.1.1)).1 = 0 := by simp [heq]
    linarith
  have hYr : Chromosome.prime^[r] Y.1.1 ≠ 0 :=
    prime_ne_zero_of_Y_no_gene_mix hr hY_no_gene h1c
  have hsig_ne : Sigma.sigma X.1.1 r ≠ Sigma.sigma Y.1.1 r := hsigeq r hr hYr
  have hle_r : Sigma.sigma X.1.1 r ≤ Sigma.sigma Y.1.1 r :=
    le_iff_dominates.mp hXY.le r
  -- restval := X.1.1 - single gpos 1 - single gneg 1.
  let restval := X.1.1 - Finsupp.single gpos 1 - Finsupp.single gneg 1
  have hne : gpos ≠ gneg := by
    intro h
    apply absurd (congrArg Gene.type h)
    rw [hgpos, hgneg]
    decide
  -- The "ofRank" equalities.
  have hgpos_eq : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) := by
    rw [← hgpos]
    exact Gene.ofRank_eq_gene
  have hgneg_eq : Gene.ofRank r .Negative = (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rw [hgneg] at h
    rwa [← hrank] at h
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  -- Set ε = .Positive (the case split is unnecessary here since X7, Y7 are
  -- symmetric in (Positive, Negative)).
  let ε : GeneType := .Positive
  have hε : ε ≠ .NonPolarized := by decide
  let X7' : Mix (Lambda, Pi) := X7 (m := mr) (n := mr) (le_refl mr) hε
  let Y7' : Mix (Lambda, Pi) := Y7 (m := mr) (n := mr) (le_refl mr)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hX7_val : X7'.1 = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
    show (X7 (m := mr) (n := mr) (le_refl mr) hε).1 = _
    rw [X7_eq, ← hr_eq, GeneType.neg_positive, hgpos_eq, hgneg_eq]
  have hX_eq : X7'.1 + restval = X.1.1 := by
    rw [hX7_val]
    exact X_eq_X7_add_rest_mix hXgpos hXgneg hne
  let Z : Mix (Lambda, Pi) := ⟨Y7'.1 + restval, add_mem Y7'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : X7' + rest_M = X.1) ▸
    MixLambdaPi.Step.mk X7' Y7' rest_M
      (MixLambdaPi.Primitive.type7 ε hε (le_refl mr)), ?_⟩
  change Y7'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] X7'.1) + signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) :=
    le_iff_dominates.mp hXY.le j
  rcases lt_trichotomy j r with hjr | rfl | hjr
  · -- j < r: signature(prime^[j] X7) = signature(prime^[j] Y7).
    have hY7X7 : signature (Chromosome.prime^[j] Y7'.1) =
        signature (Chromosome.prime^[j] X7'.1) := by
      have := signature_type7_eq_before (m := mr) hε (show j < 2 * mr + 1 from hr_eq ▸ hjr)
      exact this
    rw [hY7X7, ← hdecomp]
    exact hXYj
  · -- j = r: signature(prime^[r] X7) = 0, signature(prime^[r] Y7) = (1/2, 1/2).
    have hX7zero : signature (Chromosome.prime^[r] X7'.1) = 0 := by
      have := signature_type7_source_self_eq_zero (m := mr) hε
      rw [hr_eq]; exact this
    have hY7half : signature (Chromosome.prime^[r] Y7'.1) = ((1 : ℚ) / 2, (1 : ℚ) / 2) := by
      have := signature_type7_target_self_eq_half (m := mr)
      rw [hr_eq]; exact this
    have hrest_eq : signature (Chromosome.prime^[r] restval) =
        signature (Chromosome.prime^[r] X.1.1) := by
      rw [hdecomp, hX7zero, zero_add]
    rw [hY7half, hrest_eq]
    -- Need: (1/2, 1/2) + signature(prime^[r] X) ≤ signature(prime^[r] Y).
    have hsig_ne' : signature (Chromosome.prime^[r] X.1.1) ≠
        signature (Chromosome.prime^[r] Y.1.1) := hsig_ne
    apply half_le_sigma_diff_at_r X.1.2 Y.1.2 hr_odd hXYj hsig_ne'
  · -- j > r: both prime iterates are zero in signature.
    have hX7zero : signature (Chromosome.prime^[j] X7'.1) = 0 := by
      have := signature_type7_source_after_eq_zero (m := mr) hε
        (show 2 * mr + 1 < j from hr_eq ▸ hjr)
      exact this
    have hY7zero : signature (Chromosome.prime^[j] Y7'.1) = 0 := by
      have := signature_type7_target_after_eq_zero (m := mr)
        (show 2 * mr + 1 < j from hr_eq ▸ hjr)
      exact this
    have hrestj : signature (Chromosome.prime^[j] restval) =
        signature (Chromosome.prime^[j] X.1.1) := by
      rw [hdecomp, hX7zero, zero_add]
    rw [hY7zero, zero_add, hrestj]
    exact hXYj

end MixLambdaPi
