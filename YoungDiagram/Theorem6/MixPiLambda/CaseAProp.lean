import YoungDiagram.Theorem6.MixPiLambda.Case1
import YoungDiagram.Theorem6.MixPiLambda.Case3
import YoungDiagram.Theorem6.MixPiLambda.Drops
import YoungDiagram.Theorem6.MixPiLambda.SigmaWindow
import YoungDiagram.Theorem6.MixPiLambda.Propagation

/-!
# §16 Case A Branch A infrastructure for `Mix (Pi, Lambda)` (label 2).

Parity-mirror of `MixLambdaPi/CaseA.lean` Branch A.  For `Mix (Pi, Lambda)` the
minimal nonpolarized gene `g₁` has ODD rank `2m'+1`, the §16 window is
odd-anchored, half-integer corrections land at EVEN levels and unit boosts at ODD
levels (via the odd propagation `branchA_hprop_odd_gen` of `Propagation.lean`).

Contents: the R2 reduction (`X ⊇ 2g(m)`, type4 diagonal), the dichotomy, the
Case 1 propagation core and the type4 assembly.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- A nonpolarized gene of `X ∈ Mix (Pi, Lambda)` has odd rank. -/
lemma rank_odd_of_nonpolarized_mem {X : Chromosome} (hX : X ∈ Mix (Pi, Lambda))
    {g : Gene} (hNP : g.type = .NonPolarized) (hgX : 0 < X g) :
    Odd g.rank := by
  by_contra hnot
  rw [Nat.not_odd_iff_even] at hnot
  have hev : 0 < X.evenPart g := by
    rw [evenPart_eq, Finsupp.filter_apply, if_pos hnot]; exact hgX
  have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp hX.1) g
    (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hev))
  rw [hNP] at hpol
  exact hpol rfl

/-- If `X` contains a nonpolarized gene `g`, then `signature (prime^[g.rank-1] X).1 ≥ 1/2`. -/
lemma half_le_signature_fst_of_contains_nonpolarized_mix {X : Chromosome}
    {g : Gene} (hNP : g.type = .NonPolarized) (hXg : 0 < X g) :
    (1 : ℚ) / 2 ≤ (signature (Chromosome.prime^[g.rank - 1] X)).1 := by
  have hr : 1 ≤ g.rank := g.rank_pos
  have hg_single : Gene.ofRank g.rank .NonPolarized = (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g); rw [hNP] at h; exact h
  have hprime : Chromosome.prime^[g.rank - 1] (Finsupp.single g 1 : Chromosome) =
      Gene.ofRank 1 .NonPolarized := by
    rw [← hg_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
  have hXeq : X = Finsupp.single g 1 + (X - Finsupp.single g 1) := by
    rw [add_comm, sub_single_add_single_eq hXg]
  calc (1 : ℚ) / 2
      = (signature (Gene.ofRank 1 .NonPolarized : Chromosome)).1 := by
        simp [signature_ofRank_nonPolarized]
    _ = (signature (Chromosome.prime^[g.rank - 1] (Finsupp.single g 1 : Chromosome))).1 := by
        rw [hprime]
    _ ≤ (signature (Chromosome.prime^[g.rank - 1] X)).1 := by
        conv_rhs => rw [hXeq]
        rw [iterate_map_add, map_add]
        exact le_add_of_nonneg_right (signature_nonneg _).1

/-- For disjoint `X, Y`, if `X` has a nonpolarized gene `g₁` of odd rank `r`, then `Y` has
no gene of rank `r` (the unique odd-rank gene shape is the nonpolarized `g₁`). -/
lemma Y_no_gene_of_odd_rank_mix {X Y : Chromosome}
    (hYmem : Y ∈ Mix (Pi, Lambda))
    (hcommon : ∀ g, 0 < X g → Y g ≤ 0)
    (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized) (hXg₁ : 0 < X g₁)
    {r : ℕ} (hr : g₁.rank = r) (hrev : Odd r)
    (g : Gene) (hgr : g.rank = r) : Y g = 0 := by
  by_contra hne
  have hgY : 0 < Y g := Nat.pos_of_ne_zero hne
  have hgY_odd : 0 < Y.oddPart g := by
    rw [oddPart_eq, Finsupp.filter_apply, if_pos (hgr ▸ hrev)]; exact hgY
  have hg_NP : g.type = .NonPolarized :=
    IsNonPolarized_def'.mp (mem_Lambda_iff.mp hYmem.2) g
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgY_odd))
  have hgeq : g = g₁ := Gene.ext (hgr.trans hr.symm) (hg_NP.trans hg₁NP.symm)
  subst hgeq
  have := hcommon g hXg₁
  omega

/-- The second sigma component is an integer at odd levels for `Mix (Pi, Lambda)`. -/
lemma sig_snd_isInt_odd {Z : Chromosome} (hZ : Z ∈ Mix (Pi, Lambda))
    {i : ℕ} (hi : Odd i) : ∃ z : ℤ, (Sigma.sigma Z i).2 = (z : ℚ) := by
  obtain ⟨a, ha⟩ := sig_fst_isInt_odd hZ hi
  have hsum : (signature (Chromosome.prime^[i] Z)).1 + (signature (Chromosome.prime^[i] Z)).2 =
      ((Chromosome.prime^[i] Z).rank : ℚ) := signature_sum_eq_rank
  refine ⟨((Chromosome.prime^[i] Z).rank : ℤ) - a, ?_⟩
  have : (Sigma.sigma Z i).2 = ((Chromosome.prime^[i] Z).rank : ℚ) - (Sigma.sigma Z i).1 := by
    show (signature (Chromosome.prime^[i] Z)).2 = _
    have : (Sigma.sigma Z i).1 = (signature (Chromosome.prime^[i] Z)).1 := rfl
    rw [this] at *; linarith
  rw [this, ha]; push_cast; ring

/-- Odd-level strict `<` upgrades to `+1 ≤` on the first sigma component (integrality). -/
lemma add_one_le_sigma_fst_of_lt_odd {A B : Chromosome}
    (hA : A ∈ Mix (Pi, Lambda)) (hB : B ∈ Mix (Pi, Lambda)) {i : ℕ} (hi : Odd i)
    (hlt : (Sigma.sigma A i).1 < (Sigma.sigma B i).1) :
    (Sigma.sigma A i).1 + 1 ≤ (Sigma.sigma B i).1 := by
  obtain ⟨a, ha⟩ := sig_fst_isInt_odd hA hi
  obtain ⟨b, hb⟩ := sig_fst_isInt_odd hB hi
  rw [ha, hb] at hlt ⊢
  have hab : a < b := by exact_mod_cast hlt
  have : (a : ℚ) + 1 ≤ b := by exact_mod_cast hab
  linarith

/-- Odd-level strict `<` upgrades to `+1 ≤` on the second sigma component (integrality). -/
lemma add_one_le_sigma_snd_of_lt_odd {A B : Chromosome}
    (hA : A ∈ Mix (Pi, Lambda)) (hB : B ∈ Mix (Pi, Lambda)) {i : ℕ} (hi : Odd i)
    (hlt : (Sigma.sigma A i).2 < (Sigma.sigma B i).2) :
    (Sigma.sigma A i).2 + 1 ≤ (Sigma.sigma B i).2 := by
  obtain ⟨a, ha⟩ := sig_snd_isInt_odd hA hi
  obtain ⟨b, hb⟩ := sig_snd_isInt_odd hB hi
  rw [ha, hb] at hlt ⊢
  have hab : a < b := by exact_mod_cast hlt
  have : (a : ℚ) + 1 ≤ b := by exact_mod_cast hab
  linarith

/-- Decomposition `2g + (X - 2g) = X` when `X` has multiplicity `≥ 2` at `g`. -/
lemma X_eq_double_add_rest {X : Chromosome} {g : Gene} (hXg : 2 ≤ X g) :
    Finsupp.single g 1 + Finsupp.single g 1 +
      (X - Finsupp.single g 1 - Finsupp.single g 1) = X := by
  ext g'
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases h1 : g = g'
  · subst h1; simp; omega
  · simp [if_neg h1]

/-- **R2 reduction, single step.** The type4 diagonal mutation
`2g(m) → g^{-ε}(m-1) + g^ε(m+1)` produces `Z ≤ Y`, given the boost at the odd level
`r = 2m'+1` (`hboost`). -/
lemma branchA_R2_step {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (m' : ℕ) (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized)
    (hg₁rank : g₁.rank = 2 * m' + 1) (hXg₁2 : 2 ≤ X.1.1 g₁)
    (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hboost : signature (Gene.ofRank 1 (-ε)) +
        signature (Chromosome.prime^[2 * m' + 1] X.1.1) ≤
        signature (Chromosome.prime^[2 * m' + 1] Y.1.1)) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let X4' : Mix (Pi, Lambda) := X4 (le_refl m')
  let Y4' : Mix (Pi, Lambda) := Y4 (le_refl m') hε
  have hg₁_eq : Gene.ofRank (2 * m' + 1) .NonPolarized = (Finsupp.single g₁ 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g₁); rw [hg₁rank, hg₁NP] at h; exact h
  have hX4_val : X4'.1 = Finsupp.single g₁ 1 + Finsupp.single g₁ 1 := by
    show (X4 (le_refl m')).1 = _
    rw [X4_eq, hg₁_eq]
  let restval : Chromosome := X.1.1 - Finsupp.single g₁ 1 - Finsupp.single g₁ 1
  have rest_mem : restval ∈ Mix (Pi, Lambda) :=
    sub_mem_Mix_Pi_Lambda _ (sub_mem_Mix_Pi_Lambda _ X.1.2)
  let rest_M : Mix (Pi, Lambda) := ⟨restval, rest_mem⟩
  have hX_eq : X4'.1 + restval = X.1.1 := by
    rw [hX4_val]; exact X_eq_double_add_rest hXg₁2
  let Z : Mix (Pi, Lambda) := ⟨Y4'.1 + restval, add_mem Y4'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X4 (le_refl m') : Mix (Pi, Lambda)) + rest_M = X.1) ▸
    MixPiLambda.Step.mk (X4 (le_refl m')) Y4' rest_M
      (MixPiLambda.Primitive.type4 ε hε (le_refl m')), ?_⟩
  change Y4'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] X4'.1) + signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) :=
    le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m'
  · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
        signature (Chromosome.prime^[j] X4'.1) :=
      (sigma_type4_eq_before (le_refl m') hε (hj := hj)).symm
    rw [hY4X4, ← hdecomp]; exact hXYj
  · by_cases hj_after : 2 * m' + 2 ≤ j
    · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
          signature (Chromosome.prime^[j] X4'.1) :=
        (sigma_type4_eq_after (le_refl m') hε (hj := hj_after)).symm
      rw [hY4X4, ← hdecomp]; exact hXYj
    · have hjeq : j = 2 * m' + 1 := by omega
      subst hjeq
      have hmid := sigma_type4_mid (le_refl m') hε (j := 2 * m' + 1) (by omega) (by omega)
      rw [show 2 * m' + 1 - (2 * m' + 1) = 0 from by omega, if_pos (by decide : Even 0)] at hmid
      have hY4_eq : signature (Chromosome.prime^[2 * m' + 1] Y4'.1) =
          signature (Chromosome.prime^[2 * m' + 1] X4'.1) + signature (Gene.ofRank 1 (-ε)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY4_eq]
      have heq : signature (Chromosome.prime^[2 * m' + 1] X4'.1) + signature (Gene.ofRank 1 (-ε))
            + signature (Chromosome.prime^[2 * m' + 1] restval)
          = signature (Gene.ofRank 1 (-ε)) + signature (Chromosome.prime^[2 * m' + 1] X.1.1) := by
        rw [hdecomp]; abel
      rw [heq]; exact hboost

/-- **Branch A dichotomy.** For the minimal nonpolarized gene `g₁` (rank `2m'+1`, odd),
disjointness gives `Y` no gene of rank `2m'+1`, hence `prime^[2m'+1] Y ≠ 0`, and `(16.1)`
forces `r_m < s_m`; so `a_m < c_m` or `b_m < d_m`. -/
lemma branchA_dichotomy {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' : ℕ) (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized)
    (hg₁rank : g₁.rank = 2 * m' + 1) (hXg₁ : 0 < X.1.1 g₁) :
    (Sigma.sigma X.1.1 (2 * m' + 1)).1 < (Sigma.sigma Y.1.1 (2 * m' + 1)).1 ∨
    (Sigma.sigma X.1.1 (2 * m' + 1)).2 < (Sigma.sigma Y.1.1 (2 * m' + 1)).2 := by
  push_neg at hcommon hsigeq
  have hrev : Odd (2 * m' + 1) := ⟨m', by ring⟩
  have hr1 : 1 ≤ 2 * m' + 1 := by omega
  have hY_no_gene : ∀ g : Gene, g.rank = 2 * m' + 1 → Y.1.1 g = 0 :=
    fun g hgr => Y_no_gene_of_odd_rank_mix Y.1.2 hcommon g₁ hg₁NP hXg₁ hg₁rank hrev g hgr
  have h_half : (1 : ℚ) / 2 ≤ (signature (Chromosome.prime^[2 * m'] X.1.1)).1 := by
    have := half_le_signature_fst_of_contains_nonpolarized_mix hg₁NP hXg₁
    rwa [hg₁rank, show 2 * m' + 1 - 1 = 2 * m' from by omega] at this
  have hYr1 : Chromosome.prime^[2 * m'] Y.1.1 ≠ 0 := by
    intro heq
    have hdom : (signature (Chromosome.prime^[2 * m'] X.1.1)).1 ≤
        (signature (Chromosome.prime^[2 * m'] Y.1.1)).1 :=
      (le_iff_dominates.mp hXY.le (2 * m')).1
    rw [heq, map_zero] at hdom
    simp only [Prod.fst_zero] at hdom; linarith
  have hYr : Chromosome.prime^[2 * m' + 1] Y.1.1 ≠ 0 :=
    prime_ne_zero_of_Y_no_gene_mix hr1 hY_no_gene
      (show Chromosome.prime^[(2 * m' + 1) - 1] Y.1.1 ≠ 0 by
        rwa [show 2 * m' + 1 - 1 = 2 * m' from by omega])
  have hsig_ne : Sigma.sigma X.1.1 (2 * m' + 1) ≠ Sigma.sigma Y.1.1 (2 * m' + 1) :=
    hsigeq (2 * m' + 1) (by omega) hYr
  have hle_r : Sigma.sigma X.1.1 (2 * m' + 1) ≤ Sigma.sigma Y.1.1 (2 * m' + 1) :=
    le_iff_dominates.mp hXY.le (2 * m' + 1)
  rcases lt_or_eq_of_le hle_r.1 with h | h
  · exact Or.inl h
  · rcases lt_or_eq_of_le hle_r.2 with h2 | h2
    · exact Or.inr h2
    · exact absurd (Prod.ext h h2) hsig_ne

/-- **R2 reduction.** When `X` contains `2g(m)` (the minimal-rank nonpolarized gene `g₁` has
multiplicity `≥ 2`), the §16 step `2g(m) → g^{-ε}(m-1) + g^ε(m+1)` applies. -/
lemma branchA_R2 {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' : ℕ) (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized)
    (hg₁rank : g₁.rank = 2 * m' + 1) (hXg₁2 : 2 ≤ X.1.1 g₁) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXg₁ : 0 < X.1.1 g₁ := by omega
  have hrev : Odd (2 * m' + 1) := ⟨m', by ring⟩
  have hle_r : Sigma.sigma X.1.1 (2 * m' + 1) ≤ Sigma.sigma Y.1.1 (2 * m' + 1) :=
    le_iff_dominates.mp hXY.le (2 * m' + 1)
  rcases branchA_dichotomy X Y hXY hcommon hsigeq m' g₁ hg₁NP hg₁rank hXg₁ with hlt | hlt
  · have hint : (Sigma.sigma X.1.1 (2 * m' + 1)).1 + 1 ≤ (Sigma.sigma Y.1.1 (2 * m' + 1)).1 :=
      add_one_le_sigma_fst_of_lt_odd X.1.2 Y.1.2 hrev hlt
    refine branchA_R2_step X Y hXY m' g₁ hg₁NP hg₁rank hXg₁2 .Negative (by decide) ?_
    rw [GeneType.neg_negative, signature_ofRank_one_positive]
    refine ⟨?_, ?_⟩
    · show (1 : ℚ) + (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).1 ≤
        (signature (Chromosome.prime^[2 * m' + 1] Y.1.1)).1
      have h1 : (Sigma.sigma X.1.1 (2 * m' + 1)).1 =
        (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).1 := rfl
      have h2 : (Sigma.sigma Y.1.1 (2 * m' + 1)).1 =
        (signature (Chromosome.prime^[2 * m' + 1] Y.1.1)).1 := rfl
      rw [h1, h2] at hint; linarith
    · show (0 : ℚ) + (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).2 ≤
        (signature (Chromosome.prime^[2 * m' + 1] Y.1.1)).2
      rw [zero_add]; exact hle_r.2
  · have hint : (Sigma.sigma X.1.1 (2 * m' + 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (2 * m' + 1)).2 :=
      add_one_le_sigma_snd_of_lt_odd X.1.2 Y.1.2 hrev hlt
    refine branchA_R2_step X Y hXY m' g₁ hg₁NP hg₁rank hXg₁2 .Positive (by decide) ?_
    rw [GeneType.neg_positive, signature_ofRank_one_negative]
    refine ⟨?_, ?_⟩
    · show (0 : ℚ) + (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).1 ≤
        (signature (Chromosome.prime^[2 * m' + 1] Y.1.1)).1
      rw [zero_add]; exact hle_r.1
    · show (1 : ℚ) + (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).2 ≤
        (signature (Chromosome.prime^[2 * m' + 1] Y.1.1)).2
      have h1 : (Sigma.sigma X.1.1 (2 * m' + 1)).2 =
        (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).2 := rfl
      have h2 : (Sigma.sigma Y.1.1 (2 * m' + 1)).2 =
        (signature (Chromosome.prime^[2 * m' + 1] Y.1.1)).2 := rfl
      rw [h1, h2] at hint; linarith

/-- **Propagation core** of §16 Branch A Case 1 for `Mix (Pi, Lambda)` (odd-anchored).
Takes the self-dual total-rank gap `hgap_nat`. -/
lemma exists_mutation_le_caseA_branchA_case1_propagate {N : ℕ}
    (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hgap_nat : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 1) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 1 ≤ g.rank)
    (ha_m : (Sigma.sigma X.1.1 (2 * m' + 1)).1 < (Sigma.sigma Y.1.1 (2 * m' + 1)).1) :
    (∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * n' + 1 → Odd j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1) ∧
    (∀ j, 2 * m' + 1 ≤ j → j < 2 * n' + 1 → Chromosome.prime^[j] Y.1.1 ≠ 0) := by
  refine ⟨?_, ?_⟩
  · exact branchA_case1_hprop_odd X Y hgap_nat m' n' hmn gm gk hgm_rank hgm_np hgk_rank hgk_np
      hXgm hXgk hne hmin h2nd ha_m
  · intro j _ hj2
    have hXgk0 : 0 < X.1.1 gk :=
      lt_of_lt_of_le hXgk (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
    have hgk_supp : gk ∈ X.1.1.support :=
      Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hXgk0)
    have hXj : Chromosome.prime^[j] X.1.1 ≠ 0 := by
      intro hzero
      have hle := (prime_iterate_eq_zero_rank_le).mpr hzero gk hgk_supp
      rw [hgk_rank] at hle
      omega
    intro hYzero
    have hsig_le : signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
    rw [hYzero, map_zero] at hsig_le
    exact hXj (signature_eq_zero (le_antisymm hsig_le (signature_nonneg _)))

/-- **Assembly** of §16 Branch A Case 1 for `Mix (Pi, Lambda)`, given the propagation
outputs.  Builds the `type4` step `g(m)+g(k) → g⁻(m-1)+g⁺(k+1)` (ε = `.Negative`) and
proves `Z ≤ Y`: outside the window source/target agree; inside, the odd-level unit `(1,0)`
is absorbed by `hprop_odd` and the even-level `(1/2,1/2)` by `half_le_sigma_diff_at_r`. -/
lemma exists_mutation_le_caseA_branchA_case1 {N : ℕ}
    (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 1) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_odd : ∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * n' + 1 → Odd j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 2 * m' + 1 ≤ j → j < 2 * n' + 1 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  push_neg at hsigeq
  have hε : GeneType.Negative ≠ .NonPolarized := by decide
  let Y4' : Mix (Pi, Lambda) := Y4 hmn hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Pi, Lambda) :=
    sub_mem_Mix_Pi_Lambda _ (sub_mem_Mix_Pi_Lambda _ X.1.2)
  let rest_M : Mix (Pi, Lambda) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * m' + 1) .NonPolarized = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_np] at h; exact h
  have hgk_eq : Gene.ofRank (2 * n' + 1) .NonPolarized = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_np] at h; exact h
  have hX4_val : (X4 hmn).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X4_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X4 hmn).1 + restval = X.1.1 := by
    rw [hX4_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Pi, Lambda) := ⟨Y4'.1 + restval, add_mem Y4'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X4 hmn : Mix (Pi, Lambda)) + rest_M = X.1) ▸
    MixPiLambda.Step.mk (X4 hmn) Y4' rest_M
      (MixPiLambda.Primitive.type4 GeneType.Negative hε hmn), ?_⟩
  change Y4'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X4 hmn).1) + signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) :=
    le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m'
  · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
        signature (Chromosome.prime^[j] (X4 hmn).1) :=
      (sigma_type4_eq_before hmn hε (hj := hj)).symm
    rw [hY4X4, ← hdecomp]
    exact hXYj
  · have h_not_before : 2 * m' < j := by omega
    by_cases hj_after : 2 * n' + 2 ≤ j
    · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
          signature (Chromosome.prime^[j] (X4 hmn).1) :=
        (sigma_type4_eq_after hmn hε (hj := hj_after)).symm
      rw [hY4X4, ← hdecomp]
      exact hXYj
    · have h_mid : j < 2 * n' + 2 := by omega
      have hmid := sigma_type4_mid hmn hε h_not_before h_mid
      have hY4_eq : signature (Chromosome.prime^[j] Y4'.1) =
          signature (Chromosome.prime^[j] (X4 hmn).1) +
            (if Even (2 * n' + 1 - j) then signature (Gene.ofRank 1 (-GeneType.Negative))
             else ((1 : ℚ) / 2, (1 : ℚ) / 2)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY4_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 1 - j)
      · rw [if_pos hpar]
        have h_odd_j : Odd j := by
          have hp : (2 * n' + 1 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.odd_iff]; omega
        have h_sig_pos : signature (Gene.ofRank 1 (-GeneType.Negative)) = ((1 : ℚ), (0 : ℚ)) := by
          rw [GeneType.neg_negative, signature_ofRank_one_positive]
        rw [h_sig_pos]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have h_sigma := hprop_odd j (by omega) (by omega) h_odd_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · show (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · show (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          rw [add_zero]; exact hXYj.2
      · rw [if_neg hpar]
        have heven_j : Even j := by
          have hp : (2 * n' + 1 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.even_iff]; omega
        have hne' : signature (Chromosome.prime^[j] X.1.1) ≠
            signature (Chromosome.prime^[j] Y.1.1) := by
          intro h_eq
          exact hsigeq j (by omega)
            (hYwin j (by omega) (by rcases heven_j with ⟨t, rfl⟩; omega))
            (by simpa [Sigma.sigma] using h_eq)
        rw [add_comm]
        exact half_le_sigma_diff_at_r X.1.2 Y.1.2 heven_j hXYj hne'

/-- **b-propagation core for §16 Branch A Case 2** (`Mix (Pi, Lambda)`).  The
`b`-component analogue of `branchA_case1_hprop_odd`, via the sign-dual `(-X, -Y)`
(where `a_{-X} = b_X`).  Anchored at the odd minimal NP gene rank `2m'+1`.  The level-1
asymmetry of `Mix (Pi, Lambda)` is sidestepped because `branchA_hprop_odd_gen` now takes
the *total* rank gap `r_1 < s_1` (self-dual under negation), supplied by `rank_gap_one`. -/
lemma branchA_case2_bprop {N : ℕ}
    (X Y : nMixPiLambda N)
    (hgap_nat : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm : Gene) (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgm1 : X.1.1 gm = 1)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 1 ≤ g.rank)
    (hb_m : (Sigma.sigma X.1.1 (2 * m' + 1)).2 < (Sigma.sigma Y.1.1 (2 * m' + 1)).2) :
    ∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * n' + 1 → Odd j →
        (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2 := by
  have hg₁neg : (-gm : Gene) = gm := Gene.ext (Gene.neg_rank gm) (by rw [Gene.neg_type, hgm_np]; rfl)
  set Xd : nMixPiLambda N := ⟨- X.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, X.2]⟩ with Xd_def
  set Yd : nMixPiLambda N := ⟨- Y.1, by rw [Mix.Pi_Lambda_neg_val, rank_neg, Y.2]⟩ with Yd_def
  have hgap_d : (Chromosome.prime^[1] Xd.1.1).rank < (Chromosome.prime^[1] Yd.1.1).rank := by
    have e1 : Chromosome.prime^[1] Xd.1.1 = - (Chromosome.prime^[1] X.1.1) := by
      change Chromosome.prime^[1] (- X.1.1) = _; rw [prime_iterate_neg]
    have e2 : Chromosome.prime^[1] Yd.1.1 = - (Chromosome.prime^[1] Y.1.1) := by
      change Chromosome.prime^[1] (- Y.1.1) = _; rw [prime_iterate_neg]
    rw [e1, e2, rank_neg, rank_neg]
    exact hgap_nat
  have hgm1_d : Xd.1.1 gm = 1 := by
    change (- X.1.1) gm = 1; rw [Chromosome.neg_apply, hg₁neg]; exact hgm1
  have hmin_d : ∀ g ∈ Xd.1.1.support, 2 * m' + 1 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff] at hg
    have hng : X.1.1 (-g) ≠ 0 := by
      change (- X.1.1) g ≠ 0 at hg; rwa [Chromosome.neg_apply] at hg
    have h := hmin (-g) (Finsupp.mem_support_iff.mpr hng); rwa [Gene.neg_rank] at h
  have hsingle_neg : ∀ g, (Finsupp.single gm 1 : Chromosome) g =
      (Finsupp.single gm 1 : Chromosome) (-g) := by
    intro g
    have hiff : (gm = g) ↔ (gm = -g) := by
      constructor
      · rintro rfl; exact hg₁neg.symm
      · intro h
        have h2 : -gm = g := by rw [h, neg_neg]
        rw [← hg₁neg]; exact h2
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : gm = g
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hval : ∀ g, (Xd.1.1 - Finsupp.single gm 1 : Chromosome) g
      = (X.1.1 - Finsupp.single gm 1 : Chromosome) (-g) := by
    intro g; rw [Finsupp.tsub_apply, Finsupp.tsub_apply, hsingle_neg g]; congr 1
  have h2nd_d : ∀ g ∈ (Xd.1.1 - Finsupp.single gm 1).support, 2 * n' + 1 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, hval g] at hg
    have h := h2nd (-g) (Finsupp.mem_support_iff.mpr hg); rwa [Gene.neg_rank] at h
  have ha_m_d : (Sigma.sigma Xd.1.1 (2 * m' + 1)).1 <
      (Sigma.sigma Yd.1.1 (2 * m' + 1)).1 := by
    change (signature (Chromosome.prime^[2 * m' + 1] (- X.1.1))).1 <
      (signature (Chromosome.prime^[2 * m' + 1] (- Y.1.1))).1
    rw [← @prime_iterate_neg (2 * m' + 1) X.1.1, ← @prime_iterate_neg (2 * m' + 1) Y.1.1,
      signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    exact hb_m
  have hgen := branchA_hprop_odd_gen Xd Yd hgap_d m' n' hmn gm hgm_rank hgm_np
    hgm1_d hmin_d h2nd_d ha_m_d
  intro j hj1 hj2 hoj
  have hg := hgen j hj1 hj2 hoj
  have hconvX : (Sigma.sigma Xd.1.1 j).1 = (Sigma.sigma X.1.1 j).2 := by
    change (signature (Chromosome.prime^[j] (- X.1.1))).1 =
      (signature (Chromosome.prime^[j] X.1.1)).2
    rw [← @prime_iterate_neg j X.1.1, signature_neg, Prod.fst_swap]
  have hconvY : (Sigma.sigma Yd.1.1 j).1 = (Sigma.sigma Y.1.1 j).2 := by
    change (signature (Chromosome.prime^[j] (- Y.1.1))).1 =
      (signature (Chromosome.prime^[j] Y.1.1)).2
    rw [← @prime_iterate_neg j Y.1.1, signature_neg, Prod.fst_swap]
  rw [hconvX, hconvY] at hg; exact hg

/-- **Assembly** of §16 Branch A Case 2 (`g₂ = g⁺(k)`) for `Mix (Pi, Lambda)`.  Builds the
`type5` step `g(m)+g⁺(k) → g⁺(m-1)+g(k+1)` (ε = `.Positive`) and proves `Z ≤ Y` over the
window `2m' < j < 2n'+3`: outside source/target agree; inside, the odd-level `(0,1)` is
absorbed by `hprop_odd` (the `b`-propagation) and the even-level `(1/2,1/2)` by
`half_le_sigma_diff_at_r`. -/
lemma exists_mutation_le_caseA_branchA_case2_assembly {N : ℕ}
    (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_pos : gk.type = .Positive)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_odd : ∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * n' + 1 → Odd j →
        (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2)
    (hYwin : ∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  push_neg at hsigeq
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y5' : Mix (Pi, Lambda) := Y5 hmn hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Pi, Lambda) :=
    sub_mem_Mix_Pi_Lambda _ (sub_mem_Mix_Pi_Lambda _ X.1.2)
  let rest_M : Mix (Pi, Lambda) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * m' + 1) .NonPolarized = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_np] at h; exact h
  have hgk_eq : Gene.ofRank (2 * n' + 2) .Positive = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_pos] at h; exact h
  have hX5_val : (X5 hmn hε).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X5_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X5 hmn hε).1 + restval = X.1.1 := by
    rw [hX5_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Pi, Lambda) := ⟨Y5'.1 + restval, add_mem Y5'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X5 hmn hε : Mix (Pi, Lambda)) + rest_M = X.1) ▸
    MixPiLambda.Step.mk (X5 hmn hε) Y5' rest_M
      (MixPiLambda.Primitive.type5 GeneType.Positive hε hmn), ?_⟩
  change Y5'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X5 hmn hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m'
  · have h54 : signature (Chromosome.prime^[j] Y5'.1) =
        signature (Chromosome.prime^[j] (X5 hmn hε).1) :=
      (sigma_type5_eq_before hmn hε (hj := hj)).symm
    rw [h54, ← hdecomp]; exact hXYj
  · have h_not_before : 2 * m' < j := by omega
    by_cases hj_after : 2 * n' + 3 ≤ j
    · have h54 : signature (Chromosome.prime^[j] Y5'.1) =
          signature (Chromosome.prime^[j] (X5 hmn hε).1) :=
        (sigma_type5_eq_after hmn hε (hj := hj_after)).symm
      rw [h54, ← hdecomp]; exact hXYj
    · have h_mid : j < 2 * n' + 3 := by omega
      have hmid := sigma_type5_mid hmn hε h_not_before h_mid
      have hY5_eq : signature (Chromosome.prime^[j] Y5'.1) =
          signature (Chromosome.prime^[j] (X5 hmn hε).1) +
            (if Even (2 * n' + 2 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
             else signature (Gene.ofRank 1 (-GeneType.Positive))) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY5_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 2 - j)
      · rw [if_pos hpar]
        have heven_j : Even j := by
          have hp : (2 * n' + 2 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.even_iff]; omega
        have hne' : signature (Chromosome.prime^[j] X.1.1) ≠
            signature (Chromosome.prime^[j] Y.1.1) := by
          intro h_eq
          exact hsigeq j (by omega) (hYwin j (by omega) (by obtain ⟨t, ht⟩ := heven_j; omega))
            (by simpa [Sigma.sigma] using h_eq)
        rw [add_comm]
        exact half_le_sigma_diff_at_r X.1.2 Y.1.2 heven_j hXYj hne'
      · rw [if_neg hpar]
        have hodd_j : Odd j := by
          have hp : (2 * n' + 2 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.odd_iff]; omega
        have h_sig_neg : signature (Gene.ofRank 1 (-GeneType.Positive)) = ((0 : ℚ), (1 : ℚ)) := by
          rw [GeneType.neg_positive, signature_ofRank_one_negative]
        rw [h_sig_neg]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).2 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2 := by
          have hjle : j ≤ 2 * n' + 1 := by rcases hodd_j with ⟨t, rfl⟩; omega
          have h_sigma := hprop_odd j (by omega) hjle hodd_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · show (signature (Chromosome.prime^[j] X.1.1)).1 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          rw [add_zero]; exact hXYj.1
        · show (signature (Chromosome.prime^[j] X.1.1)).2 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          exact h_sigXj

end MixPiLambda
