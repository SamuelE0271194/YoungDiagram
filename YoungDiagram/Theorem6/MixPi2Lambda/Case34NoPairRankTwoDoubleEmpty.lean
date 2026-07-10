import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoBranches
import YoungDiagram.Theorem6.MixPi2Lambda.Case34Seed

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Label 4 no-pair rank-two double-empty leaf

This module closes the first actual mutation leaf under the prepared no-pair
rank-`2` dispatcher.  The three type10 dominance gaps are first exposed as a
reusable interface, then discharged by the rank-`2` specialization of the
paper's §17 Case 2 drop argument.
-/

/-- The first iterate of the double-empty rank-`2` source is exactly two copies
of the corresponding rank-`1` gene, at the signature level. -/
lemma no_pair_rank_two_double_empty_prime_one_signature {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
    (g : Gene)
    (hg_rank : g.rank = 2)
    (hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1) :
    signature (Chromosome.prime^[1] X.1.1) =
      signature (Gene.ofRank 1 g.type) + signature (Gene.ofRank 1 g.type) := by
  have hg_single :
      (Finsupp.single g 1 : Chromosome) = Gene.ofRank 2 g.type := by
    rw [← Gene.ofRank_eq_gene (g := g), hg_rank]
  rw [hXeq, hg_single, iterate_map_add, prime_iterate_ofRank, map_add]

/-- The second iterate of the double-empty rank-`2` source vanishes. -/
lemma no_pair_rank_two_double_empty_prime_two_zero {m : ℕ}
    (X : nMixPi2Lambda (m + 2))
    (g : Gene)
    (hg_rank : g.rank = 2)
    (hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1) :
    Chromosome.prime^[2] X.1.1 = 0 := by
  have hg_single :
      (Finsupp.single g 1 : Chromosome) = Gene.ofRank 2 g.type := by
    rw [← Gene.ofRank_eq_gene (g := g), hg_rank]
  rw [hXeq, hg_single, iterate_map_add, prime_iterate_ofRank]
  simp

/-- In the double-empty rank-`2` leaf, dominance forces `Y` to have nonzero
level-`1` iterate. -/
lemma no_pair_rank_two_double_empty_Y_prime_one_ne {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (g : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1) :
    Chromosome.prime^[1] Y.1.1 ≠ 0 := by
  intro hYzero
  have hle := le_iff_dominates.mp hXY.le 1
  have hsigX :=
    no_pair_rank_two_double_empty_prime_one_signature X g hg_rank hXeq
  have hsigY : signature (Chromosome.prime^[1] Y.1.1) = 0 := by
    rw [hYzero, map_zero]
  cases htype : g.type with
  | NonPolarized => exact False.elim (hg_pol htype)
  | Positive =>
      have hle_fst := hle.1
      rw [hsigX, hsigY] at hle_fst
      simp [htype, signature_ofRank_one_positive] at hle_fst
      linarith
  | Negative =>
      have hle_snd := hle.2
      rw [hsigX, hsigY] at hle_snd
      simp [htype, signature_ofRank_one_negative] at hle_snd
      linarith

/-- The level-`1` strict gap from (17.1), oriented according to the type10
predecessor gap.  If the preferred component is not strict, the opposite
component is recorded as the fallback branch for the later boundary analysis. -/
lemma no_pair_rank_two_double_empty_pred_component_split {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1) :
    (g.type = GeneType.Positive ∧
        ((signature (Chromosome.prime^[1] X.1.1)).2 <
            (signature (Chromosome.prime^[1] Y.1.1)).2 ∨
          (¬ (signature (Chromosome.prime^[1] X.1.1)).2 <
              (signature (Chromosome.prime^[1] Y.1.1)).2 ∧
            (signature (Chromosome.prime^[1] X.1.1)).1 <
              (signature (Chromosome.prime^[1] Y.1.1)).1))) ∨
      (g.type = GeneType.Negative ∧
        ((signature (Chromosome.prime^[1] X.1.1)).1 <
            (signature (Chromosome.prime^[1] Y.1.1)).1 ∨
          (¬ (signature (Chromosome.prime^[1] X.1.1)).1 <
              (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
            (signature (Chromosome.prime^[1] X.1.1)).2 <
              (signature (Chromosome.prime^[1] Y.1.1)).2))) := by
  have hY1 :
      Chromosome.prime^[1] Y.1.1 ≠ 0 :=
    no_pair_rank_two_double_empty_Y_prime_one_ne X Y hXY g hg_pol
      hg_rank hXeq
  cases htype : g.type with
  | NonPolarized => exact False.elim (hg_pol htype)
  | Positive =>
      exact Or.inl ⟨rfl,
        prime_iterate_snd_or_fst_lt X Y hXY h17_1
          (k := 1) (by omega) hY1⟩
  | Negative =>
      exact Or.inr ⟨rfl,
        prime_iterate_fst_or_snd_lt X Y hXY h17_1
          (k := 1) (by omega) hY1⟩

/-- The double-empty rank-`2` no-pair leaf reduces to the standard doubled-gene
type10 gap interface. -/
lemma exists_mutation_le_no_pair_rank_two_double_empty_of_type10_gaps {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (g : Gene)
    (_hgX : 0 < X.1.1 g)
    (_hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (_hneg_zero : X.1.1 (-g) = 0)
    (restAfterDouble : Chromosome)
    (_hrestAfterDouble :
      restAfterDouble = X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (_hrest_zero : restAfterDouble = 0)
    (hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1)
    (_hm2 : m = 2)
    (_hsigX : signature X.1.1 = ((2 : ℚ), (2 : ℚ)))
    (_hX3 : Chromosome.prime^[3] X.1.1 = 0)
    (hgap_pred :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[1] X.1.1) ≤
        signature (Gene.ofRank 1 g.type) +
          signature (Chromosome.prime^[1] Y.1.1))
    (hgap_mid :
      ∀ j, 2 ≤ j → j ≤ 2 →
        ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1))
    (hgap_succ :
      signature (Gene.ofRank 1 g.type) +
          signature (Chromosome.prime^[3] X.1.1) ≤
        signature (Chromosome.prime^[3] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg_rank0 : g.rank = 2 * 0 + 2 := by
    omega
  have hg_two : 2 ≤ X.1.1 g := by
    rw [hXeq]
    simp
  have hZle :
      (Y10 (le_refl 0) hg_pol hg_pol).1 +
          (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1) ≤ Y.1.1 := by
    refine type10_double_target_add_rest_le_of_gaps
      (q := 0) hg_pol X Y hXY g rfl hg_rank0 hg_two ?_ ?_ ?_
    · simpa using hgap_pred
    · intro j hjlo hjhi
      exact hgap_mid j hjlo hjhi
    · simpa using hgap_succ
  exact exists_mutation_le_type10_of_double hg_pol X Y g rfl hg_rank0
    hg_two hZle

/-- The successor gap in §17 Case 2.  The paper's chain
`r₁-r₂ = r₀-r₁ > s₀-s₁ ≥ s₁-s₂` combines with (15.6)/(15.7) at level `1`
to force the component matching the sign of the doubled rank-`2` gene to be
strict at level `3`. -/
lemma no_pair_rank_two_double_empty_case2_succ_gap {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1)
    (hm2 : m = 2)
    (hX3 : Chromosome.prime^[3] X.1.1 = 0) :
    signature (Gene.ofRank 1 g.type) +
        signature (Chromosome.prime^[3] X.1.1) ≤
      signature (Chromosome.prime^[3] Y.1.1) := by
  have hY1 :=
    no_pair_rank_two_double_empty_Y_prime_one_ne X Y hXY g hg_pol
      hg_rank hXeq
  have hr1 := h17_1 1 (by omega) hY1
  have hsigX1 :=
    no_pair_rank_two_double_empty_prime_one_signature X g hg_rank hXeq
  have hX0sum :
      (signature X.1.1).1 + (signature X.1.1).2 = 4 := by
    rw [signature_sum_eq_rank, X.2, hm2]
    norm_num
  have hY0sum :
      (signature Y.1.1).1 + (signature Y.1.1).2 = 4 := by
    rw [signature_sum_eq_rank, Y.2, hm2]
    norm_num
  have hr1Q :
      (signature (Chromosome.prime^[1] X.1.1)).1 +
          (signature (Chromosome.prime^[1] X.1.1)).2 <
        (signature (Chromosome.prime^[1] Y.1.1)).1 +
          (signature (Chromosome.prime^[1] Y.1.1)).2 := by
    simp only [signature_sum_eq_rank]
    exact_mod_cast hr1
  have hdrop :
      (signature (Chromosome.prime^[1] Y.1.1)).1 +
            (signature (Chromosome.prime^[1] Y.1.1)).2 -
          ((signature (Chromosome.prime^[2] Y.1.1)).1 +
            (signature (Chromosome.prime^[2] Y.1.1)).2) ≤
        (signature Y.1.1).1 + (signature Y.1.1).2 -
          ((signature (Chromosome.prime^[1] Y.1.1)).1 +
            (signature (Chromosome.prime^[1] Y.1.1)).2) := by
    simpa [Sigma.sigma] using rank_drop_le Y.1.2 1
  have hY2eq :
      (signature (Chromosome.prime^[2] Y.1.1)).1 =
        (signature (Chromosome.prime^[2] Y.1.1)).2 :=
    Mix2LambdaSection17.signature_prime_iterate_even_eq_components_L4
      Y.1.2 ⟨1, by omega⟩
  have hcond6 :
      (signature (Chromosome.prime^[2] Y.1.1)).1 -
          (signature (Chromosome.prime^[3] Y.1.1)).1 ≤
        (signature (Chromosome.prime^[1] Y.1.1)).2 -
          (signature (Chromosome.prime^[2] Y.1.1)).2 := by
    have h := Mix2LambdaSection17.cond_15_6_Mix_Pi_2Lambda Y.1.2 1
    rw [if_neg (by decide : ¬ Even 1)] at h
    simpa [Sigma.sigma] using h
  have hcond7 :
      (signature (Chromosome.prime^[2] Y.1.1)).2 -
          (signature (Chromosome.prime^[3] Y.1.1)).2 ≤
        (signature (Chromosome.prime^[1] Y.1.1)).1 -
          (signature (Chromosome.prime^[2] Y.1.1)).1 := by
    have h := Mix2LambdaSection17.cond_15_7_Mix_Pi_2Lambda Y.1.2 1
    rw [if_neg (by decide : ¬ Even 1)] at h
    simpa [Sigma.sigma] using h
  have hdom := le_iff_dominates.mp hXY.le 1
  cases htype : g.type with
  | NonPolarized => exact False.elim (hg_pol htype)
  | Positive =>
      have hX1fst :
          (signature (Chromosome.prime^[1] X.1.1)).1 = 2 := by
        rw [hsigX1]
        norm_num [htype, signature_ofRank_one_positive]
      have hX1snd :
          (signature (Chromosome.prime^[1] X.1.1)).2 = 0 := by
        rw [hsigX1]
        norm_num [htype, signature_ofRank_one_positive]
      have hX3fst :
          (signature (Chromosome.prime^[3] X.1.1)).1 = 0 := by
        rw [hX3, map_zero]
        rfl
      have hfst :
          (signature (Chromosome.prime^[3] X.1.1)).1 <
            (signature (Chromosome.prime^[3] Y.1.1)).1 := by
        linarith [hdom.1]
      simpa [htype] using
        type10_succ_gap_positive X Y hXY (q := 0) hfst
  | Negative =>
      have hX1fst :
          (signature (Chromosome.prime^[1] X.1.1)).1 = 0 := by
        rw [hsigX1]
        norm_num [htype, signature_ofRank_one_negative]
      have hX1snd :
          (signature (Chromosome.prime^[1] X.1.1)).2 = 2 := by
        rw [hsigX1]
        norm_num [htype, signature_ofRank_one_negative]
      have hX3snd :
          (signature (Chromosome.prime^[3] X.1.1)).2 = 0 := by
        rw [hX3, map_zero]
        rfl
      have hsnd :
          (signature (Chromosome.prime^[3] X.1.1)).2 <
            (signature (Chromosome.prime^[3] Y.1.1)).2 := by
        linarith [hdom.2]
      simpa [htype] using
        type10_succ_gap_negative X Y hXY (q := 0) hsnd

/-- In the double-empty specialization, the wrong predecessor component from
(17.1) is impossible: level-`0` signatures agree, while `signature_prime_le`
bounds the wrong level-`1` component by the corresponding value `2` already
attained by `X`. -/
lemma no_pair_rank_two_double_empty_case2_pred_gap {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g : Gene)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1)
    (hsigX : signature X.1.1 = ((2 : ℚ), (2 : ℚ))) :
    ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[1] X.1.1) ≤
      signature (Gene.ofRank 1 g.type) +
        signature (Chromosome.prime^[1] Y.1.1) := by
  have hsplit :=
    no_pair_rank_two_double_empty_pred_component_split X Y hXY h17_1
      g hg_pol hg_rank hXeq
  have hsigX1 :=
    no_pair_rank_two_double_empty_prime_one_signature X g hg_rank hXeq
  have hsig0 : signature X.1.1 = signature Y.1.1 := by
    simpa [Sigma.sigma] using sigma_zero_eq X Y hXY
  have hY1fst_le :
      (signature (Chromosome.prime^[1] Y.1.1)).1 ≤
        (signature Y.1.1).1 := by
    simpa [Function.iterate_one] using
      (((signature_prime_le Y.1.1).trans inf_le_left).1)
  have hY1snd_le :
      (signature (Chromosome.prime^[1] Y.1.1)).2 ≤
        (signature Y.1.1).2 := by
    simpa [Function.iterate_one] using
      (((signature_prime_le Y.1.1).trans inf_le_left).2)
  rcases hsplit with ⟨htype, hsnd_or_fst⟩ | ⟨htype, hfst_or_snd⟩
  · rcases hsnd_or_fst with hsnd | ⟨_hnsnd, hfst⟩
    · simpa [htype] using type10_pred_gap_positive X Y hXY (p := 0)
        (by simpa [htype] using hsnd)
    · exfalso
      have hX1fst :
          (signature (Chromosome.prime^[1] X.1.1)).1 = 2 := by
        rw [hsigX1]
        norm_num [htype, signature_ofRank_one_positive]
      rw [← hsig0, hsigX] at hY1fst_le
      norm_num at hY1fst_le
      simp only [Function.iterate_one] at hfst hX1fst
      linarith [hX1fst, hfst]
  · rcases hfst_or_snd with hfst | ⟨_hnfst, hsnd⟩
    · simpa [htype] using type10_pred_gap_negative X Y hXY (p := 0)
        (by simpa [htype] using hfst)
    · exfalso
      have hX1snd :
          (signature (Chromosome.prime^[1] X.1.1)).2 = 2 := by
        rw [hsigX1]
        norm_num [htype, signature_ofRank_one_negative]
      rw [← hsig0, hsigX] at hY1snd_le
      norm_num at hY1snd_le
      simp only [Function.iterate_one] at hsnd hX1snd
      linarith [hX1snd, hsnd]

/-- The rank-`2` double-empty no-pair leaf of §17 Case 2.  The predecessor and
successor gaps are forced by the Case 2 drop argument; successor nonvanishing
then supplies the unique even middle gap. -/
lemma exists_mutation_le_no_pair_rank_two_double_empty {m : ℕ}
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (g : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2)
    (hneg_zero : X.1.1 (-g) = 0)
    (restAfterDouble : Chromosome)
    (hrestAfterDouble :
      restAfterDouble = X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (hrest_zero : restAfterDouble = 0)
    (hXeq : X.1.1 = Finsupp.single g 1 + Finsupp.single g 1)
    (hm2 : m = 2)
    (hsigX : signature X.1.1 = ((2 : ℚ), (2 : ℚ)))
    (hX3 : Chromosome.prime^[3] X.1.1 = 0) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hgap_pred := no_pair_rank_two_double_empty_case2_pred_gap
    X Y hXY h17_1 g hg_pol hg_rank hXeq hsigX
  have hgap_succ := no_pair_rank_two_double_empty_case2_succ_gap
    X Y hXY h17_1 g hg_pol hg_rank hXeq hm2 hX3
  have hY3 : Chromosome.prime^[3] Y.1.1 ≠ 0 := by
    intro hY3
    cases htype : g.type with
    | NonPolarized => exact hg_pol htype
    | Positive =>
        have h := hgap_succ.1
        rw [hX3, hY3, map_zero] at h
        norm_num [htype, signature_ofRank_one_positive] at h
    | Negative =>
        have h := hgap_succ.2
        rw [hX3, hY3, map_zero] at h
        norm_num [htype, signature_ofRank_one_negative] at h
  have hY2 : Chromosome.prime^[2] Y.1.1 ≠ 0 :=
    Chromosome.prime_iterate_ne_zero_if_prime_ne (j := 2) (k := 3)
      (by omega) hY3
  have hgap_mid :
      ∀ j, 2 ≤ j → j ≤ 2 →
        ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1) := by
    intro j hjlo hjhi
    have hj : j = 2 := by omega
    subst j
    exact type10_mid_gap_even_of_Y_ne X Y h17_1
      (heven := ⟨1, by norm_num⟩) (hjpos := by omega) hY2
  exact exists_mutation_le_no_pair_rank_two_double_empty_of_type10_gaps
    X Y hXY g hgX hgmin hg_pol hg_rank hneg_zero restAfterDouble
    hrestAfterDouble hrest_zero hXeq hm2 hsigX hX3
    hgap_pred hgap_mid hgap_succ

end MixPi2Lambda
