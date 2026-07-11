import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleBoundary

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Third-gene continuation for the rank-two singleton branch

The selected third gene cannot lie at the same rank as the second gene: equal
type would make the genes equal, while opposite type would violate no-pair.
Thus the remaining continuation starts at a genuinely later even rank.
-/

/-- Distinct polarized no-pair genes of normalized even ranks cannot have equal
rank parameters. -/
lemma no_pair_rank_two_single_third_gene_strict
    {N q₂ q₃ : ℕ} (X : nMixPi2Lambda N)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g₂ g₃ : Gene) (hXg₂ : 0 < X.1.1 g₂) (hXg₃ : 0 < X.1.1 g₃)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₃_pol : g₃.type ≠ GeneType.NonPolarized)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (hg₃_rank : g₃.rank = 2 * q₃ + 4)
    (hne : g₃ ≠ g₂) (hq : q₂ ≤ q₃) :
    q₂ < q₃ := by
  apply lt_of_le_of_ne hq
  intro heq
  have hrank : g₂.rank = g₃.rank := by omega
  rcases no_pair_rank_two_single_later_type_split g₂ g₃ hg₂_pol hg₃_pol with
    hsame | hopp
  · exact hne (Gene.ext hrank.symm hsame)
  · cases hg₂_type : g₂.type with
    | NonPolarized => exact False.elim (hg₂_pol hg₂_type)
    | Positive =>
        have hg₃_neg : g₃.type = GeneType.Negative := by
          rw [hopp, hg₂_type, GeneType.neg_positive]
        exact hno_pair ⟨g₂, g₃, hrank, hg₂_type, hg₃_neg, hXg₂, hXg₃⟩
    | Negative =>
        have hg₃_pos : g₃.type = GeneType.Positive := by
          rw [hopp, hg₂_type, GeneType.neg_negative]
        exact hno_pair ⟨g₃, g₂, hrank.symm, hg₃_pos, hg₂_type, hXg₃, hXg₂⟩

/-- Full normalized third-gene package for the remaining nonempty branch,
including strict rank separation, sign relation, and multiplicity split. -/
lemma no_pair_rank_two_single_third_gene_cases
    {m q₂ : ℕ} (X : nMixPi2Lambda (m + 2))
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene) (hg_one : X.1.1 g = 1)
    (hg₂_one : X.1.1 g₂ = 1) (hne : g ≠ g₂)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_rank : g₂.rank = 2 * q₂ + 4)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (restAfterG₂ : Chromosome)
    (hrestAfterG₂ :
      restAfterG₂ = X.1.1 - Finsupp.single g 1 - Finsupp.single g₂ 1)
    (hrest_ne : restAfterG₂ ≠ 0) :
    ∃ (g₃ : Gene) (q₃ : ℕ),
      0 < restAfterG₂ g₃ ∧
      (∀ h : Gene, 0 < restAfterG₂ h → g₃.rank ≤ h.rank) ∧
      0 < X.1.1 g₃ ∧ g₃ ≠ g ∧ g₃ ≠ g₂ ∧
      g₃.type ≠ GeneType.NonPolarized ∧
      g₃.rank = 2 * q₃ + 4 ∧ q₂ < q₃ ∧
      (g₃.type = g₂.type ∨ g₃.type = -g₂.type) ∧
      (X.1.1 g₃ = 1 ∨ 2 ≤ X.1.1 g₃) := by
  obtain ⟨g₃, q₃, hg₃_rest, hg₃min, hXg₃, hg₃_ne_g, hg₃_ne_g₂,
      hg₃_pol, hg₃_rank, hq₂q₃⟩ :=
    no_pair_rank_two_single_third_gene_data X hXpol g g₂ hg_one
      hg₂_one hne h2nd restAfterG₂ hrestAfterG₂ hrest_ne
  have hXg₂ : 0 < X.1.1 g₂ := by omega
  have hq_strict := no_pair_rank_two_single_third_gene_strict X hno_pair
    g₂ g₃ hXg₂ hXg₃ hg₂_pol hg₃_pol hg₂_rank hg₃_rank
      hg₃_ne_g₂ hq₂q₃
  have htype := no_pair_rank_two_single_later_type_split g₂ g₃
    hg₂_pol hg₃_pol
  have hmult : X.1.1 g₃ = 1 ∨ 2 ≤ X.1.1 g₃ := by omega
  exact ⟨g₃, q₃, hg₃_rest, hg₃min, hXg₃, hg₃_ne_g,
    hg₃_ne_g₂, hg₃_pol, hg₃_rank, hq_strict, htype, hmult⟩

/-- The exact-one odd window supplies the predecessor gap for the next Type10
move, now based at `g₂`. -/
lemma no_pair_rank_two_single_third_type10_pred_gap
    {m q₂ : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank <
      (Chromosome.prime^[1] Y.1.1).rank)
    (g g₂ : Gene) (hg_rank : g.rank = 2)
    (hg_one : X.1.1 g = 1) (hg₂_neg : g₂.type = -g.type)
    (h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
      2 * q₂ + 4 ≤ h.rank)
    (hone : RankTwoSingleExactOne X Y g) :
    ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[2 * q₂ + 3] X.1.1) ≤
      signature (Gene.ofRank 1 g₂.type) +
        signature (Chromosome.prime^[2 * q₂ + 3] Y.1.1) := by
  have hodd := no_pair_rank_two_single_type17_odd_mid_gaps
    X Y hXY hr1 g hg_rank hg_one h2nd hone
  rcases hone with ⟨hg_pos, _⟩ | ⟨hg_neg, _⟩
  · have hgap := hodd.1 hg_pos (2 * q₂ + 3) (by omega) (by omega)
      (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩)
    have hdom := le_iff_dominates.mp hXY.le (2 * q₂ + 3)
    have hg₂_type : g₂.type = GeneType.Negative := by
      rw [hg₂_neg, hg_pos, GeneType.neg_positive]
    rw [hg₂_type, signature_ofRank_one_negative]
    have hgap_fst := hgap.1
    have hdom_snd := hdom.2
    simp only [Prod.fst_add] at hgap_fst
    constructor
    · change 1 + (signature (Chromosome.prime^[2 * q₂ + 3] X.1.1)).1 ≤
        0 + (signature (Chromosome.prime^[2 * q₂ + 3] Y.1.1)).1
      linarith [hgap_fst]
    · change 1 + (signature (Chromosome.prime^[2 * q₂ + 3] X.1.1)).2 ≤
        1 + (signature (Chromosome.prime^[2 * q₂ + 3] Y.1.1)).2
      linarith [hdom_snd]
  · have hgap := hodd.2 hg_neg (2 * q₂ + 3) (by omega) (by omega)
      (Nat.not_even_iff_odd.mpr ⟨q₂ + 1, by ring⟩)
    have hdom := le_iff_dominates.mp hXY.le (2 * q₂ + 3)
    have hg₂_type : g₂.type = GeneType.Positive := by
      rw [hg₂_neg, hg_neg, GeneType.neg_negative]
    rw [hg₂_type, signature_ofRank_one_positive]
    have hgap_snd := hgap.2
    have hdom_fst := hdom.1
    simp only [Prod.snd_add] at hgap_snd
    constructor
    · change 1 + (signature (Chromosome.prime^[2 * q₂ + 3] X.1.1)).1 ≤
        1 + (signature (Chromosome.prime^[2 * q₂ + 3] Y.1.1)).1
      linarith [hdom_fst]
    · change 1 + (signature (Chromosome.prime^[2 * q₂ + 3] X.1.1)).2 ≤
        0 + (signature (Chromosome.prime^[2 * q₂ + 3] Y.1.1)).2
      linarith [hgap_snd]

end MixPi2Lambda
