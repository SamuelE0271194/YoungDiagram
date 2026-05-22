import YoungDiagram.Theorem6.Case4B.EvenGapEvenRank
import YoungDiagram.Theorem6.Case4B.EvenGapOddRank
import YoungDiagram.Theorem6.Case4B.OddGapEvenRank
import YoungDiagram.Theorem6.Case4B.OddGapOddRank

open Variety hiding prime prime_def
open Chromosome

/-! Dispatcher for Case 4b of §15.10. -/

lemma exists_mutation_le_case4b
    {n : ℕ} (X Y : nPi n) (hXY : X.1 < Y.1)
    {g₁ g₂ : Gene}
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1)
    (hε₁ : ¬ g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative)
    (hXg₁ : X.1.val g₁ ≠ 0)
    (hXg₁pos : 0 < X.1.val g₁)
    (hg₁min : ∀ g ∈ X.1.val.support, g₁.rank ≤ g.rank)
    (hg₁_ge2 : 2 ≤ g₁.rank)
    (hg₁_one : X.1.val g₁ = 1)
    (hg₂pos : 0 < X.1.val g₂)
    (hg₂rank : g₁.rank < g₂.rank)
    (hg₂min : ∀ g' : Gene, 0 < X.1.val g' → g₁.rank < g'.rank → g₂.rank ≤ g'.rank)
    (hε₂ : ¬ g₂.type = -g₁.type) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hparity : Even (g₂.rank - g₁.rank)
  · by_cases h_g1_rank_even : Even g₁.rank
    · exact exists_mutation_le_case4b_evenGap_evenRank X Y hXY hXpn ha hε₁ hXg₁
        hXg₁pos hg₁min hg₁_ge2 hg₁_one hg₂pos hg₂rank hg₂min hε₂ hparity
        h_g1_rank_even
    · exact exists_mutation_le_case4b_evenGap_oddRank X Y hXY hXpn ha hε₁ hXg₁
        hXg₁pos hg₁min hg₁_ge2 hg₁_one hg₂pos hg₂rank hg₂min hε₂ hparity
        h_g1_rank_even
  · by_cases h_g1_rank_even : Even g₁.rank
    · exact exists_mutation_le_case4b_oddGap_evenRank X Y hXY hXpn ha hε₁
        hXg₁ hXg₁pos hg₁min hg₁_ge2 hg₁_one hg₂pos hg₂rank hg₂min hε₂ hparity h_g1_rank_even
    · exact exists_mutation_le_case4b_oddGap_oddRank X Y hXY hXpn ha hε₁
        hXg₁ hXg₁pos hg₁min hg₁_ge2 hg₁_one hg₂pos hg₂rank hg₂min hε₂ hparity h_g1_rank_even
