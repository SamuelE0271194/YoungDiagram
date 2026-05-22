import YoungDiagram.Theorem6.Case4B.Common

open Variety hiding prime prime_def
open Chromosome

/-! Case 4b, even rank-gap and odd lower rank. -/

set_option linter.unusedVariables false in
lemma exists_mutation_le_case4b_evenGap_oddRank
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
    (hε₂ : ¬ g₂.type = -g₁.type)
    (hparity : Even (g₂.rank - g₁.rank))
    (h_g1_rank_odd : ¬Even g₁.rank) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 :=
  exists_mutation_le_case4b_evenGap_of_sigma_window X Y hXg₁ hg₁_ge2 hg₁_one
    hg₂pos hg₂rank hε₂ <| by
      intro hε hle hm j
      -- TODO: prove the odd lower-rank window estimates.
      sorry
