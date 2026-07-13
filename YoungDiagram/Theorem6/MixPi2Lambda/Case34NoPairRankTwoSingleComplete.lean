import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoClosed
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSinglePreferred

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Complete rank-two singleton branch

This is the thin, callback-free entry point for §17 Case 2.  Structural
remainder selection remains in the existing dispatcher; the two mathematical
leaves are the preferred Case 1 endpoint and the low-fallback Case 2 engine.
-/

lemma exists_mutation_le_no_pair_rank_two_single_complete
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ h : Gene, 0 < X.1.1 h → Y.1.1 h ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ h : Gene, 0 < X.1.1 h → g.rank ≤ h.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized) (hg_rank : g.rank = 2)
    (hg_one : X.1.1 g = 1) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  apply exists_mutation_le_no_pair_rank_two_single_of_rank_ge_four
    X Y hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_one
  · intro hneg_zero restAfterG hrestAfterG _hg_one hrest_zero hXeq
      hm0 hsigX hX3
    exact exists_mutation_le_no_pair_rank_two_single_empty X Y hXY h17_1
      g hgX hgmin hg_pol hg_rank hneg_zero restAfterG hrestAfterG hg_one
        hrest_zero hXeq hm0 hsigX hX3
  · intro _hneg_zero restAfterG hrestAfterG _hg_one _hrest_ne g₂
      _hg₂_rest hg₂min hXg₂ _hg₂_rank_ge hg₂_pol _hg₂_ne_neg q₂ hg₂_rank
    have hne : g ≠ g₂ := by
      intro heq
      rw [← heq, hg_rank] at hg₂_rank
      omega
    have h2nd : ∀ h ∈ (X.1.1 - Finsupp.single g 1).support,
        2 * q₂ + 4 ≤ h.rank := by
      intro h hh
      have hrest_pos : 0 < restAfterG h := by
        rw [hrestAfterG]
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      have hle := hg₂min h hrest_pos
      rwa [hg₂_rank] at hle
    have hY1 := no_pair_rank_two_single_Y_prime_one_ne
      X Y hXY g hgX hgmin hg_rank
    have hr1 := h17_1 1 (by omega) hY1
    rcases no_pair_rank_two_single_level_one_split
        X Y hXY h17_1 g hgX hgmin hg_pol hg_rank with
      ⟨hg_pos, hsnd | hlow⟩ | ⟨hg_neg, hfst | hlow⟩
    · exact exists_mutation_le_no_pair_rank_two_single_preferred
        X Y hXY hcommon h17_1 hr1 hXpol hno_pair g g₂ hg_pol hg₂_pol
          hg_rank hg₂_rank hg_one hXg₂ hne h2nd (Or.inl ⟨hg_pos, hsnd⟩)
    · exact exists_mutation_le_no_pair_rank_two_single_low_fallback
        X Y hXY hcommon h17_1 hXpol hno_pair g hgX hgmin hg_pol
          hg_rank hg_one (Or.inl ⟨hg_pos, hlow.1, hlow.2⟩)
    · exact exists_mutation_le_no_pair_rank_two_single_preferred
        X Y hXY hcommon h17_1 hr1 hXpol hno_pair g g₂ hg_pol hg₂_pol
          hg_rank hg₂_rank hg_one hXg₂ hne h2nd (Or.inr ⟨hg_neg, hfst⟩)
    · exact exists_mutation_le_no_pair_rank_two_single_low_fallback
        X Y hXY hcommon h17_1 hXpol hno_pair g hgX hgmin hg_pol
          hg_rank hg_one (Or.inr ⟨hg_neg, hlow.1, hlow.2⟩)

end MixPi2Lambda
