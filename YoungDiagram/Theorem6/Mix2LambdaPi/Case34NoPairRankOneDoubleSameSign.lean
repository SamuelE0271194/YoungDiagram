import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- The remaining same-sign frontier in the rank-one-double no-pair branch.

The main dispatcher has already handled the Type10-ready doubled `g2` cases.
This lemma isolates the remaining singleton and same-component predecessor
fallbacks, keeping the large rank-one-double dispatcher from accumulating more
case-local proof code. -/
lemma rank_one_double_same_sign_remaining
    {m p q₂ : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_two : 2 ≤ X.1.1 g)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (restAfterDouble : Chromosome)
    (hrestAfterDouble_eq :
      restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (hrestAfterDouble_ne : restAfterDouble ≠ 0)
    (hrestAfterDouble_total :
      restAfterDouble.sum (fun _ n => n) + 2 = X.1.1.sum (fun _ n => n))
    (hg₂_rest : 0 < restAfterDouble g₂)
    (hg₂min : ∀ g' : Gene, 0 < restAfterDouble g' → g₂.rank ≤ g'.rank)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hsame : ¬ g₂ = g)
    (hg₂_rank_q : g₂.rank = 2 * q₂ + 3)
    (hopp : ¬ g₂.type = -g.type)
    (hg₂_same_type : g₂.type = g.type)
    (hXneg_g₂_zero : X.1.1 (-g₂) = 0)
    (hrestAfterDouble_g₂_eq_X : restAfterDouble g₂ = X.1.1 g₂)
    (hrestAfterDouble_neg_g₂_zero : restAfterDouble (-g₂) = 0)
    (htail_after_double_same :
      ∀ h ∈ restAfterDouble.support, 2 * q₂ + 3 ≤ h.rank)
    (hgap_middle_same :
      (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → ¬ Even j → j ≠ 1 →
        ((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) ∧
      (∀ j, 1 ≤ j → j ≤ 2 * q₂ + 3 → Even j →
        (signature (Gene.ofRank 1 g.type) +
              signature (Gene.ofRank 1 g.type)) +
            signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)))
    (hgap_pred_even_same :
      (signature (Gene.ofRank 1 g₂.type) +
            signature (Gene.ofRank 1 g₂.type)) +
          signature (Chromosome.prime^[2 * q₂ + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1))
    (hgap_succ_same_double :
      signature (Gene.ofRank 1 g₂.type) +
          signature (Chromosome.prime^[2 * q₂ + 4] X.1.1) ≤
        signature (Chromosome.prime^[2 * q₂ + 4] Y.1.1))
    (htype10_same_double_of_pred_gap :
      2 ≤ X.1.1 g₂ →
        (((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[2 * q₂ + 2] X.1.1) ≤
          signature (Gene.ofRank 1 g₂.type) +
            signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)) →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (hdouble_same_pred_or_done :
      2 ≤ X.1.1 g₂ →
        (∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∨
          (g₂.type = GeneType.Positive ∧
            (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1) ∨
          (g₂.type = GeneType.Negative ∧
            (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2)) :
    (X.1.1 g₂ = 1 →
      ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∧
    (2 ≤ X.1.1 g₂ → g₂.type = GeneType.Positive →
      (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).1 <
        (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).1 →
      ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∧
    (2 ≤ X.1.1 g₂ → g₂.type = GeneType.Negative →
      (signature (Chromosome.prime^[2 * q₂ + 2] X.1.1)).2 <
        (signature (Chromosome.prime^[2 * q₂ + 2] Y.1.1)).2 →
      ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) := by
  sorry

end Mix2LambdaPi

