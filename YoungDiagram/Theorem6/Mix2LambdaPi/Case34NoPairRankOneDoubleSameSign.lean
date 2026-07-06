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
  -- All three conclusions have the same unconditional consequent
  -- `∃ Z, Step X.1 Z ∧ Z ≤ Y.1`, so it suffices to produce one reducing step.
  suffices hstep : ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 by
    exact ⟨fun _ => hstep, fun _ _ _ => hstep, fun _ _ _ => hstep⟩
  have hXPi : X.1.1 ∈ Variety.Pi := Variety.mem_Pi_iff.mpr hXpol
  -- Level 1 is odd, so its two signature components agree (Label 3 symmetry).
  have ha1b1 : (signature (Chromosome.prime^[1] X.1.1)).1
             = (signature (Chromosome.prime^[1] X.1.1)).2 :=
    Mix2LambdaSection17.signature_prime_iterate_odd_eq_components_L3 X.1.2 (by decide)
  -- Case 3 (§17) dichotomy: does `X` carry opposite-sign (negative-count) mass?
  -- `neg_gene_of_b0_gt_a1` extracts an opposite-sign gene `g⁻(k)` (k ≠ 1 by
  -- `hno_pair`, so k ≥ 3) exactly when `a₁ < b₀`; that gene pairs with the
  -- rank-one source `g` to feed the opposite-sign Type16/Type14 boundary.
  by_cases hb0a1 : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma X.1.1 0).2
  · obtain ⟨gneg, hgneg_type, hgneg_pos⟩ :=
      Sigma.neg_gene_of_b0_gt_a1 X.1.1 hXPi hb0a1
    have hgneg_rank_ge : g.rank ≤ gneg.rank := hgmin gneg hgneg_pos
    -- Opposite-sign tail gene present: use the (already-proven) Type16/Type14
    -- opposite-sign boundary machinery anchored at `gneg.rank`, mirroring the
    -- opposite-sign branch of `rank_one_double_same_gene_tail_cases`.
    sorry
  · -- No opposite-sign mass: `b₀ ≤ a₁`, so (via `b₀ - a₁ = neg-count`) `X` has no
    -- negative gene, i.e. `X` is all-positive.  This configuration is vacuous:
    -- level 1 is odd, so `a₁ = b₁`; level-0 dominance forces `b₀ = d₀`; and `sigma`
    -- is antitone, so `d₁ ≤ d₀`.  Chaining
    --   `b₁ = a₁ ≥ b₀ = d₀ ≥ d₁ > b₁`   (the last strict step is `hseed1.2`)
    -- gives `b₁ < b₁`, a contradiction.
    exfalso
    have hB0A1 : (signature X.1.1).2 ≤ (signature (Chromosome.prime^[1] X.1.1)).1 :=
      not_lt.mp hb0a1
    have hle0 := le_iff_dominates.mp hXY.le 0
    simp only [Function.iterate_zero, id_eq] at hle0
    have hsum : (signature X.1.1).1 + (signature X.1.1).2 =
        (signature Y.1.1).1 + (signature Y.1.1).2 := by
      rw [signature_sum_eq_rank, signature_sum_eq_rank, X.2, Y.2]
    have hB0D0 : (signature X.1.1).2 = (signature Y.1.1).2 :=
      le_antisymm hle0.2 (by linarith [hle0.1])
    have hD1D0 : (signature (Chromosome.prime^[1] Y.1.1)).2 ≤ (signature Y.1.1).2 :=
      ((signature_prime_le Y.1.1).trans inf_le_left).2
    linarith [hseed1.2, ha1b1, hB0A1, hB0D0, hD1D0]

end Mix2LambdaPi

