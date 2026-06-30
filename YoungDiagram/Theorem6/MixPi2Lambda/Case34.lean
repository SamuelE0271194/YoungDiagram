import YoungDiagram.Theorem6.MixPi2Lambda.Type13

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

private lemma prime_iterate_rank_lt_of_sigma_ne
    {X Y : Chromosome} (hXY : X ≤ Y) {k : ℕ}
    (hne : Sigma.sigma X k ≠ Sigma.sigma Y k) :
    (Chromosome.prime^[k] X).rank < (Chromosome.prime^[k] Y).rank := by
  have hle := le_iff_dominates.mp hXY k
  change Sigma.sigma X k ≤ Sigma.sigma Y k at hle
  have hstrict :
      (Sigma.sigma X k).1 < (Sigma.sigma Y k).1 ∨
      (Sigma.sigma X k).2 < (Sigma.sigma Y k).2 := by
    by_cases hfst : (Sigma.sigma X k).1 = (Sigma.sigma Y k).1
    · right
      exact lt_of_le_of_ne hle.2 fun hsnd => hne (Prod.ext hfst hsnd)
    · left
      exact lt_of_le_of_ne hle.1 hfst
  have hsum :
      (Sigma.sigma X k).1 + (Sigma.sigma X k).2 <
      (Sigma.sigma Y k).1 + (Sigma.sigma Y k).2 := by
    rcases hstrict with h | h <;> linarith [hle.1, hle.2]
  simp only [Sigma.sigma, signature_sum_eq_rank] at hsum
  exact_mod_cast hsum

/-- Remaining polarized cases after the diagonal type13 branch. -/
private lemma exists_mutation_le_polarized_remaining (m : ℕ)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hnodouble : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      2 ≤ X.1.1 gpos ∧ 2 ≤ X.1.1 gneg) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  sorry

/-! ## Section 17 core after the induction and lifting reductions

The joint Label 3/4 induction first removes common genes and handles every
positive level at which the two sigma columns agree.  Consequently this file
starts precisely from condition (17.1) of Djoković.  The remaining proof is
the type9--type17 classification from §17. -/

/-- The primitive-classification core of §17 for `Mix (Pi, 2 • Lambda)`. -/
lemma exists_mutation_le_reduced (m : ℕ)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬ ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬ ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank := by
    intro k hkpos hYkne
    apply prime_iterate_rank_lt_of_sigma_ne hXY.le
    intro hsig
    exact hsigeq ⟨k, hkpos, hYkne, hsig⟩
  push Not at hcommon
  by_cases hNP : ∃ g : Gene, 0 < X.1.1 g ∧ g.type = .NonPolarized
  · obtain ⟨g, hXg, hgNP⟩ := hNP
    exact exists_mutation_le_of_nonpolarized X Y hXY hcommon h17_1 g hXg hgNP
  · push Not at hNP
    -- From here on `X` is polarized; this is the remaining type10--type17
    -- classification in §17.
    have hXpol : X.1.1.IsPolarized := by
      rw [IsPolarized_def']
      intro g hg
      exact hNP g (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg))
    by_cases hdouble : ∃ (gpos gneg : Gene),
        gpos.rank = gneg.rank ∧
        gpos.type = .Positive ∧ gneg.type = .Negative ∧
        2 ≤ X.1.1 gpos ∧ 2 ≤ X.1.1 gneg
    · obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXpos2, hXneg2⟩ := hdouble
      exact exists_mutation_le_of_double_pair X Y hXY hcommon h17_1
        gpos gneg hrank hgpos hgneg hXpos2 hXneg2
    · exact exists_mutation_le_polarized_remaining m X Y hXY hcommon h17_1
        hXpol hdouble

end MixPi2Lambda
