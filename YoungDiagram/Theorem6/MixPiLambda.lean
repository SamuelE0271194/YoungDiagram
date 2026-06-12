import YoungDiagram.Theorem6.MixPiLambda.Case1
import YoungDiagram.Theorem6.MixPiLambda.Case3

open Variety hiding prime prime_def
open Chromosome Sigma

namespace MixPiLambda

/-- Rank-0 elements of `Mix (Pi, Lambda)` are all zero, so `X < Y` is absurd. -/
lemma exists_mutation_le_rank_zero {X Y : nMixPiLambda 0} (hXY : X < Y) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_zero X.2).trans (rank_zero Y.2).symm) (ne_of_lt hXY)

/-- Any rank-one element of `Mix (Pi, Lambda)` is `Gene.ofRank 1 .NonPolarized`:
its odd part equals itself and must lie in `Lambda`, forcing the gene to be
non-polarized. -/
private lemma rank_one_eq_of_mem {X : Chromosome}
    (hX : X ∈ Mix (Pi, Lambda)) (hr : X.rank = 1) :
    X = Gene.ofRank 1 .NonPolarized := by
  obtain ⟨ε, hε⟩ := rank_one hr
  have hodd : X.oddPart = X := by rw [hε, oddPart_ofRank]; simp
  have hNP : X.IsNonPolarized := by
    rw [← hodd]
    exact mem_Lambda_iff.mp (mem_Mix_iff.mp hX).2
  have : ε = .NonPolarized := by
    rw [hε] at hNP
    exact (IsNonPolarized_ofRank le_rfl).mp hNP
  rw [hε, this]

/-- Rank-1 case: `X < Y` is impossible because every rank-1 element of
`Mix (Pi, Lambda)` equals the unique non-polarized rank-1 chromosome. -/
lemma exists_mutation_le_rank_one {X Y : nMixPiLambda 1} (hXY : X < Y) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 :=
  absurd ((rank_one_eq_of_mem X.1.2 X.2).trans (rank_one_eq_of_mem Y.1.2 Y.2).symm)
    (ne_of_lt hXY)

/--
Theorem 6 of [Djoković 1982] for `Mix (Pi, Lambda)` (Label 2).
Given `X < Y` of equal rank in `Mix (Pi, Lambda)`, there exists a
`MixPiLambda.Step` from `X` to some `Z ≤ Y`.

Base cases (rank 0, 1), the shared-gene sub-case, and the disjoint pair sub-case
are proved here. The remaining sub-cases for rank ≥ 2 are sorried.
-/
theorem exists_mutation_le {n : ℕ} : ∀ (X Y : nMixPiLambda n), X < Y →
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X Z ∧ Z ≤ Y :=
  Nat.strongRecOn n fun n ih X Y hXY ↦
  match n with
  | 0 => exists_mutation_le_rank_zero hXY
  | 1 => exists_mutation_le_rank_one hXY
  | m + 2 => by
    by_cases hcommon : ∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g
    · exact exists_mutation_le_shared_gene m ih X Y hXY hcommon
    · by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
        Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k
      · sorry  -- Case2 (sigma equal)
      · by_cases hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
          g.type = .Positive ∧ h.type = .Negative ∧
          0 < X.1.1 g ∧ 0 < X.1.1 h
        · exact exists_mutation_le_disjoint_pair X Y hXY hcommon hsigeq hXpn
        · sorry  -- Case4 (§15.10)

end MixPiLambda
