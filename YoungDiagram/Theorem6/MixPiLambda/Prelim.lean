import YoungDiagram.Sigma
import YoungDiagram.Lifting.MixPiLambda

open Variety hiding prime prime_def
open Chromosome

/-- Elements of `Mix (Pi, Lambda)` with rank exactly `n`. -/
abbrev nMixPiLambda (n : ℕ) := {X : Mix (Pi, Lambda) // X.1.rank = n}

namespace MixPiLambda

/-- The filter of a (tsub) difference is the difference of filters. -/
private lemma filter_sub_eq {X Y : Chromosome} {p : Gene → Prop} [DecidablePred p] :
    (X - Y).filter p = X.filter p - Y.filter p := by
  ext g
  simp only [Finsupp.filter_apply, Finsupp.tsub_apply]
  split_ifs <;> simp

/-- `evenPart` commutes with subtraction. -/
private lemma evenPart_sub (X Y : Chromosome) :
    (X - Y).evenPart = X.evenPart - Y.evenPart := filter_sub_eq

/-- `oddPart` commutes with subtraction. -/
private lemma oddPart_sub (X Y : Chromosome) :
    (X - Y).oddPart = X.oddPart - Y.oddPart := filter_sub_eq

/-- For `X ∈ Mix (Pi, Lambda)` with `0 < X g`, the gene `g` has the right
polarization for `single g 1` to lie in `Mix (Pi, Lambda)`. -/
lemma single_mem_Mix_Pi_Lambda {X : Chromosome} {g : Gene}
    (hX : X ∈ Mix (Pi, Lambda)) (hgX : 0 < X g) :
    (Finsupp.single g 1 : Chromosome) ∈ Mix (Pi, Lambda) := by
  refine ⟨?_, ?_⟩
  · rw [mem_Pi_iff, evenPart_single]
    by_cases hgrank : Even g.rank
    · rw [if_pos hgrank, IsPolarized_single Nat.one_ne_zero]
      apply IsPolarized_def'.mp (mem_Pi_iff.mp hX.1) g
      rw [Finsupp.mem_support_iff, evenPart_eq, Finsupp.filter_apply, if_pos hgrank]
      exact Nat.pos_iff_ne_zero.mp hgX
    · rw [if_neg hgrank]
      exact IsPolarized_zero
  · rw [mem_Lambda_iff, oddPart_single]
    by_cases hgrank : Even g.rank
    · rw [if_pos hgrank]
      exact IsNonPolarized_zero
    · rw [if_neg hgrank, IsNonPolarized_single Nat.one_ne_zero]
      apply IsNonPolarized_def'.mp (mem_Lambda_iff.mp hX.2) g
      rw [Finsupp.mem_support_iff, oddPart_eq, Finsupp.filter_apply,
        if_pos (Nat.not_even_iff_odd.mp hgrank)]
      exact Nat.pos_iff_ne_zero.mp hgX

/-- `Mix (Pi, Lambda)` is closed under (truncated) subtraction. -/
lemma sub_mem_Mix_Pi_Lambda {X : Chromosome} (Y : Chromosome)
    (hX : X ∈ Mix (Pi, Lambda)) : X - Y ∈ Mix (Pi, Lambda) := by
  refine ⟨?_, ?_⟩
  · rw [evenPart_sub]
    exact IsPolarized_sub Y.evenPart hX.1
  · rw [oddPart_sub, mem_Lambda_iff]
    exact IsFiltered_sub Y.oddPart (mem_Lambda_iff.mp hX.2)

end MixPiLambda
