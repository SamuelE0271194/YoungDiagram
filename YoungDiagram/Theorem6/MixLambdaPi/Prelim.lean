import YoungDiagram.Lifting.MixLambdaPi

open Variety hiding prime prime_def
open Chromosome

abbrev nMixLambdaPi (n : ℕ) := {X : Mix (Lambda, Pi) // X.1.rank = n}

namespace MixLambdaPi

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

/-- For `X ∈ Mix (Lambda, Pi)` with `0 < X g`, the gene `g` has the right
polarization for `single g 1` to lie in `Mix (Lambda, Pi)`. -/
lemma single_mem_Mix_Lambda_Pi {X : Chromosome} {g : Gene}
    (hX : X ∈ Mix (Lambda, Pi)) (hgX : 0 < X g) :
    (Finsupp.single g 1 : Chromosome) ∈ Mix (Lambda, Pi) := by
  refine ⟨?_, ?_⟩
  · rw [mem_Lambda_iff, evenPart_single]
    by_cases hgrank : Even g.rank
    · rw [if_pos hgrank, IsNonPolarized_single Nat.one_ne_zero]
      apply IsNonPolarized_def'.mp (mem_Lambda_iff.mp hX.1) g
      rw [Finsupp.mem_support_iff, evenPart_eq, Finsupp.filter_apply, if_pos hgrank]
      exact Nat.pos_iff_ne_zero.mp hgX
    · rw [if_neg hgrank]
      exact IsNonPolarized_zero
  · rw [mem_Pi_iff, oddPart_single]
    by_cases hgrank : Even g.rank
    · rw [if_pos hgrank]
      exact IsPolarized_zero
    · rw [if_neg hgrank, IsPolarized_single Nat.one_ne_zero]
      apply IsPolarized_def'.mp (mem_Pi_iff.mp hX.2) g
      rw [Finsupp.mem_support_iff, oddPart_eq, Finsupp.filter_apply,
        if_pos (Nat.not_even_iff_odd.mp hgrank)]
      exact Nat.pos_iff_ne_zero.mp hgX

/-- `Mix (Lambda, Pi)` is closed under (truncated) subtraction. -/
lemma sub_mem_Mix_Lambda_Pi {X : Chromosome} (Y : Chromosome)
    (hX : X ∈ Mix (Lambda, Pi)) : X - Y ∈ Mix (Lambda, Pi) := by
  refine ⟨?_, ?_⟩
  · rw [evenPart_sub, mem_Lambda_iff]
    exact IsFiltered_sub Y.evenPart (mem_Lambda_iff.mp hX.1)
  · rw [oddPart_sub]
    exact IsPolarized_sub Y.oddPart hX.2

end MixLambdaPi
