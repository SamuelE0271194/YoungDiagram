import YoungDiagram.Chromosome
import YoungDiagram.Variety
import YoungDiagram.Mutations
import YoungDiagram.SigmaAux_Claude
import YoungDiagram.Sigma_Claude

open Chromosome Variety

/--
`Pi_n n` is the set of elements of `Π` (the polarized variety) with rank equal to `n`.
This corresponds to `Π(n)` in the paper.
-/
def Pi_n (n : ℕ) : Set Variety.Pi := { X | X.val.rank = n }

lemma rank_0 (X : Chromosome) (h : X.rank = 0) : X = 0 := by
  simp [Chromosome.rank, Finsupp.sum] at h
  have h' : ∀ a ∈ X.support, 1 ≤ a.rank := by
    intro a h''
    exact a.rank_pos
  apply Finsupp.ext
  intro a
  simp
  simp_all

/--
Proposition after (15.7) [Djoković 1982, p. 29]:
Let X, Y ∈ Π(n) with X < Y.  Then there exists a Π-mutation X → Z such that Z ≤ Y.

Here:
- `Π(n)` is the set of polarized chromosomes of rank `n`
- `X < Y` is the pointwise (Finsupp) strict order on chromosomes
- `Variety.Pi.Step X Z` witnesses a single Π-mutation from X to Z
- `Z ≤ Y` is the pointwise order on `Variety.Pi`
-/
theorem exists_mutation_le (n : ℕ) (X Y : Variety.Pi)
    (hX : X ∈ Pi_n n) (hY : Y ∈ Pi_n n)
    (hXY : X < Y) :
    ∃ Z : Variety.Pi, Variety.Pi.Step X Z ∧ Z ≤ Y := by
  induction n generalizing X Y with
  | zero =>
    -- Both X and Y have rank 0.  Since rank is a sum of positive gene ranks,
    -- rank 0 forces the chromosome to be 0, so X = 0 = Y, contradicting X < Y.
    exfalso
    have hX0 : X.val = 0 := rank_0 X.val hX
    have hY0 : Y.val = 0 := rank_0 Y.val hY
    have : X = Y := by
      ext1
      rw [hX0, hY0]
    exact absurd this (ne_of_lt hXY)
  | succ n ih =>
    cases n with
    | zero =>
      -- X, Y ∈ Π(1): every element is a single polarized gene of rank 1.
      -- Decide whether X and Y share a common gene.
      by_cases hcommon :
          ∃ g : Gene, 0 < X.val g ∧ 0 < Y.val g
      · -- Case 1: shared gene g.
        obtain ⟨g, hgX, hgY⟩ := hcommon
        sorry
      · -- Case 2: disjoint supports.
        push_neg at hcommon
        sorry
    | succ m =>
      -- X, Y ∈ Π(m+2): the full inductive step with IH available at rank m+1.
      -- Decide whether X and Y share a common gene.
      by_cases hcommon :
          ∃ g : Gene, 0 < X.val g ∧ 0 < Y.val g
      · -- Case 1: shared gene g.
        -- Subtract one copy of g from both, apply ih at rank m+1, reattach g.
        obtain ⟨g, hgX, hgY⟩ := hcommon
        sorry
      · -- Case 2: disjoint supports.
        -- Direct primitive mutation from X to some Z ≤ Y.
        push_neg at hcommon
        sorry
