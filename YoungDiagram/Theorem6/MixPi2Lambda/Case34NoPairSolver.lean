import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairDispatcher
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankGeFourSolver
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoSingleComplete
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleRest
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleEmpty
import YoungDiagram.Theorem6.MixPi2Lambda.Case34NoPairRankTwoDoubleFallback

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-! # Label 4 no-pair solver (assembled)

Hypothesis-free assembly of the §17 no-pair branch for `Mix (Pi, 2 • Lambda)`:
the minimal polarized gene has rank `2` (single/double) or `≥ 4` (window solver).
The rank-`2` single case is closed by `single_complete`; the rank-`≥4` case by
`exists_mutation_le_no_pair_rank_ge_four` (with `p := q+1`); the rank-`2` double
case is closed via `double_of_rank_split` with `double_empty` supplied and the
two nonempty double leaves sharing the multiplicity-agnostic Case 2 fallback
solver. -/

private lemma exists_mutation_le_no_pair_rank_two_double_preferred
    {m : ℕ} (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g : Gene) (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ GeneType.NonPolarized)
    (hg_rank : g.rank = 2) (hg_two : 2 ≤ X.1.1 g)
    (hpreferred :
      (g.type = GeneType.Positive ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) ∨
      (g.type = GeneType.Negative ∧
        (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hY1 := no_pair_rank_two_single_Y_prime_one_ne
    X Y hXY g hgX hgmin hg_rank
  have hr1 := h17_1 1 (by omega) hY1
  have hmin_rank : ∀ h ∈ X.1.1.support, 2 ≤ h.rank := by
    intro h hh
    have hle := hgmin h (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh))
    omega
  have hWtop : ∀ z ∈ X.1.1.support,
      2 ≤ z.rank ∧ (z.rank = 2 → z.type = g.type) := by
    intro z hz
    have hzX := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz)
    refine ⟨hmin_rank z hz, ?_⟩
    intro hzrank
    have hzpol := IsPolarized_def'.mp hXpol z hz
    have hrank : z.rank = g.rank := by omega
    cases hzg : z.type <;> cases hgg : g.type
    · exact False.elim (hzpol hzg)
    · exact False.elim (hzpol hzg)
    · exact False.elim (hzpol hzg)
    · exact False.elim (hg_pol hgg)
    · rfl
    · exact False.elim (hno_pair ⟨z, g, hrank, hzg, hgg, hzX, hgX⟩)
    · exact False.elim (hg_pol hgg)
    · exact False.elim (hno_pair ⟨g, z, hrank.symm, hgg, hzg, hgX, hzX⟩)
    · rfl
  have hD := totalMult_cast_eq_sigma_zero_sub_sigma_one X.1.1
  have hgap_pred := no_pair_rank_two_single_preferred_type10_pred_gap
    X Y hXY g hpreferred
  cases htype : g.type with
  | NonPolarized => exact False.elim (hg_pol htype)
  | Positive =>
      have hWpos : ∀ z ∈ X.1.1.support,
          2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Positive) := by
        intro z hz
        exact ⟨(hWtop z hz).1, fun hzrank => by
          rw [(hWtop z hz).2 hzrank, htype]⟩
      have hXdrop := edge_drop_fst_eq_totalMult_positive_iterate
        (W := X.1.1) (i := 0) hWpos
      simp only [Function.iterate_zero, id_eq] at hXdrop
      rw [hD] at hXdrop
      have hdom := (le_iff_dominates.mp hXY.le 1).1
      have hsucc := seed_fst_lt_odd X Y hr1 (i := 1) (by decide)
        (by simpa [Sigma.sigma] using hXdrop) hdom
      have hsucc' :
          (signature (Chromosome.prime^[3] X.1.1)).1 <
            (signature (Chromosome.prime^[3] Y.1.1)).1 := by
        simpa [Sigma.sigma] using hsucc
      have hY3 : Chromosome.prime^[3] Y.1.1 ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hsucc'
        exact (not_lt_of_ge
          (signature_nonneg (Chromosome.prime^[3] X.1.1)).1) hsucc'
      have hY2 := Chromosome.prime_iterate_ne_zero_if_prime_ne
        (j := 2) (k := 3) (by omega) hY3
      have hZle := type10_double_target_add_rest_le_of_gaps
        (q := 0) (by decide : GeneType.Positive ≠ .NonPolarized)
        X Y hXY g htype (by omega) hg_two (by simpa [htype] using hgap_pred)
        (by
          intro j hjlo hjhi
          have : j = 2 := by omega
          subst j
          exact type10_mid_gap_even_of_Y_ne X Y h17_1 ⟨1, by omega⟩
            (by omega) hY2)
        (type10_succ_gap_positive (q := 0) X Y hXY hsucc')
      exact exists_mutation_le_type10_of_double (by decide) X Y g htype
        (by omega) hg_two hZle
  | Negative =>
      have hWneg : ∀ z ∈ X.1.1.support,
          2 ≤ z.rank ∧ (z.rank = 2 → z.type = GeneType.Negative) := by
        intro z hz
        exact ⟨(hWtop z hz).1, fun hzrank => by
          rw [(hWtop z hz).2 hzrank, htype]⟩
      have hXdrop := edge_drop_snd_eq_totalMult_negative_iterate
        (W := X.1.1) (i := 0) hWneg
      simp only [Function.iterate_zero, id_eq] at hXdrop
      rw [hD] at hXdrop
      have hdom := (le_iff_dominates.mp hXY.le 1).2
      have hsucc := seed_snd_lt_odd X Y hr1 (i := 1) (by decide)
        (by simpa [Sigma.sigma] using hXdrop) hdom
      have hsucc' :
          (signature (Chromosome.prime^[3] X.1.1)).2 <
            (signature (Chromosome.prime^[3] Y.1.1)).2 := by
        simpa [Sigma.sigma] using hsucc
      have hY3 : Chromosome.prime^[3] Y.1.1 ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hsucc'
        exact (not_lt_of_ge
          (signature_nonneg (Chromosome.prime^[3] X.1.1)).2) hsucc'
      have hY2 := Chromosome.prime_iterate_ne_zero_if_prime_ne
        (j := 2) (k := 3) (by omega) hY3
      have hZle := type10_double_target_add_rest_le_of_gaps
        (q := 0) (by decide : GeneType.Negative ≠ .NonPolarized)
        X Y hXY g htype (by omega) hg_two (by simpa [htype] using hgap_pred)
        (by
          intro j hjlo hjhi
          have : j = 2 := by omega
          subst j
          exact type10_mid_gap_even_of_Y_ne X Y h17_1 ⟨1, by omega⟩
            (by omega) hY2)
        (type10_succ_gap_negative (q := 0) X Y hXY hsucc')
      exact exists_mutation_le_type10_of_double (by decide) X Y g htype
        (by omega) hg_two hZle

set_option maxHeartbeats 800000 in
-- The assembled dispatcher elaborates all rank and multiplicity branches at once.
lemma exists_mutation_le_no_pair (m : ℕ)
    (X Y : nMixPi2Lambda (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  refine exists_mutation_le_no_pair_of_rank_branches m X Y hXY hcommon h17_1
    hXpol hno_pair ?_ ?_
  · -- minimal polarized gene of rank 2
    intro g hgX hgmin hg_pol hg_rank
    by_cases hg_two : 2 ≤ X.1.1 g
    · -- rank-2 double case
      refine exists_mutation_le_no_pair_rank_two_double_of_rank_split
        X Y hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_two
        (fun hneg restD hrestD hrest_zero hXeq hm2 hsigX hX3 =>
          exists_mutation_le_no_pair_rank_two_double_empty X Y hXY h17_1 g hgX
            hgmin hg_pol hg_rank hneg restD hrestD hrest_zero hXeq hm2 hsigX hX3)
        ?_ ?_
      · -- second gene equals `g` (double same-gene) — remaining frontier
        intro _hneg _restD _hrestD _hrest_ne _g₂ _hg₂rest _hg₂min
          _hXg₂ _hg₂rank _hg₂pol _hg₂neg _hsame
        have hfallback :
            ((g.type = GeneType.Positive ∧
                ¬ (signature (Chromosome.prime^[1] X.1.1)).2 <
                  (signature (Chromosome.prime^[1] Y.1.1)).2 ∧
                (signature (Chromosome.prime^[1] X.1.1)).1 <
                  (signature (Chromosome.prime^[1] Y.1.1)).1) ∨
              (g.type = GeneType.Negative ∧
                ¬ (signature (Chromosome.prime^[1] X.1.1)).1 <
                  (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
                (signature (Chromosome.prime^[1] X.1.1)).2 <
                  (signature (Chromosome.prime^[1] Y.1.1)).2)) →
            ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
          intro hlow
          exact exists_mutation_le_no_pair_rank_two_copy_low_fallback
            X Y hXY hcommon h17_1 hXpol hno_pair g hgX hgmin hg_pol
              hg_rank (by omega) hlow
        rcases no_pair_rank_two_single_level_one_split X Y hXY h17_1 g hgX
            hgmin hg_pol hg_rank with
          ⟨hg_pos, hsnd | ⟨hnsnd, hfst⟩⟩ |
          ⟨hg_neg, hfst | ⟨hnfst, hsnd⟩⟩
        · exact exists_mutation_le_no_pair_rank_two_double_preferred
            X Y hXY h17_1 hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_two
            (Or.inl ⟨hg_pos, hsnd⟩)
        · exact hfallback (Or.inl ⟨hg_pos, hnsnd, hfst⟩)
        · exact exists_mutation_le_no_pair_rank_two_double_preferred
            X Y hXY h17_1 hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_two
            (Or.inr ⟨hg_neg, hfst⟩)
        · exact hfallback (Or.inr ⟨hg_neg, hnfst, hsnd⟩)
      · -- second gene distinct of rank `2*q₂+4` — remaining frontier
        intro _hneg _restD _hrestD _hrest_ne _g₂ _hg₂rest _hg₂min
          _hXg₂ _hg₂rank _hg₂pol _hg₂neg q₂ _hg₂rankq
        have hfallback :
            ((g.type = GeneType.Positive ∧
                ¬ (signature (Chromosome.prime^[1] X.1.1)).2 <
                  (signature (Chromosome.prime^[1] Y.1.1)).2 ∧
                (signature (Chromosome.prime^[1] X.1.1)).1 <
                  (signature (Chromosome.prime^[1] Y.1.1)).1) ∨
              (g.type = GeneType.Negative ∧
                ¬ (signature (Chromosome.prime^[1] X.1.1)).1 <
                  (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
                (signature (Chromosome.prime^[1] X.1.1)).2 <
                  (signature (Chromosome.prime^[1] Y.1.1)).2)) →
            ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
          intro hlow
          exact exists_mutation_le_no_pair_rank_two_copy_low_fallback
            X Y hXY hcommon h17_1 hXpol hno_pair g hgX hgmin hg_pol
              hg_rank (by omega) hlow
        rcases no_pair_rank_two_single_level_one_split X Y hXY h17_1 g hgX
            hgmin hg_pol hg_rank with
          ⟨hg_pos, hsnd | ⟨hnsnd, hfst⟩⟩ |
          ⟨hg_neg, hfst | ⟨hnfst, hsnd⟩⟩
        · exact exists_mutation_le_no_pair_rank_two_double_preferred
            X Y hXY h17_1 hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_two
            (Or.inl ⟨hg_pos, hsnd⟩)
        · exact hfallback (Or.inl ⟨hg_pos, hnsnd, hfst⟩)
        · exact exists_mutation_le_no_pair_rank_two_double_preferred
            X Y hXY h17_1 hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_two
            (Or.inr ⟨hg_neg, hfst⟩)
        · exact hfallback (Or.inr ⟨hg_neg, hnfst, hsnd⟩)
    · -- rank-2 single case
      have hg_one : X.1.1 g = 1 := by omega
      exact exists_mutation_le_no_pair_rank_two_single_complete X Y hXY hcommon
        h17_1 hXpol hno_pair g hgX hgmin hg_pol hg_rank hg_one
  · -- minimal polarized gene of rank ≥ 4
    intro g q hgX hgmin hg_pol hg_rank hmin_rank hX1 hY1 hr1
    have hXne : X.1.1 ≠ 0 := fun h => by simp [h] at hgX
    exact exists_mutation_le_no_pair_rank_ge_four X Y hXY hcommon h17_1 hXpol
      hno_pair hXne g hgX hgmin hg_pol (show g.rank = 2 * (q + 1) + 2 by omega)
      (by omega)

end MixPi2Lambda
