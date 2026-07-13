import YoungDiagram.Theorem6.MixPi2Lambda.Type15

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace MixPi2Lambda

/-!
# Rank-two Type17 boundary profile

For `m = 0`, Type17 and Type15 have the same target-source signature delta
through the later source rank.  Type17 then vanishes instead of carrying the
final Type15 successor cell.  This module packages that relation without
introducing an import cycle between the two mutation modules.
-/

/-- Up to the later source rank, rank-two Type17 and Type15 have equal
target-source signature deltas. -/
lemma type17_rank_two_delta_eq_type15
    {n j : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (hj : j ≤ 2 * n + 2) :
    signature (Chromosome.prime^[j] (Y17 (Nat.zero_le n) hε).1) +
        signature (Chromosome.prime^[j] (X15 (Nat.zero_le n) hε).1) =
      signature (Chromosome.prime^[j] (X17 (Nat.zero_le n) hε).1) +
        signature (Chromosome.prime^[j] (Y15 (Nat.zero_le n) hε).1) := by
  let r := 2 * n + 2 - j
  have hr_top : 2 * n + 2 - j = r := rfl
  have hr_top1 : 2 * n + 3 - j = r + 1 := by
    dsimp [r]
    omega
  have hr_top2 : 2 * n + 4 - j = r + 2 := by
    dsimp [r]
    omega
  have hpair := signature_ofRank_succ_add_pred_neg
    (ε := ε) (m := r + 1) (n := r + 1) (by omega)
    (show Even ((r + 1) + (r + 1)) by exact ⟨r + 1, by omega⟩)
  have hpair' :
      signature (Gene.ofRank (r + 2) ε) +
          signature (Gene.ofRank r (-ε)) =
        signature (Gene.ofRank (r + 1) GeneType.NonPolarized) +
          signature (Gene.ofRank (r + 1) GeneType.NonPolarized) := by
    simpa using hpair
  simp only [X17_eq, Y17_eq, X15_eq, Y15_eq, iterate_map_add,
    prime_iterate_ofRank, map_add]
  rw [hr_top, hr_top1, hr_top2]
  have hzero : 2 * 0 - j = 0 := by omega
  have hlow : 2 * 0 + 2 - j = 2 - j := by omega
  rw [hzero, hlow, Gene.ofRank_zero, map_zero, zero_add]
  rw [← hpair']
  abel

private lemma cancel_delta
    {A B C D : ℚ × ℚ} (h : A + B = C + (D + B)) : A = D + C := by
  apply add_right_cancel (b := B)
  calc
    A + B = C + (D + B) := h
    _ = (D + C) + B := by abel

/-- Lower odd transition profile for rank-two Type17. -/
lemma type17_rank_two_signature_pred
    {n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) :
    signature (Chromosome.prime^[1] (Y17 (Nat.zero_le n) hε).1) =
      signature (Gene.ofRank 1 ε) +
        signature (Chromosome.prime^[1] (X17 (Nat.zero_le n) hε).1) := by
  have hdelta := type17_rank_two_delta_eq_type15 (n := n) hε
    (j := 1) (by omega)
  rw [type15_signature_pred (Nat.zero_le n)] at hdelta
  exact cancel_delta hdelta

/-- Even middle levels of rank-two Type17 have `(1,1)` slack. -/
lemma type17_rank_two_signature_mid_even
    {n j : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (hjlo : 2 ≤ j) (hjhi : j ≤ 2 * n + 2) (heven : Even j) :
    signature (Chromosome.prime^[j] (Y17 (Nat.zero_le n) hε).1) =
      ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[j] (X17 (Nat.zero_le n) hε).1) := by
  have hdelta := type17_rank_two_delta_eq_type15 hε hjhi
  rw [type15_signature_mid_even (Nat.zero_le n) hjlo hjhi heven] at hdelta
  exact cancel_delta hdelta

/-- Positive odd middle levels of rank-two Type17 have two cells of first
component slack. -/
lemma type17_rank_two_signature_mid_odd_positive
    {n j : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (hjlo : 2 ≤ j) (hjhi : j ≤ 2 * n + 2) (hodd : ¬ Even j)
    (hεpos : ε = GeneType.Positive) :
    signature (Chromosome.prime^[j] (Y17 (Nat.zero_le n) hε).1) =
      ((2 : ℚ), (0 : ℚ)) +
        signature (Chromosome.prime^[j] (X17 (Nat.zero_le n) hε).1) := by
  have hdelta := type17_rank_two_delta_eq_type15 hε hjhi
  rw [type15_signature_mid_odd_positive (Nat.zero_le n) hjlo hjhi hodd hεpos]
    at hdelta
  exact cancel_delta hdelta

/-- Negative odd middle levels of rank-two Type17 have two cells of second
component slack. -/
lemma type17_rank_two_signature_mid_odd_negative
    {n j : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (hjlo : 2 ≤ j) (hjhi : j ≤ 2 * n + 2) (hodd : ¬ Even j)
    (hεneg : ε = GeneType.Negative) :
    signature (Chromosome.prime^[j] (Y17 (Nat.zero_le n) hε).1) =
      ((0 : ℚ), (2 : ℚ)) +
        signature (Chromosome.prime^[j] (X17 (Nat.zero_le n) hε).1) := by
  have hdelta := type17_rank_two_delta_eq_type15 hε hjhi
  rw [type15_signature_mid_odd_negative (Nat.zero_le n) hjlo hjhi hodd hεneg]
    at hdelta
  exact cancel_delta hdelta

/-- After the later source rank, rank-two Type17 source and target signatures
agree (both mutation-specific parts have vanished). -/
lemma type17_rank_two_signature_eq_after
    {n j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized}
    (hj : 2 * n + 3 ≤ j) :
    signature (Chromosome.prime^[j] (Y17 (Nat.zero_le n) hε).1) =
      signature (Chromosome.prime^[j] (X17 (Nat.zero_le n) hε).1) := by
  simp only [X17_eq, Y17_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have hlowX : 2 - j = 0 := by omega
  have hlowY : 0 - j = 0 := by omega
  have htopX : 2 * n + 2 - j = 0 := by omega
  have htopY : 2 * n + 3 - j = 0 := by omega
  simp [hlowX, hlowY, htopX, htopY]

/-- Dominance assembler for the rank-two (`m=0`) Type17 boundary.  Its middle
window is the same parity-sensitive window as Type15, but Type17 has no upper
successor cell and therefore no successor-gap obligation. -/
lemma type17_rank_two_target_add_rest_le_of_gaps
    {N n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1) (restval : Chromosome)
    (hXeq : (X17 (Nat.zero_le n) hε).1 + restval = X.1.1)
    (hgap_pred :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[1] X.1.1) ≤
        signature (Chromosome.prime^[1] Y.1.1))
    (hgap_mid_even : ∀ j, 2 ≤ j → j ≤ 2 * n + 2 → Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_mid_odd_positive :
      ε = GeneType.Positive →
        ∀ j, 2 ≤ j → j ≤ 2 * n + 2 → ¬ Even j →
          ((2 : ℚ), (0 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1))
    (hgap_mid_odd_negative :
      ε = GeneType.Negative →
        ∀ j, 2 ≤ j → j ≤ 2 * n + 2 → ¬ Even j →
          ((0 : ℚ), (2 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1)) :
    (Y17 (Nat.zero_le n) hε).1 + restval ≤ Y.1.1 := by
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp :
      signature (Chromosome.prime^[j] X.1.1) =
        signature (Chromosome.prime^[j] (X17 (Nat.zero_le n) hε).1) +
          signature (Chromosome.prime^[j] restval) := by
    conv_lhs => rw [← hXeq]
    rw [iterate_map_add, map_add]
  by_cases hj0 : j = 0
  · subst j
    have hsig0 :
        signature (Y17 (Nat.zero_le n) hε).1 =
          signature (X17 (Nat.zero_le n) hε).1 := by
      simpa [X17_eq, Y17_eq] using
        (mutation_type17_signature_eq (ε := ε) (m := 0)
          (n := n) (Nat.zero_le n)).symm
    have hdecomp0 :
        signature X.1.1 = signature (X17 (Nat.zero_le n) hε).1 +
          signature restval := by
      simpa only [Function.iterate_zero_apply] using hdecomp
    simp only [Function.iterate_zero_apply]
    rw [hsig0, ← hdecomp0]
    exact le_iff_dominates.mp hXY.le 0
  · by_cases hj1 : j = 1
    · subst j
      rw [type17_rank_two_signature_pred hε]
      calc
        signature (Gene.ofRank 1 ε) +
              signature (Chromosome.prime^[1] (X17 (Nat.zero_le n) hε).1) +
            signature (Chromosome.prime^[1] restval) =
          signature (Gene.ofRank 1 ε) +
            (signature (Chromosome.prime^[1] (X17 (Nat.zero_le n) hε).1) +
              signature (Chromosome.prime^[1] restval)) := by abel
        _ = signature (Gene.ofRank 1 ε) +
              signature (Chromosome.prime^[1] X.1.1) := by rw [← hdecomp]
        _ ≤ signature (Chromosome.prime^[1] Y.1.1) := hgap_pred
    · by_cases hjmid : j ≤ 2 * n + 2
      · have hjlo : 2 ≤ j := by omega
        by_cases heven : Even j
        · rw [type17_rank_two_signature_mid_even hε hjlo hjmid heven]
          calc
            ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[j]
                    (X17 (Nat.zero_le n) hε).1) +
                signature (Chromosome.prime^[j] restval) =
              ((1 : ℚ), (1 : ℚ)) +
                (signature (Chromosome.prime^[j]
                    (X17 (Nat.zero_le n) hε).1) +
                  signature (Chromosome.prime^[j] restval)) := by abel
            _ = ((1 : ℚ), (1 : ℚ)) +
                  signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
            _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
              hgap_mid_even j hjlo hjmid heven
        · by_cases hpos : ε = GeneType.Positive
          · rw [type17_rank_two_signature_mid_odd_positive hε hjlo hjmid
              heven hpos]
            calc
              ((2 : ℚ), (0 : ℚ)) +
                    signature (Chromosome.prime^[j]
                      (X17 (Nat.zero_le n) hε).1) +
                  signature (Chromosome.prime^[j] restval) =
                ((2 : ℚ), (0 : ℚ)) +
                  (signature (Chromosome.prime^[j]
                      (X17 (Nat.zero_le n) hε).1) +
                    signature (Chromosome.prime^[j] restval)) := by abel
              _ = ((2 : ℚ), (0 : ℚ)) +
                    signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
              _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
                hgap_mid_odd_positive hpos j hjlo hjmid heven
          · have hneg : ε = GeneType.Negative := by
              cases htype : ε with
              | NonPolarized => exact False.elim (hε htype)
              | Positive => exact False.elim (hpos htype)
              | Negative => rfl
            rw [type17_rank_two_signature_mid_odd_negative hε hjlo hjmid
              heven hneg]
            calc
              ((0 : ℚ), (2 : ℚ)) +
                    signature (Chromosome.prime^[j]
                      (X17 (Nat.zero_le n) hε).1) +
                  signature (Chromosome.prime^[j] restval) =
                ((0 : ℚ), (2 : ℚ)) +
                  (signature (Chromosome.prime^[j]
                      (X17 (Nat.zero_le n) hε).1) +
                    signature (Chromosome.prime^[j] restval)) := by abel
              _ = ((0 : ℚ), (2 : ℚ)) +
                    signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
              _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
                hgap_mid_odd_negative hneg j hjlo hjmid heven
      · have hjafter : 2 * n + 3 ≤ j := by omega
        rw [type17_rank_two_signature_eq_after hjafter, ← hdecomp]
        exact le_iff_dominates.mp hXY.le j

/-- Concrete-gene rank-two Type17 constructor using the pred/even/odd gap
interface. -/
lemma exists_mutation_le_type17_rank_two_of_genes_of_gaps
    {N n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (X Y : nMixPi2Lambda N) (hXY : X.1 < Y.1) (gε gnegε : Gene)
    (hgε : gε.type = ε) (hgnegε : gnegε.type = -ε)
    (hgε_rank : gε.rank = 2)
    (hgnegε_rank : gnegε.rank = 2 * n + 2)
    (hεcopy : 1 ≤ X.1.1 gε) (hnegεtwo : 2 ≤ X.1.1 gnegε)
    (hne : gε ≠ gnegε)
    (hgap_pred :
      signature (Gene.ofRank 1 ε) +
          signature (Chromosome.prime^[1] X.1.1) ≤
        signature (Chromosome.prime^[1] Y.1.1))
    (hgap_mid_even : ∀ j, 2 ≤ j → j ≤ 2 * n + 2 → Even j →
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1))
    (hgap_mid_odd_positive :
      ε = GeneType.Positive →
        ∀ j, 2 ≤ j → j ≤ 2 * n + 2 → ¬ Even j →
          ((2 : ℚ), (0 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1))
    (hgap_mid_odd_negative :
      ε = GeneType.Negative →
        ∀ j, 2 ≤ j → j ≤ 2 * n + 2 → ¬ Even j →
          ((0 : ℚ), (2 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1)) :
    ∃ Z : Mix (Pi, 2 • Lambda), MixPi2Lambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gnegε 1 - Finsupp.single gnegε 1 -
      Finsupp.single gε 1
  have hgε_eq :
      Gene.ofRank 2 ε = (Finsupp.single gε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gε)
    rwa [hgε_rank, hgε] at h
  have hgnegε_eq :
      Gene.ofRank (2 * n + 2) (-ε) =
        (Finsupp.single gnegε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gnegε)
    rwa [hgnegε_rank, hgnegε] at h
  have hX17val :
      (X17 (Nat.zero_le n) hε).1 =
        Finsupp.single gε 1 + Finsupp.single gnegε 1 +
          Finsupp.single gnegε 1 := by
    rw [X17_eq, hgε_eq, hgnegε_eq]
  have hXeq : (X17 (Nat.zero_le n) hε).1 + restval = X.1.1 := by
    rw [hX17val]
    exact Mix2LambdaSection17.single_double_pair_add_rest
      hnegεtwo hεcopy hne.symm
  have hZle := type17_rank_two_target_add_rest_le_of_gaps hε X Y hXY
    restval hXeq hgap_pred hgap_mid_even hgap_mid_odd_positive
    hgap_mid_odd_negative
  exact exists_mutation_le_type17_of_genes hε (Nat.zero_le n) X Y
    gε gnegε hgε hgnegε (by simpa using hgε_rank) hgnegε_rank
    hεcopy hnegεtwo hne hZle

end MixPi2Lambda
