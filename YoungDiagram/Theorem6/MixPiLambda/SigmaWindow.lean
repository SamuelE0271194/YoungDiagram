import YoungDiagram.Mutations.MixPiLambda

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-! ## §15.10 Case A `sigma`-windows for `Mix (Pi, Lambda)`.

Parity-mirror of `MixLambdaPi/SigmaWindow.lean`.  For `Mix (Pi, Lambda)` the
nonpolarized genes sit at odd rank and the polarized genes at even rank, so the
type4/5/8 windows shift down by one and the type6/7 windows shift up by one
relative to `Mix (Lambda, Pi)`.

The gene structures (with `m ≤ n`, `ε ≠ NonPolarized`):
* type4: `X = NP(2m+1)+NP(2n+1)`, `Y = ε(2m)+(-ε)(2n+2)`;
* type5: `X = NP(2m+1)+ε(2n+2)`, `Y = ε(2m)+NP(2n+3)`;
* type6: `X = ε(2m+2)+NP(2n+3)`, `Y = NP(2m+1)+ε(2n+4)`;
* type7: `X = ε(2m+2)+(-ε)(2n+2)`, `Y = NP(2m+1)+NP(2n+3)`;
* type8: `X = ε(2m+2)+ε(2n+2)`, `Y = ε(2m)+ε(2n+4)`.
-/

variable {m n : ℕ}

/-! ### type8 -/

private lemma signature_prime_X8 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X8 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 2 - j) ε) +
      signature (Gene.ofRank (2 * n + 2 - j) ε) := by
  rw [X8_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y8 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y8 h_le hε).1) =
      signature (Gene.ofRank (2 * m - j) ε) +
      signature (Gene.ofRank (2 * n + 4 - j) ε) := by
  rw [Y8_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

lemma sigma_type8_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m) :
    signature (Chromosome.prime^[j] (X8 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y8 h_le hε).1) := by
  rw [signature_prime_X8 h_le hε, signature_prime_Y8 h_le hε]
  have hbot : 2 * m + 2 - j = (2 * m - j) + 2 := by omega
  have htop : 2 * n + 4 - j = (2 * n + 2 - j) + 2 := by omega
  rw [hbot, htop, signature_ofRank_eq₂', signature_ofRank_eq₂']
  abel

lemma sigma_type8_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 4 ≤ j) :
    signature (Chromosome.prime^[j] (X8 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y8 h_le hε).1) := by
  rw [signature_prime_X8 h_le hε, signature_prime_Y8 h_le hε]
  rw [show 2 * m + 2 - j = 0 from by omega, show 2 * n + 2 - j = 0 from by omega,
    show 2 * m - j = 0 from by omega, show 2 * n + 4 - j = 0 from by omega]

lemma sigma_type8_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m < j) (hj2 : j < 2 * n + 4) :
    signature (Chromosome.prime^[j] (Y8 h_le hε).1) -
      signature (Chromosome.prime^[j] (X8 h_le hε).1) =
      (if j ≤ 2 * n + 2 then (1, 1) else signature (Gene.ofRank 1 ε)) +
      (if 2 * m + 2 ≤ j then 0 else -signature (Gene.ofRank 1 ε)) := by
  rw [signature_prime_X8 h_le hε, signature_prime_Y8 h_le hε]
  by_cases hbot : 2 * m + 2 ≤ j
  · rw [show 2 * m - j = 0 from by omega, show 2 * m + 2 - j = 0 from by omega,
      signature_ofRank_zero, zero_add, zero_add, if_pos hbot, add_zero]
    by_cases htop : j ≤ 2 * n + 2
    · rw [if_pos htop, show 2 * n + 4 - j = (2 * n + 2 - j) + 2 from by omega,
        signature_ofRank_eq₂']
      abel
    · rw [if_neg htop, show 2 * n + 4 - j = 1 from by omega,
        show 2 * n + 2 - j = 0 from by omega, signature_ofRank_zero, sub_zero]
  · have hj_eq : j = 2 * m + 1 := by omega
    rw [if_neg hbot, hj_eq, show 2 * m - (2 * m + 1) = 0 from by omega,
      show 2 * m + 2 - (2 * m + 1) = 1 from by omega, signature_ofRank_zero, zero_add]
    have htop : 2 * m + 1 ≤ 2 * n + 2 := by omega
    rw [if_pos htop, show 2 * n + 4 - (2 * m + 1) = (2 * n + 2 - (2 * m + 1)) + 2 from by omega,
      signature_ofRank_eq₂']
    abel

/-! ### type4 -/

private lemma signature_prime_X4 (h_le : m ≤ n) {ε : GeneType} (_hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X4 h_le).1) =
      signature (Gene.ofRank (2 * m + 1 - j) .NonPolarized) +
      signature (Gene.ofRank (2 * n + 1 - j) .NonPolarized) := by
  rw [X4_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y4 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y4 h_le hε).1) =
      signature (Gene.ofRank (2 * m - j) ε) +
      signature (Gene.ofRank (2 * n + 2 - j) (-ε)) := by
  rw [Y4_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

lemma sigma_type4_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m) :
    signature (Chromosome.prime^[j] (X4 h_le).1) =
      signature (Chromosome.prime^[j] (Y4 h_le hε).1) := by
  rw [signature_prime_X4 h_le hε, signature_prime_Y4 h_le hε,
    signature_ofRank_nonPolarized, signature_ofRank_nonPolarized,
    signature_ofRank_sum_even (by rw [Nat.even_iff]; omega), Prod.mk_add_mk, ← add_div]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
    Nat.cast_sub (by omega), Prod.mk.injEq]
  push_cast
  constructor <;> ring

lemma sigma_type4_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 2 ≤ j) :
    signature (Chromosome.prime^[j] (X4 h_le).1) =
      signature (Chromosome.prime^[j] (Y4 h_le hε).1) := by
  rw [signature_prime_X4 h_le hε, signature_prime_Y4 h_le hε,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 1 - j = 0 from by omega,
    show 2 * m - j = 0 from by omega, show 2 * n + 2 - j = 0 from by omega]
  simp

lemma sigma_type4_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m < j) (hj2 : j < 2 * n + 2) :
    signature (Chromosome.prime^[j] (Y4 h_le hε).1) -
      signature (Chromosome.prime^[j] (X4 h_le).1) =
      if Even (2 * n + 1 - j) then signature (Gene.ofRank 1 (-ε))
      else ((1 : ℚ) / 2, (1 : ℚ) / 2) := by
  rw [signature_prime_X4 h_le hε, signature_prime_Y4 h_le hε,
    show 2 * m - j = 0 from by omega, show 2 * m + 1 - j = 0 from by omega,
    signature_ofRank_zero, signature_ofRank_zero, zero_add, zero_add]
  by_cases htop0 : j = 2 * n + 1
  · subst htop0
    rw [show 2 * n + 2 - (2 * n + 1) = 1 from by omega,
      show 2 * n + 1 - (2 * n + 1) = 0 from by omega, signature_ofRank_zero, sub_zero,
      if_pos (by simp)]
  · rw [show 2 * n + 2 - j = (2 * n + 1 - j) + 1 from by omega]
    by_cases hpar : Even (2 * n + 1 - j)
    · rw [if_pos hpar,
        signature_ofRank_eq (k := 2 * n + 1 - j + 1) (by omega)
          (GeneType.neg_ne_nonPolarized_iff.1 hε),
        Nat.add_sub_cancel, neg_neg, signature_ofRank_even_half hpar,
        signature_ofRank_nonPolarized]
      abel
    · rw [if_neg hpar, signature_ofRank_even_half (by rw [Nat.even_add_one]; exact hpar),
        signature_ofRank_nonPolarized, Prod.mk_sub_mk, ← sub_div, Nat.cast_add, Nat.cast_one]
      norm_num

/-! ### type5 -/

private lemma signature_prime_X5 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X5 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 1 - j) .NonPolarized) +
      signature (Gene.ofRank (2 * n + 2 - j) ε) := by
  rw [X5_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y5 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y5 h_le hε).1) =
      signature (Gene.ofRank (2 * m - j) ε) +
      signature (Gene.ofRank (2 * n + 3 - j) .NonPolarized) := by
  rw [Y5_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

lemma sigma_type5_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m) :
    signature (Chromosome.prime^[j] (X5 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y5 h_le hε).1) := by
  rw [signature_prime_X5 h_le hε, signature_prime_Y5 h_le hε,
    show 2 * m + 1 - j = (2 * m - j) + 1 from by omega,
    show 2 * n + 3 - j = (2 * n + 2 - j) + 1 from by omega,
    signature_ofRank_nonPolarized_succ_add (by rw [Nat.even_iff]; omega)]

lemma sigma_type5_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 3 ≤ j) :
    signature (Chromosome.prime^[j] (X5 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y5 h_le hε).1) := by
  rw [signature_prime_X5 h_le hε, signature_prime_Y5 h_le hε,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 2 - j = 0 from by omega,
    show 2 * m - j = 0 from by omega, show 2 * n + 3 - j = 0 from by omega]
  rw [add_comm]

lemma sigma_type5_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m < j) (hj2 : j < 2 * n + 3) :
    signature (Chromosome.prime^[j] (Y5 h_le hε).1) -
      signature (Chromosome.prime^[j] (X5 h_le hε).1) =
      if Even (2 * n + 2 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
      else signature (Gene.ofRank 1 (-ε)) := by
  rw [signature_prime_X5 h_le hε, signature_prime_Y5 h_le hε,
    show 2 * m - j = 0 from by omega, show 2 * m + 1 - j = 0 from by omega,
    signature_ofRank_zero, signature_ofRank_zero, zero_add, zero_add]
  by_cases htop0 : j = 2 * n + 2
  · subst htop0
    rw [show 2 * n + 3 - (2 * n + 2) = 1 from by omega,
      show 2 * n + 2 - (2 * n + 2) = 0 from by omega, signature_ofRank_zero, sub_zero,
      if_pos (by simp), signature_ofRank_nonPolarized]
    norm_num
  · rw [show 2 * n + 3 - j = (2 * n + 2 - j) + 1 from by omega]
    by_cases hpar : Even (2 * n + 2 - j)
    · rw [if_pos hpar, signature_ofRank_nonPolarized, signature_ofRank_even_half hpar,
        Prod.mk_sub_mk, ← sub_div, Nat.cast_add, Nat.cast_one]
      norm_num
    · have hr1 : 1 ≤ 2 * n + 2 - j := by omega
      have heven : Even (2 * n + 2 - j - 1) :=
        Nat.Odd.sub_odd (Nat.not_even_iff_odd.1 hpar) odd_one
      rw [if_neg hpar, signature_ofRank_eq hr1 hε,
        signature_ofRank_even_half heven, signature_ofRank_nonPolarized]
      have hcast : ((2 * n + 2 - j + 1 : ℕ) : ℚ) = ((2 * n + 2 - j - 1 : ℕ) : ℚ) + 2 := by
        rw [Nat.cast_sub hr1, Nat.cast_add]; push_cast; ring
      rw [hcast]
      match ε, hε with
      | .Positive, _ =>
          rw [signature_ofRank_one_positive, GeneType.neg_positive,
            signature_ofRank_one_negative]
          simp only [Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
          constructor <;> ring
      | .Negative, _ =>
          rw [signature_ofRank_one_negative, GeneType.neg_negative,
            signature_ofRank_one_positive]
          simp only [Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
          constructor <;> ring

/-! ### type6 -/

private lemma signature_prime_X6 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X6 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 2 - j) ε) +
      signature (Gene.ofRank (2 * n + 3 - j) .NonPolarized) := by
  rw [X6_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y6 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y6 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 1 - j) .NonPolarized) +
      signature (Gene.ofRank (2 * n + 4 - j) ε) := by
  rw [Y6_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

lemma sigma_type6_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m + 1) :
    signature (Chromosome.prime^[j] (X6 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y6 h_le hε).1) := by
  rw [signature_prime_X6 h_le hε, signature_prime_Y6 h_le hε,
    show 2 * m + 2 - j = (2 * m + 1 - j) + 1 from by omega,
    show 2 * n + 4 - j = (2 * n + 3 - j) + 1 from by omega,
    signature_ofRank_succ_add_nonPolarized (by rw [Nat.even_iff]; omega)]

lemma sigma_type6_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 4 ≤ j) :
    signature (Chromosome.prime^[j] (X6 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y6 h_le hε).1) := by
  rw [signature_prime_X6 h_le hε, signature_prime_Y6 h_le hε,
    show 2 * m + 2 - j = 0 from by omega, show 2 * n + 3 - j = 0 from by omega,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 4 - j = 0 from by omega]
  rw [add_comm]

lemma sigma_type6_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m + 1 < j) (hj2 : j < 2 * n + 4) :
    signature (Chromosome.prime^[j] (Y6 h_le hε).1) -
      signature (Chromosome.prime^[j] (X6 h_le hε).1) =
      if Even (2 * n + 3 - j) then signature (Gene.ofRank 1 ε)
      else ((1 : ℚ) / 2, (1 : ℚ) / 2) := by
  rw [signature_prime_X6 h_le hε, signature_prime_Y6 h_le hε,
    show 2 * m + 2 - j = 0 from by omega, show 2 * m + 1 - j = 0 from by omega,
    signature_ofRank_zero, signature_ofRank_zero, zero_add, zero_add]
  by_cases htop0 : j = 2 * n + 3
  · subst htop0
    rw [show 2 * n + 4 - (2 * n + 3) = 1 from by omega,
      show 2 * n + 3 - (2 * n + 3) = 0 from by omega, signature_ofRank_zero, sub_zero,
      if_pos (by simp)]
  · rw [show 2 * n + 4 - j = (2 * n + 3 - j) + 1 from by omega]
    by_cases hpar : Even (2 * n + 3 - j)
    · rw [if_pos hpar,
        signature_ofRank_eq (k := 2 * n + 3 - j + 1) (by omega) hε,
        Nat.add_sub_cancel, signature_ofRank_even_half hpar, signature_ofRank_nonPolarized]
      abel
    · rw [if_neg hpar, signature_ofRank_even_half (by rw [Nat.even_add_one]; exact hpar),
        signature_ofRank_nonPolarized, Prod.mk_sub_mk, ← sub_div, Nat.cast_add, Nat.cast_one]
      norm_num

/-! ### type7 -/

private lemma signature_prime_X7 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X7 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 2 - j) ε) +
      signature (Gene.ofRank (2 * n + 2 - j) (-ε)) := by
  rw [X7_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y7 (h_le : m ≤ n) {ε : GeneType} (_hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y7 h_le).1) =
      signature (Gene.ofRank (2 * m + 1 - j) .NonPolarized) +
      signature (Gene.ofRank (2 * n + 3 - j) .NonPolarized) := by
  rw [Y7_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

lemma sigma_type7_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m + 1) :
    signature (Chromosome.prime^[j] (X7 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y7 h_le).1) := by
  rw [signature_prime_X7 h_le hε, signature_prime_Y7 h_le hε,
    show 2 * m + 2 - j = (2 * m + 1 - j) + 1 from by omega,
    show 2 * n + 2 - j = (2 * n + 3 - j) - 1 from by omega,
    signature_ofRank_succ_add_pred_neg (by omega) (by rw [Nat.even_iff]; omega)]

lemma sigma_type7_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 3 ≤ j) :
    signature (Chromosome.prime^[j] (X7 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y7 h_le).1) := by
  rw [signature_prime_X7 h_le hε, signature_prime_Y7 h_le hε,
    show 2 * m + 2 - j = 0 from by omega, show 2 * n + 2 - j = 0 from by omega,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 3 - j = 0 from by omega]
  simp

lemma sigma_type7_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m + 1 < j) (hj2 : j < 2 * n + 3) :
    signature (Chromosome.prime^[j] (Y7 h_le).1) -
      signature (Chromosome.prime^[j] (X7 h_le hε).1) =
      if Even (2 * n + 2 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
      else signature (Gene.ofRank 1 ε) := by
  rw [signature_prime_X7 h_le hε, signature_prime_Y7 h_le hε,
    show 2 * m + 2 - j = 0 from by omega, show 2 * m + 1 - j = 0 from by omega,
    signature_ofRank_zero, signature_ofRank_zero, zero_add, zero_add]
  by_cases htop0 : j = 2 * n + 2
  · subst htop0
    rw [show 2 * n + 3 - (2 * n + 2) = 1 from by omega,
      show 2 * n + 2 - (2 * n + 2) = 0 from by omega, signature_ofRank_zero, sub_zero,
      if_pos (by simp), signature_ofRank_nonPolarized]
    norm_num
  · rw [show 2 * n + 3 - j = (2 * n + 2 - j) + 1 from by omega]
    by_cases hpar : Even (2 * n + 2 - j)
    · rw [if_pos hpar, signature_ofRank_nonPolarized, signature_ofRank_even_half hpar,
        Prod.mk_sub_mk, ← sub_div, Nat.cast_add, Nat.cast_one]
      norm_num
    · have hr1 : 1 ≤ 2 * n + 2 - j := by omega
      have heven : Even (2 * n + 2 - j - 1) :=
        Nat.Odd.sub_odd (Nat.not_even_iff_odd.1 hpar) odd_one
      rw [if_neg hpar, signature_ofRank_eq hr1 (GeneType.neg_ne_nonPolarized_iff.1 hε),
        neg_neg, signature_ofRank_even_half heven, signature_ofRank_nonPolarized]
      have hcast : ((2 * n + 2 - j + 1 : ℕ) : ℚ) = ((2 * n + 2 - j - 1 : ℕ) : ℚ) + 2 := by
        rw [Nat.cast_sub hr1, Nat.cast_add]; push_cast; ring
      rw [hcast]
      match ε, hε with
      | .Positive, _ =>
          rw [GeneType.neg_positive, signature_ofRank_one_negative,
            signature_ofRank_one_positive]
          simp only [Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
          constructor <;> ring
      | .Negative, _ =>
          rw [GeneType.neg_negative, signature_ofRank_one_positive,
            signature_ofRank_one_negative]
          simp only [Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
          constructor <;> ring

end MixPiLambda
