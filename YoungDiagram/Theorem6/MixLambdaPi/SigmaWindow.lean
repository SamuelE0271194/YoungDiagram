import YoungDiagram.Mutations.MixLambdaPi

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-! ## §15.10 Case A: the `sigma`-window for the `type8` primitive mutation.

The `type8` source and target are
`X8 = ofRank (2m+3) ε + ofRank (2n+3) ε` and
`Y8 = ofRank (2m+1) ε + ofRank (2n+5) ε`  (with `m ≤ n`, `ε ≠ NonPolarized`).

Following `prime^[j]`, each gene's rank drops by `j` (truncated at `0`).  Writing
`s k := signature (Gene.ofRank k ε)`, we have
`signature (prime^[j] X8) = s (2m+3-j) + s (2n+3-j)` and
`signature (prime^[j] Y8) = s (2m+1-j) + s (2n+5-j)`.

The difference `signature (prime^[j] Y8) - signature (prime^[j] X8)` splits as
`(s (2m+1-j) - s (2m+3-j)) + (s (2n+5-j) - s (2n+3-j))`, the "bottom" and "top"
brackets.  Since `s (k+2) = s k + (1,1)`:

* **Before the window** (`j ≤ 2m+1`): bottom `= -(1,1)`, top `= +(1,1)`, so the
  two signatures are **equal**.
* **After the window** (`j ≥ 2n+5`): all four ranks are `0`, so again **equal**.
* **Inside the window** (`2m+1 < j < 2n+5`): the difference is explicit, equal to
  `(1,1)` on the deep interior `2m+3 ≤ j ≤ 2n+3` and acquiring a half-integer
  correction `signature (ofRank 1 ε)` at the two boundary iterates
  `j = 2m+2` and `j = 2n+4`.
-/

variable {m n : ℕ}

/-- Convenience: the per-level signatures of the `type8` source and target,
expanded into the two constituent genes. -/
private lemma signature_prime_X8 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X8 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 3 - j) ε) +
      signature (Gene.ofRank (2 * n + 3 - j) ε) := by
  rw [X8_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y8 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y8 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 1 - j) ε) +
      signature (Gene.ofRank (2 * n + 5 - j) ε) := by
  rw [Y8_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

/-- **Before the window.** For `j ≤ 2m+1`, the source and target have equal signature. -/
lemma sigma_type8_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m + 1) :
    signature (Chromosome.prime^[j] (X8 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y8 h_le hε).1) := by
  rw [signature_prime_X8 h_le hε, signature_prime_Y8 h_le hε]
  have hbot : 2 * m + 3 - j = (2 * m + 1 - j) + 2 := by omega
  have htop : 2 * n + 5 - j = (2 * n + 3 - j) + 2 := by omega
  rw [hbot, htop, signature_ofRank_eq₂', signature_ofRank_eq₂']
  abel

/-- **After the window.** For `j ≥ 2n+5`, all four genes have collapsed to rank `0`,
so the source and target have equal (zero) signature. -/
lemma sigma_type8_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 5 ≤ j) :
    signature (Chromosome.prime^[j] (X8 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y8 h_le hε).1) := by
  rw [signature_prime_X8 h_le hε, signature_prime_Y8 h_le hε]
  rw [show 2 * m + 3 - j = 0 from by omega, show 2 * n + 3 - j = 0 from by omega,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 5 - j = 0 from by omega]

/-- **Inside the window.** For `2m+1 < j < 2n+5`, the difference of signatures is
explicit:
* it equals `(1, 1)` on the deep interior `2m+3 ≤ j ≤ 2n+3`;
* at the bottom boundary `j = 2m+2` it is `(1,1) - signature (ofRank 1 ε)`;
* at the top boundary `j = 2n+4` it is `signature (ofRank 1 ε)`;
* if the window has length one (`m = n`, forcing `j = 2m+2 = 2n+2`) the two
  corrections combine.

Writing `S₁ := signature (ofRank 1 ε)` (so `S₁ = (1,0)` if `ε = Positive`,
`(0,1)` if `ε = Negative`), the difference is the sum of the "top" bracket
`if j ≤ 2n+3 then (1,1) else S₁` and the "bottom" bracket
`if 2m+3 ≤ j then 0 else -S₁`. -/
lemma sigma_type8_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m + 1 < j) (hj2 : j < 2 * n + 5) :
    signature (Chromosome.prime^[j] (Y8 h_le hε).1) -
      signature (Chromosome.prime^[j] (X8 h_le hε).1) =
      (if j ≤ 2 * n + 3 then (1, 1) else signature (Gene.ofRank 1 ε)) +
      (if 2 * m + 3 ≤ j then 0 else -signature (Gene.ofRank 1 ε)) := by
  rw [signature_prime_X8 h_le hε, signature_prime_Y8 h_le hε]
  by_cases hbot : 2 * m + 3 ≤ j
  · -- bottom genes both collapse to rank 0
    rw [show 2 * m + 1 - j = 0 from by omega, show 2 * m + 3 - j = 0 from by omega,
      signature_ofRank_zero, zero_add, zero_add, if_pos hbot, add_zero]
    by_cases htop : j ≤ 2 * n + 3
    · -- top bracket is (1,1)
      rw [if_pos htop, show 2 * n + 5 - j = (2 * n + 3 - j) + 2 from by omega,
        signature_ofRank_eq₂']
      abel
    · -- top boundary: ranks 1 and 0
      rw [if_neg htop, show 2 * n + 5 - j = 1 from by omega,
        show 2 * n + 3 - j = 0 from by omega, signature_ofRank_zero, sub_zero]
  · -- bottom boundary: j = 2m+2, ranks 0 and 1
    have hj_eq : j = 2 * m + 2 := by omega
    rw [if_neg hbot, hj_eq, show 2 * m + 1 - (2 * m + 2) = 0 from by omega,
      show 2 * m + 3 - (2 * m + 2) = 1 from by omega, signature_ofRank_zero, zero_add]
    have htop : 2 * m + 2 ≤ 2 * n + 3 := by omega
    rw [if_pos htop, show 2 * n + 5 - (2 * m + 2) = (2 * n + 3 - (2 * m + 2)) + 2 from by omega,
      signature_ofRank_eq₂']
    abel

/-! ## §15.10 Case A: the `sigma`-window for the `type4` primitive mutation.

`X4 = ofRank (2m+2) NP + ofRank (2n+2) NP` and
`Y4 = ofRank (2m+1) ε + ofRank (2n+3) (-ε)`  (with `m ≤ n`, `ε ≠ NonPolarized`).

After `prime^[j]`:
`signature (prime^[j] X4) = s (2m+2-j) NP + s (2n+2-j) NP` and
`signature (prime^[j] Y4) = s (2m+1-j) ε + s (2n+3-j) (-ε)`.

* **Before the window** (`j ≤ 2m+1`): equal (both `((2m+2n+4-2j)/2, ·)`, via
  `signature_ofRank_sum_even`).
* **After the window** (`j ≥ 2n+3`): all ranks `0`, so equal.
* **Inside the window** (`2m+1 < j < 2n+3`): explicit difference.
-/

private lemma signature_prime_X4 (h_le : m ≤ n) {ε : GeneType} (_hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X4 h_le).1) =
      signature (Gene.ofRank (2 * m + 2 - j) .NonPolarized) +
      signature (Gene.ofRank (2 * n + 2 - j) .NonPolarized) := by
  rw [X4_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y4 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y4 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 1 - j) ε) +
      signature (Gene.ofRank (2 * n + 3 - j) (-ε)) := by
  rw [Y4_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

/-- **Before the window.** For `j ≤ 2m+1`, the source and target have equal signature. -/
lemma sigma_type4_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m + 1) :
    signature (Chromosome.prime^[j] (X4 h_le).1) =
      signature (Chromosome.prime^[j] (Y4 h_le hε).1) := by
  rw [signature_prime_X4 h_le hε, signature_prime_Y4 h_le hε,
    signature_ofRank_nonPolarized, signature_ofRank_nonPolarized,
    signature_ofRank_sum_even (by rw [Nat.even_iff]; omega), Prod.mk_add_mk, ← add_div]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
    Nat.cast_sub (by omega), Prod.mk.injEq]
  push_cast
  constructor <;> ring

/-- **After the window.** For `j ≥ 2n+3`, all ranks collapse to `0`, so equal. -/
lemma sigma_type4_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 3 ≤ j) :
    signature (Chromosome.prime^[j] (X4 h_le).1) =
      signature (Chromosome.prime^[j] (Y4 h_le hε).1) := by
  rw [signature_prime_X4 h_le hε, signature_prime_Y4 h_le hε,
    show 2 * m + 2 - j = 0 from by omega, show 2 * n + 2 - j = 0 from by omega,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 3 - j = 0 from by omega]
  simp

/-- **Inside the window.** For `2m+1 < j < 2n+3`, both bottom genes have already
collapsed (`2m+1-j = 2m+2-j = 0`), so the whole difference is the "top" bracket
`s (2n+3-j) (-ε) - s (2n+2-j) NP`, which by parity equals `signature (ofRank 1 (-ε))`
when `2n+2-j` is even and `(1/2, 1/2)` when it is odd. -/
lemma sigma_type4_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m + 1 < j) (hj2 : j < 2 * n + 3) :
    signature (Chromosome.prime^[j] (Y4 h_le hε).1) -
      signature (Chromosome.prime^[j] (X4 h_le).1) =
      if Even (2 * n + 2 - j) then signature (Gene.ofRank 1 (-ε))
      else ((1 : ℚ) / 2, (1 : ℚ) / 2) := by
  rw [signature_prime_X4 h_le hε, signature_prime_Y4 h_le hε,
    show 2 * m + 1 - j = 0 from by omega, show 2 * m + 2 - j = 0 from by omega,
    signature_ofRank_zero, signature_ofRank_zero, zero_add, zero_add]
  -- Now reduce to the single "top" difference `s (2n+3-j) (-ε) - s (2n+2-j) NP`.
  by_cases htop0 : j = 2 * n + 2
  · -- top boundary: Y top rank 1, X top rank 0
    subst htop0
    rw [show 2 * n + 3 - (2 * n + 2) = 1 from by omega,
      show 2 * n + 2 - (2 * n + 2) = 0 from by omega, signature_ofRank_zero, sub_zero,
      if_pos (by simp)]
  · -- deep interior: 2n+2-j ≥ 1; split on its parity
    rw [show 2 * n + 3 - j = (2 * n + 2 - j) + 1 from by omega]
    by_cases hpar : Even (2 * n + 2 - j)
    · -- 2n+2-j even ⇒ Y top rank odd: s(r+1,-ε) = s(r,ε)+s(1,-ε), s(r,ε)=s(r,NP)
      rw [if_pos hpar,
        signature_ofRank_eq (k := 2 * n + 2 - j + 1) (by omega)
          (GeneType.neg_ne_nonPolarized_iff.1 hε),
        Nat.add_sub_cancel, neg_neg, signature_ofRank_even_half hpar,
        signature_ofRank_nonPolarized]
      abel
    · -- 2n+2-j odd ⇒ Y top rank even: s(r+1,-ε) = ((r+1)/2,·), X = (r/2,·)
      rw [if_neg hpar, signature_ofRank_even_half (by rw [Nat.even_add_one]; exact hpar),
        signature_ofRank_nonPolarized, Prod.mk_sub_mk, ← sub_div, Nat.cast_add, Nat.cast_one]
      norm_num

/-! ## §15.10 Case A: the `sigma`-window for the `type5` primitive mutation.

`X5 = ofRank (2m+2) NP + ofRank (2n+3) ε` and
`Y5 = ofRank (2m+1) ε + ofRank (2n+4) NP`  (with `m ≤ n`, `ε ≠ NonPolarized`).

After `prime^[j]`:
`signature (prime^[j] X5) = s (2m+2-j) NP + s (2n+3-j) ε` and
`signature (prime^[j] Y5) = s (2m+1-j) ε + s (2n+4-j) NP`.

* **Before the window** (`j ≤ 2m+1`): equal, via `signature_ofRank_nonPolarized_succ_add`.
* **After the window** (`j ≥ 2n+4`): all ranks `0`, so equal.
* **Inside the window** (`2m+1 < j < 2n+4`): both bottom genes have collapsed, so the
  difference is the "top" bracket `s (2n+4-j) NP - s (2n+3-j) ε`, equal to `(1/2,1/2)`
  when `2n+3-j` is even and `signature (ofRank 1 (-ε))` when it is odd.
-/

private lemma signature_prime_X5 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X5 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 2 - j) .NonPolarized) +
      signature (Gene.ofRank (2 * n + 3 - j) ε) := by
  rw [X5_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y5 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y5 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 1 - j) ε) +
      signature (Gene.ofRank (2 * n + 4 - j) .NonPolarized) := by
  rw [Y5_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

/-- **Before the window.** For `j ≤ 2m+1`, the source and target have equal signature. -/
lemma sigma_type5_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m + 1) :
    signature (Chromosome.prime^[j] (X5 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y5 h_le hε).1) := by
  rw [signature_prime_X5 h_le hε, signature_prime_Y5 h_le hε,
    show 2 * m + 2 - j = (2 * m + 1 - j) + 1 from by omega,
    show 2 * n + 4 - j = (2 * n + 3 - j) + 1 from by omega,
    signature_ofRank_nonPolarized_succ_add (by rw [Nat.even_iff]; omega)]

/-- **After the window.** For `j ≥ 2n+4`, all ranks collapse to `0`, so equal. -/
lemma sigma_type5_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 4 ≤ j) :
    signature (Chromosome.prime^[j] (X5 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y5 h_le hε).1) := by
  rw [signature_prime_X5 h_le hε, signature_prime_Y5 h_le hε,
    show 2 * m + 2 - j = 0 from by omega, show 2 * n + 3 - j = 0 from by omega,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 4 - j = 0 from by omega]
  rw [add_comm]

/-- **Inside the window.** For `2m+1 < j < 2n+4`, both bottom genes have collapsed,
so the difference is the "top" bracket `s (2n+4-j) NP - s (2n+3-j) ε`, equal to
`(1/2,1/2)` when `2n+3-j` is even and `signature (ofRank 1 (-ε))` when it is odd. -/
lemma sigma_type5_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m + 1 < j) (hj2 : j < 2 * n + 4) :
    signature (Chromosome.prime^[j] (Y5 h_le hε).1) -
      signature (Chromosome.prime^[j] (X5 h_le hε).1) =
      if Even (2 * n + 3 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
      else signature (Gene.ofRank 1 (-ε)) := by
  rw [signature_prime_X5 h_le hε, signature_prime_Y5 h_le hε,
    show 2 * m + 1 - j = 0 from by omega, show 2 * m + 2 - j = 0 from by omega,
    signature_ofRank_zero, signature_ofRank_zero, zero_add, zero_add]
  by_cases htop0 : j = 2 * n + 3
  · -- top boundary: Y top rank 1 (NP), X top rank 0
    subst htop0
    rw [show 2 * n + 4 - (2 * n + 3) = 1 from by omega,
      show 2 * n + 3 - (2 * n + 3) = 0 from by omega, signature_ofRank_zero, sub_zero,
      if_pos (by simp), signature_ofRank_nonPolarized]
    norm_num
  · -- deep interior: 2n+3-j ≥ 1; split on its parity
    rw [show 2 * n + 4 - j = (2 * n + 3 - j) + 1 from by omega]
    by_cases hpar : Even (2 * n + 3 - j)
    · -- 2n+3-j even ⇒ X top even half; Y top = ((r+1)/2,·)
      rw [if_pos hpar, signature_ofRank_nonPolarized, signature_ofRank_even_half hpar,
        Prod.mk_sub_mk, ← sub_div, Nat.cast_add, Nat.cast_one]
      norm_num
    · -- 2n+3-j odd ⇒ X top = s(r-1,-ε)+s(1,ε), Y top = ((r+1)/2,·)
      have hr1 : 1 ≤ 2 * n + 3 - j := by omega
      have heven : Even (2 * n + 3 - j - 1) :=
        Nat.Odd.sub_odd (Nat.not_even_iff_odd.1 hpar) odd_one
      rw [if_neg hpar, signature_ofRank_eq hr1 hε,
        signature_ofRank_even_half heven, signature_ofRank_nonPolarized]
      have hcast : ((2 * n + 3 - j + 1 : ℕ) : ℚ) = ((2 * n + 3 - j - 1 : ℕ) : ℚ) + 2 := by
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

/-! ## §15.10 Case A: the `sigma`-window for the `type6` primitive mutation.

`X6 = ofRank (2m+1) ε + ofRank (2n+2) NP` and
`Y6 = ofRank (2m) NP + ofRank (2n+3) ε`  (with `m ≤ n`, `ε ≠ NonPolarized`).

After `prime^[j]`:
`signature (prime^[j] X6) = s (2m+1-j) ε + s (2n+2-j) NP` and
`signature (prime^[j] Y6) = s (2m-j) NP + s (2n+3-j) ε`.

* **Before the window** (`j ≤ 2m`): equal, via `signature_ofRank_succ_add_nonPolarized`.
* **After the window** (`j ≥ 2n+3`): all ranks `0`, so equal.
* **Inside the window** (`2m < j < 2n+3`): both bottom genes have collapsed, so the
  difference is the "top" bracket `s (2n+3-j) ε - s (2n+2-j) NP`, equal to
  `signature (ofRank 1 ε)` when `2n+2-j` is even and `(1/2,1/2)` when it is odd.
-/

private lemma signature_prime_X6 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X6 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 1 - j) ε) +
      signature (Gene.ofRank (2 * n + 2 - j) .NonPolarized) := by
  rw [X6_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y6 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y6 h_le hε).1) =
      signature (Gene.ofRank (2 * m - j) .NonPolarized) +
      signature (Gene.ofRank (2 * n + 3 - j) ε) := by
  rw [Y6_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

/-- **Before the window.** For `j ≤ 2m`, the source and target have equal signature. -/
lemma sigma_type6_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m) :
    signature (Chromosome.prime^[j] (X6 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y6 h_le hε).1) := by
  rw [signature_prime_X6 h_le hε, signature_prime_Y6 h_le hε,
    show 2 * m + 1 - j = (2 * m - j) + 1 from by omega,
    show 2 * n + 3 - j = (2 * n + 2 - j) + 1 from by omega,
    signature_ofRank_succ_add_nonPolarized (by rw [Nat.even_iff]; omega)]

/-- **After the window.** For `j ≥ 2n+3`, all ranks collapse to `0`, so equal. -/
lemma sigma_type6_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 3 ≤ j) :
    signature (Chromosome.prime^[j] (X6 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y6 h_le hε).1) := by
  rw [signature_prime_X6 h_le hε, signature_prime_Y6 h_le hε,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 2 - j = 0 from by omega,
    show 2 * m - j = 0 from by omega, show 2 * n + 3 - j = 0 from by omega]
  rw [add_comm]

/-- **Inside the window.** For `2m < j < 2n+3`, both bottom genes have collapsed,
so the difference is the "top" bracket `s (2n+3-j) ε - s (2n+2-j) NP`, equal to
`signature (ofRank 1 ε)` when `2n+2-j` is even and `(1/2,1/2)` when it is odd. -/
lemma sigma_type6_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m < j) (hj2 : j < 2 * n + 3) :
    signature (Chromosome.prime^[j] (Y6 h_le hε).1) -
      signature (Chromosome.prime^[j] (X6 h_le hε).1) =
      if Even (2 * n + 2 - j) then signature (Gene.ofRank 1 ε)
      else ((1 : ℚ) / 2, (1 : ℚ) / 2) := by
  rw [signature_prime_X6 h_le hε, signature_prime_Y6 h_le hε,
    show 2 * m + 1 - j = 0 from by omega, show 2 * m - j = 0 from by omega,
    signature_ofRank_zero, signature_ofRank_zero, zero_add, zero_add]
  by_cases htop0 : j = 2 * n + 2
  · -- top boundary: Y top rank 1, X top rank 0
    subst htop0
    rw [show 2 * n + 3 - (2 * n + 2) = 1 from by omega,
      show 2 * n + 2 - (2 * n + 2) = 0 from by omega, signature_ofRank_zero, sub_zero,
      if_pos (by simp)]
  · -- deep interior: 2n+2-j ≥ 1; split on its parity
    rw [show 2 * n + 3 - j = (2 * n + 2 - j) + 1 from by omega]
    by_cases hpar : Even (2 * n + 2 - j)
    · -- 2n+2-j even ⇒ Y top rank odd: s(r+1,ε) = s(r,-ε)+s(1,ε), s(r,-ε)=s(r,NP)
      rw [if_pos hpar,
        signature_ofRank_eq (k := 2 * n + 2 - j + 1) (by omega) hε,
        Nat.add_sub_cancel, signature_ofRank_even_half hpar, signature_ofRank_nonPolarized]
      abel
    · -- 2n+2-j odd ⇒ Y top rank even
      rw [if_neg hpar, signature_ofRank_even_half (by rw [Nat.even_add_one]; exact hpar),
        signature_ofRank_nonPolarized, Prod.mk_sub_mk, ← sub_div, Nat.cast_add, Nat.cast_one]
      norm_num

/-! ## §15.10 Case A: the `sigma`-window for the `type7` primitive mutation.

`X7 = ofRank (2m+1) ε + ofRank (2n+1) (-ε)` and
`Y7 = ofRank (2m) NP + ofRank (2n+2) NP`  (with `m ≤ n`, `ε ≠ NonPolarized`).

After `prime^[j]`:
`signature (prime^[j] X7) = s (2m+1-j) ε + s (2n+1-j) (-ε)` and
`signature (prime^[j] Y7) = s (2m-j) NP + s (2n+2-j) NP`.

* **Before the window** (`j ≤ 2m`): equal, via `signature_ofRank_succ_add_pred_neg`.
* **After the window** (`j ≥ 2n+2`): all ranks `0`, so equal.
* **Inside the window** (`2m < j < 2n+2`): both bottom genes have collapsed, so the
  difference is the "top" bracket `s (2n+2-j) NP - s (2n+1-j) (-ε)`, equal to
  `(1/2,1/2)` when `2n+1-j` is even and `signature (ofRank 1 ε)` when it is odd.

Note: at `m = n` this reduces to the diagonal `signature_type7_*` lemmas of `Case3`. -/

private lemma signature_prime_X7 (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (X7 h_le hε).1) =
      signature (Gene.ofRank (2 * m + 1 - j) ε) +
      signature (Gene.ofRank (2 * n + 1 - j) (-ε)) := by
  rw [X7_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

private lemma signature_prime_Y7 (h_le : m ≤ n) {ε : GeneType} (_hε : ε ≠ .NonPolarized)
    (j : ℕ) :
    signature (Chromosome.prime^[j] (Y7 h_le).1) =
      signature (Gene.ofRank (2 * m - j) .NonPolarized) +
      signature (Gene.ofRank (2 * n + 2 - j) .NonPolarized) := by
  rw [Y7_eq, iterate_map_add, prime_iterate_ofRank, prime_iterate_ofRank, map_add]

/-- **Before the window.** For `j ≤ 2m`, the source and target have equal signature. -/
lemma sigma_type7_eq_before (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : j ≤ 2 * m) :
    signature (Chromosome.prime^[j] (X7 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y7 h_le).1) := by
  rw [signature_prime_X7 h_le hε, signature_prime_Y7 h_le hε,
    show 2 * m + 1 - j = (2 * m - j) + 1 from by omega,
    show 2 * n + 1 - j = (2 * n + 2 - j) - 1 from by omega,
    signature_ofRank_succ_add_pred_neg (by omega) (by rw [Nat.even_iff]; omega)]

/-- **After the window.** For `j ≥ 2n+2`, all ranks collapse to `0`, so equal. -/
lemma sigma_type7_eq_after (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj : 2 * n + 2 ≤ j) :
    signature (Chromosome.prime^[j] (X7 h_le hε).1) =
      signature (Chromosome.prime^[j] (Y7 h_le).1) := by
  rw [signature_prime_X7 h_le hε, signature_prime_Y7 h_le hε,
    show 2 * m + 1 - j = 0 from by omega, show 2 * n + 1 - j = 0 from by omega,
    show 2 * m - j = 0 from by omega, show 2 * n + 2 - j = 0 from by omega]
  simp

/-- **Inside the window.** For `2m < j < 2n+2`, both bottom genes have collapsed,
so the difference is the "top" bracket `s (2n+2-j) NP - s (2n+1-j) (-ε)`, equal to
`(1/2,1/2)` when `2n+1-j` is even and `signature (ofRank 1 ε)` when it is odd. -/
lemma sigma_type7_mid (h_le : m ≤ n) {ε : GeneType} (hε : ε ≠ .NonPolarized)
    {j : ℕ} (hj1 : 2 * m < j) (hj2 : j < 2 * n + 2) :
    signature (Chromosome.prime^[j] (Y7 h_le).1) -
      signature (Chromosome.prime^[j] (X7 h_le hε).1) =
      if Even (2 * n + 1 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
      else signature (Gene.ofRank 1 ε) := by
  rw [signature_prime_X7 h_le hε, signature_prime_Y7 h_le hε,
    show 2 * m + 1 - j = 0 from by omega, show 2 * m - j = 0 from by omega,
    signature_ofRank_zero, signature_ofRank_zero, zero_add, zero_add]
  by_cases htop0 : j = 2 * n + 1
  · -- top boundary: Y top rank 1 (NP), X top rank 0
    subst htop0
    rw [show 2 * n + 2 - (2 * n + 1) = 1 from by omega,
      show 2 * n + 1 - (2 * n + 1) = 0 from by omega, signature_ofRank_zero, sub_zero,
      if_pos (by simp), signature_ofRank_nonPolarized]
    norm_num
  · -- deep interior: 2n+1-j ≥ 1; split on its parity
    rw [show 2 * n + 2 - j = (2 * n + 1 - j) + 1 from by omega]
    by_cases hpar : Even (2 * n + 1 - j)
    · -- 2n+1-j even ⇒ X top even half; Y top = ((r+1)/2,·)
      rw [if_pos hpar, signature_ofRank_nonPolarized, signature_ofRank_even_half hpar,
        Prod.mk_sub_mk, ← sub_div, Nat.cast_add, Nat.cast_one]
      norm_num
    · -- 2n+1-j odd ⇒ X top = s(r-1,ε)+s(1,-ε), Y top = ((r+1)/2,·)
      have hr1 : 1 ≤ 2 * n + 1 - j := by omega
      have heven : Even (2 * n + 1 - j - 1) :=
        Nat.Odd.sub_odd (Nat.not_even_iff_odd.1 hpar) odd_one
      rw [if_neg hpar, signature_ofRank_eq hr1 (GeneType.neg_ne_nonPolarized_iff.1 hε),
        neg_neg, signature_ofRank_even_half heven, signature_ofRank_nonPolarized]
      have hcast : ((2 * n + 1 - j + 1 : ℕ) : ℚ) = ((2 * n + 1 - j - 1 : ℕ) : ℚ) + 2 := by
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

end MixLambdaPi
