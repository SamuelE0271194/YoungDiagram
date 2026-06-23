import YoungDiagram.Theorem6.MixLambdaPi.CaseA
import YoungDiagram.Theorem6.MixLambdaPi.CaseBProp

/-!
# §16 Case A, Branch B, **Case 3** (`m ≥ 3`) for `Mix (Lambda, Pi)` (label 1).

`g₁ = g⁺(m)` is the minimal-rank gene of `X` with `m = 2m'+1 ≥ 3` (`m' ≥ 1`).
Following §16 (Djoković) we either have `X ⊇ 2g₁` (the type8 diagonal mutation
`2g⁺(m) → g⁺(m-2) + g⁺(m+2)`), or a second gene `g₂` of `X - g₁` of minimal rank
`k`, giving:

* `g₂ = g(k)` nonpolarized → `g⁺(m) + g(k) → g(m-1) + g⁺(k+1)` (type6);
* `g₂ = g⁻(k)`            → `g⁺(m) + g⁻(k) → g(m-1) + g(k+1)`  (type7);
* `g₂ = g⁺(k)`            → `g⁺(m) + g⁺(k) → g⁺(m-2) + g⁺(k+2)` (type8).

The type6/type7 charges only require the `a`-propagation `branchB_case5_aprop_gen`
(anchored at `a₁ < c₁`), exactly as in Case 5; the assemblies below are the
general-bottom-`m'` analogues of `branchB_case5_assembly_type{6,7}`.  The type8
charge and the `2g₁` diagonal additionally need the deep-interior `(1,1)` window
absorption (odd-level integer gap), which is isolated as `sorry` for a dedicated
effort.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-- **Odd-interior `(1,1)` absorption.**  At an odd level `r`, `Mix (Lambda, Pi)` has
`a = b`, so `2·a = rank(prime^[r] ·)`.  If `σX(r) ≤ σY(r)` strictly (componentwise `≤`
and `≠`) and the two ranks have the **same parity**, then the gap is a full `(1,1)`
(not just the `(1/2,1/2)` of `half_le_sigma_diff_at_r`): strictness gives
`rank_X < rank_Y`, and equal parity upgrades this to `rank_Y ≥ rank_X + 2`, i.e.
`a_Y ≥ a_X + 1` (and `b` likewise).  This is the structural core of §16 Case 3 type8. -/
lemma odd_interior_absorb {X Y : Chromosome}
    (hX : X ∈ Mix (Lambda, Pi)) (hY : Y ∈ Mix (Lambda, Pi))
    {r : ℕ} (hodd : Odd r)
    (hle : signature (Chromosome.prime^[r] X) ≤ signature (Chromosome.prime^[r] Y))
    (hne : signature (Chromosome.prime^[r] X) ≠ signature (Chromosome.prime^[r] Y))
    (hpar : (Chromosome.prime^[r] X).rank % 2 = (Chromosome.prime^[r] Y).rank % 2) :
    ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[r] X) ≤
      signature (Chromosome.prime^[r] Y) := by
  have hXeq := signature_prime_iterate_odd_eq_components hX hodd
  have hYeq := signature_prime_iterate_odd_eq_components hY hodd
  set sX := signature (Chromosome.prime^[r] X) with hsX
  set sY := signature (Chromosome.prime^[r] Y) with hsY
  -- `2 * sX.1 = rank_X`, `2 * sY.1 = rank_Y`
  have hrX : 2 * sX.1 = ((Chromosome.prime^[r] X).rank : ℚ) := by
    have h := @signature_sum_eq_rank (Chromosome.prime^[r] X)
    rw [← hsX] at h; rw [show 2 * sX.1 = sX.1 + sX.2 from by rw [hXeq]; ring]; exact h
  have hrY : 2 * sY.1 = ((Chromosome.prime^[r] Y).rank : ℚ) := by
    have h := @signature_sum_eq_rank (Chromosome.prime^[r] Y)
    rw [← hsY] at h; rw [show 2 * sY.1 = sY.1 + sY.2 from by rw [hYeq]; ring]; exact h
  -- strictness in the first component
  have h_ne : sX.1 ≠ sY.1 := by
    intro heq; apply hne; ext
    · exact heq
    · rw [← hXeq, ← hYeq]; exact heq
  have h_lt : sX.1 < sY.1 := lt_of_le_of_ne hle.1 h_ne
  -- ranks: strict + equal parity ⇒ gap ≥ 2
  set rX := (Chromosome.prime^[r] X).rank with hrXdef
  set rY := (Chromosome.prime^[r] Y).rank with hrYdef
  have hrlt : rX < rY := by
    have : (rX : ℚ) < (rY : ℚ) := by rw [← hrX, ← hrY]; linarith
    exact_mod_cast this
  have hrge : rX + 2 ≤ rY := by omega
  have hge : sX.1 + 1 ≤ sY.1 := by
    have : (rX : ℚ) + 2 ≤ (rY : ℚ) := by exact_mod_cast hrge
    rw [← hrX, ← hrY] at this; linarith
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add]; linarith
  · simp only [Prod.snd_add]; rw [← hXeq, ← hYeq]; linarith

/-- **Assembly** of §16 Branch B Case 3, `g₂ = g(k)` nonpolarized (type6, general
bottom `m'`).  Builds `g⁺(m) + g(k) → g(m-1) + g⁺(k+1)` and proves `Z ≤ Y` over the
window `2m' < j < 2n'+3`: even-level difference `(1,0)` absorbed by `hprop_even`,
odd-level `(1/2,1/2)` by `half_le_sigma_diff_at_r`.  General-`m'` analogue of
`branchB_case5_assembly_type6`. -/
lemma branchB_case3_assembly_type6 {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' n' : ℕ) (h_le : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm_pos : gm.type = .Positive)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_even : ∀ j, 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 1 ≤ j → j < 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push_neg at hsigeq
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y6' : Mix (Lambda, Pi) := Y6 h_le hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * m' + 1) .Positive = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_pos] at h; exact h
  have hgk_eq : Gene.ofRank (2 * n' + 2) .NonPolarized = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_np] at h; exact h
  have hX6_val : (X6 h_le hε).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X6_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X6 h_le hε).1 + restval = X.1.1 := by
    rw [hX6_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Lambda, Pi) := ⟨Y6'.1 + restval, add_mem Y6'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X6 h_le hε : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X6 h_le hε) Y6' rest_M
      (MixLambdaPi.Primitive.type6 GeneType.Positive hε h_le), ?_⟩
  change Y6'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X6 h_le hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m'
  · have h66 : signature (Chromosome.prime^[j] Y6'.1) =
        signature (Chromosome.prime^[j] (X6 h_le hε).1) :=
      (sigma_type6_eq_before h_le hε (hj := hj)).symm
    rw [h66, ← hdecomp]; exact hXYj
  · have h_not_before : 2 * m' < j := by omega
    by_cases hj_after : 2 * n' + 3 ≤ j
    · have h66 : signature (Chromosome.prime^[j] Y6'.1) =
          signature (Chromosome.prime^[j] (X6 h_le hε).1) :=
        (sigma_type6_eq_after h_le hε (hj := hj_after)).symm
      rw [h66, ← hdecomp]; exact hXYj
    · have h_mid : j < 2 * n' + 3 := by omega
      have hmid := sigma_type6_mid h_le hε h_not_before h_mid
      have hY6_eq : signature (Chromosome.prime^[j] Y6'.1) =
          signature (Chromosome.prime^[j] (X6 h_le hε).1) +
            (if Even (2 * n' + 2 - j) then signature (Gene.ofRank 1 GeneType.Positive)
             else ((1 : ℚ) / 2, (1 : ℚ) / 2)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY6_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 2 - j)
      · rw [if_pos hpar]
        have h_even_j : Even j := by
          have hp : (2 * n' + 2 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.even_iff]; omega
        rw [signature_ofRank_one_positive]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have hj2 : 2 ≤ j := by obtain ⟨t, ht⟩ := h_even_j; omega
          have h_sigma := hprop_even j hj2 (by omega) h_even_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · show (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · show (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          rw [add_zero]; exact hXYj.2
      · rw [if_neg hpar]
        have hodd_j : Odd j := by
          have hp : (2 * n' + 2 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.odd_iff]; omega
        have hne' : signature (Chromosome.prime^[j] X.1.1) ≠
            signature (Chromosome.prime^[j] Y.1.1) := by
          intro h_eq
          exact hsigeq j (by omega)
            (hYwin j (by omega) (by rcases hodd_j with ⟨t, rfl⟩; omega))
            (by simpa [Sigma.sigma] using h_eq)
        rw [add_comm]
        exact half_le_sigma_diff_at_r X.1.2 Y.1.2 hodd_j hXYj hne'

/-- **Assembly** of §16 Branch B Case 3, `g₂ = g⁻(k)` (type7, general bottom `m'`).
Builds `g⁺(m) + g⁻(k) → g(m-1) + g(k+1)` and proves `Z ≤ Y` over `2m' < j < 2n'+2`.
General-`m'` analogue of `branchB_case5_assembly_type7`. -/
lemma branchB_case3_assembly_type7 {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' n' : ℕ) (h_le : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm_pos : gm.type = .Positive)
    (hgk_rank : gk.rank = 2 * n' + 1) (hgk_neg : gk.type = .Negative)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_even : ∀ j, 2 ≤ j → j ≤ 2 * n' → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 1 ≤ j → j ≤ 2 * n' + 1 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push_neg at hsigeq
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y7' : Mix (Lambda, Pi) := Y7 h_le
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * m' + 1) .Positive = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_pos] at h; exact h
  have hgk_eq : Gene.ofRank (2 * n' + 1) .Negative = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_neg] at h; exact h
  have hX7_val : (X7 h_le hε).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X7_eq, GeneType.neg_positive, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X7 h_le hε).1 + restval = X.1.1 := by
    rw [hX7_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Lambda, Pi) := ⟨Y7'.1 + restval, add_mem Y7'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X7 h_le hε : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X7 h_le hε) Y7' rest_M
      (MixLambdaPi.Primitive.type7 GeneType.Positive hε h_le), ?_⟩
  change Y7'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X7 h_le hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m'
  · have h77 : signature (Chromosome.prime^[j] Y7'.1) =
        signature (Chromosome.prime^[j] (X7 h_le hε).1) :=
      (sigma_type7_eq_before h_le hε (hj := hj)).symm
    rw [h77, ← hdecomp]; exact hXYj
  · have h_not_before : 2 * m' < j := by omega
    by_cases hj_after : 2 * n' + 2 ≤ j
    · have h77 : signature (Chromosome.prime^[j] Y7'.1) =
          signature (Chromosome.prime^[j] (X7 h_le hε).1) :=
        (sigma_type7_eq_after h_le hε (hj := hj_after)).symm
      rw [h77, ← hdecomp]; exact hXYj
    · have h_mid : j < 2 * n' + 2 := by omega
      have hmid := sigma_type7_mid h_le hε h_not_before h_mid
      have hY7_eq : signature (Chromosome.prime^[j] Y7'.1) =
          signature (Chromosome.prime^[j] (X7 h_le hε).1) +
            (if Even (2 * n' + 1 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
             else signature (Gene.ofRank 1 GeneType.Positive)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY7_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 1 - j)
      · rw [if_pos hpar]
        have hodd_j : Odd j := by
          have hp : (2 * n' + 1 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.odd_iff]; omega
        have hne' : signature (Chromosome.prime^[j] X.1.1) ≠
            signature (Chromosome.prime^[j] Y.1.1) := by
          intro h_eq
          exact hsigeq j (by omega) (hYwin j (by omega) (by omega))
            (by simpa [Sigma.sigma] using h_eq)
        rw [add_comm]
        exact half_le_sigma_diff_at_r X.1.2 Y.1.2 hodd_j hXYj hne'
      · rw [if_neg hpar]
        have h_even_j : Even j := by
          have hp : (2 * n' + 1 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.even_iff]; omega
        rw [signature_ofRank_one_positive]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have hj2 : 2 ≤ j := by obtain ⟨t, ht⟩ := h_even_j; omega
          have hjle : j ≤ 2 * n' := by obtain ⟨t, ht⟩ := h_even_j; omega
          have h_sigma := hprop_even j hj2 hjle h_even_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · show (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · show (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          rw [add_zero]; exact hXYj.2

/-- **Assembly** of §16 Branch B Case 3, `g₂ = g⁺(k)` (type8).  Builds
`g⁺(m) + g⁺(k) → g⁺(m-2) + g⁺(k+2)` (with `gm.rank = 2p+3 = m`, `gk.rank = 2q+3 = k`)
and proves `Z ≤ Y` over `2p+1 < j < 2q+5`.  The window difference is:
* `j = 2p+2` (`= m-1`): `(0,1)`, absorbed by `hbanchor`;
* `2p+3 ≤ j ≤ 2q+3` (`= [m, k]`): `(1,1)` — even `j` by `haeven`+`hbeven`, odd `j` by
  the supplied `hoddabsorb` (i.e. `odd_interior_absorb` + the rank-parity);
* `j = 2q+4` (`= k+1`): `(1,0)`, absorbed by `haeven`. -/
lemma branchB_case3_assembly_type8 {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (p q : ℕ) (h_le : p ≤ q)
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * p + 3) (hgm_pos : gm.type = .Positive)
    (hgk_rank : gk.rank = 2 * q + 3) (hgk_pos : gk.type = .Positive)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hbanchor : (Sigma.sigma X.1.1 (2 * p + 2)).2 + 1 ≤ (Sigma.sigma Y.1.1 (2 * p + 2)).2)
    (haeven : ∀ j, Even j → 2 * p + 3 ≤ j → j ≤ 2 * q + 4 →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hbeven : ∀ j, Even j → 2 * p + 3 ≤ j → j ≤ 2 * q + 3 →
        (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2)
    (hoddabsorb : ∀ j, Odd j → 2 * p + 3 ≤ j → j ≤ 2 * q + 3 →
        ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y8' : Mix (Lambda, Pi) := Y8 h_le hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * p + 3) .Positive = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_pos] at h; exact h
  have hgk_eq : Gene.ofRank (2 * q + 3) .Positive = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_pos] at h; exact h
  have hX8_val : (X8 h_le hε).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X8_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X8 h_le hε).1 + restval = X.1.1 := by
    rw [hX8_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Lambda, Pi) := ⟨Y8'.1 + restval, add_mem Y8'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X8 h_le hε : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X8 h_le hε) Y8' rest_M
      (MixLambdaPi.Primitive.type8 GeneType.Positive hε h_le), ?_⟩
  change Y8'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X8 h_le hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * p + 1
  · have h88 : signature (Chromosome.prime^[j] Y8'.1) =
        signature (Chromosome.prime^[j] (X8 h_le hε).1) :=
      (sigma_type8_eq_before h_le hε (hj := hj)).symm
    rw [h88, ← hdecomp]; exact hXYj
  · by_cases hj_after : 2 * q + 5 ≤ j
    · have h88 : signature (Chromosome.prime^[j] Y8'.1) =
          signature (Chromosome.prime^[j] (X8 h_le hε).1) :=
        (sigma_type8_eq_after h_le hε (hj := hj_after)).symm
      rw [h88, ← hdecomp]; exact hXYj
    · have hj1 : 2 * p + 1 < j := by omega
      have hj2 : j < 2 * q + 5 := by omega
      have hmid := sigma_type8_mid h_le hε hj1 hj2
      have hY8_eq : signature (Chromosome.prime^[j] Y8'.1) =
          signature (Chromosome.prime^[j] (X8 h_le hε).1) +
            ((if j ≤ 2 * q + 3 then (1, 1) else signature (Gene.ofRank 1 GeneType.Positive)) +
             (if 2 * p + 3 ≤ j then 0 else -signature (Gene.ofRank 1 GeneType.Positive))) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY8_eq, add_right_comm, ← hdecomp]
      rw [signature_ofRank_one_positive]
      by_cases hbot : 2 * p + 3 ≤ j
      · rw [if_pos hbot, add_zero]
        by_cases htop : j ≤ 2 * q + 3
        · rw [if_pos htop]
          -- deep interior `(1,1)`: even by `haeven`+`hbeven`, odd by `hoddabsorb`
          by_cases hpar : Even j
          · refine ⟨?_, ?_⟩
            · simp only [Prod.fst_add]
              have := haeven j hpar hbot (by omega)
              simpa [Sigma.sigma] using this
            · simp only [Prod.snd_add]
              have := hbeven j hpar hbot htop
              simpa [Sigma.sigma] using this
          · have hodd : Odd j := Nat.not_even_iff_odd.mp hpar
            have hab := hoddabsorb j hodd hbot htop
            rw [add_comm]
            simpa [Sigma.sigma] using hab
        · -- top boundary `j = 2q+4`: difference `(1,0)`
          rw [if_neg htop]
          have hjeq : j = 2 * q + 4 := by omega
          have hjeven : Even j := ⟨q + 2, by omega⟩
          refine ⟨?_, ?_⟩
          · simp only [Prod.fst_add]
            have := haeven j hjeven hbot (by omega)
            simpa [Sigma.sigma] using this
          · simp only [Prod.snd_add, add_zero]; exact hXYj.2
      · -- bottom boundary `j = 2p+2`: difference `(0,1)`
        rw [if_neg hbot]
        have htop : j ≤ 2 * q + 3 := by omega
        rw [if_pos htop,
          show ((1:ℚ),(1:ℚ)) + (-((1:ℚ),(0:ℚ))) = ((0:ℚ),(1:ℚ)) from by norm_num]
        have hjeq : j = 2 * p + 2 := by omega
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add]; rw [add_zero]; exact hXYj.1
        · simp only [Prod.snd_add]
          rw [hjeq]
          have hb := hbanchor
          rw [Sigma.sigma, Sigma.sigma] at hb
          linarith [hb]

/-- §16 Branch B, **Case 3** (`g₁ = g⁺(m)`, `m = 2m'+1 ≥ 3`).  Dispatch:
`2g₁` diagonal (type8) or second gene `g₂` by charge (type6/type7/type8).

The type6 (`g₂` nonpolarized) and type7 (`g₂ = g⁻`) charges are fully proved via
`branchB_case5_aprop_gen` + the general-`m'` assemblies above.  The `2g₁` diagonal
and the type8 (`g₂ = g⁺`) charge need the deep-interior `(1,1)` window absorption
(odd-level integer gap) and are isolated as `sorry`. -/
lemma branchB_case3 (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁pos : g₁.type = .Positive)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 1) (hmpos : 0 < m') :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hmult : 2 ≤ X.1.1 g₁
  · -- `X ⊇ 2g₁`: type8 diagonal `2g⁺(m) → g⁺(m-2) + g⁺(m+2)`.  Needs deep-interior
    -- `(1,1)` absorption (odd-level integer gap).
    sorry
  · -- second gene `g₂` of minimal rank
    obtain ⟨g0, hg0mem, hg0np⟩ := branchB_case5_exists_negNP X Y hXY ha
    have hg0ne : g0 ≠ g₁ := fun h => hg0np (h ▸ hg₁pos)
    obtain ⟨g₂, hg₂mem, hg₂minS⟩ := Finset.exists_min_image
      (X.1.1.support.filter (fun g => g ≠ g₁)) Gene.rank
      ⟨g0, Finset.mem_filter.mpr ⟨hg0mem, hg0ne⟩⟩
    rw [Finset.mem_filter] at hg₂mem
    obtain ⟨hg₂supp, hg₂ne⟩ := hg₂mem
    have hXg₂' : 0 < X.1.1 g₂ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂supp)
    -- minimality among non-`g₁` genes
    have hk2 : ∀ g ∈ X.1.1.support, g ≠ g₁ → g₂.rank ≤ g.rank :=
      fun g hg hgne => hg₂minS g (Finset.mem_filter.mpr ⟨hg, hgne⟩)
    -- neg/NP genes (≠ g₁ since g₁ positive) dominate `g₂`
    have hkprop : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → g₂.rank ≤ g.rank :=
      fun g hg hgnp => hk2 g hg (fun he => hgnp (he ▸ hg₁pos))
    have hne : g₁ ≠ g₂ := fun h => hg₂ne h.symm
    have hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]; exact hXg₂'
    have hm1 : g₁.rank = 2 * m' + 1 := hm'
    cases hch : g₂.type with
    | NonPolarized =>
      have hev : Even g₂.rank := rank_even_of_nonpolarized_mem X.1.2 hch hXg₂'
      obtain ⟨n', hn'⟩ : ∃ n', g₂.rank = 2 * n' + 2 := by
        have hge : 2 * m' + 1 ≤ g₂.rank := by have := hg₁min g₂ hg₂supp; omega
        obtain ⟨t, ht⟩ := hev; exact ⟨t - 1, by omega⟩
      have hmn : m' ≤ n' := by have := hg₁min g₂ hg₂supp; omega
      have hpropk := branchB_case5_aprop_gen X Y hXY ha g₂.rank hkprop
      rw [hn'] at hpropk
      have hYwin : ∀ j, 1 ≤ j → j < 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0 :=
        fun j _ hj => Ywin_below X Y hXY g₂ hXg₂' (by rw [hn']; omega)
      exact branchB_case3_assembly_type6 X Y hXY hsigeq m' n' hmn g₁ g₂ hm1 hg₁pos hn' hch
        hXg₁ hXg₂ hne hpropk hYwin
    | Negative =>
      have hodd : Odd g₂.rank :=
        rank_odd_of_polarized X.1.2 (by rw [hch]; decide) hXg₂'
      obtain ⟨n', hn'⟩ : ∃ n', g₂.rank = 2 * n' + 1 := by
        obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
      have hmn : m' ≤ n' := by have := hg₁min g₂ hg₂supp; omega
      have hpropk := branchB_case5_aprop_gen X Y hXY ha g₂.rank hkprop
      rw [hn'] at hpropk
      have hprop : ∀ j, 2 ≤ j → j ≤ 2 * n' → Even j →
          (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 :=
        fun j hj2 hjle hje => hpropk j hj2 (by omega) hje
      have hYwin : ∀ j, 1 ≤ j → j ≤ 2 * n' + 1 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
        intro j hj1 hj2
        rcases Nat.lt_or_ge j (2 * n' + 1) with hjlt | hjge
        · exact Ywin_below X Y hXY g₂ hXg₂' (by rw [hn']; omega)
        · -- j = 2n'+1 = g₂.rank: top boundary (gk = g⁻); b-mirror of Case 2 boundary
          have hjeq : j = 2 * n' + 1 := by omega
          rw [hjeq]
          exact branchB_case5_Ynonzero_top X Y hXY hcommon n' g₂ hn' hch hXg₂'
      exact branchB_case3_assembly_type7 X Y hXY hsigeq m' n' hmn g₁ g₂ hm1 hg₁pos hn' hch
        hXg₁ hXg₂ hne hprop hYwin
    | Positive =>
      -- `g₂ = g⁺(k)`: type8 `g⁺(m) + g⁺(k) → g⁺(m-2) + g⁺(k+2)`.  Needs deep-interior
      -- `(1,1)` absorption (odd-level integer gap).
      sorry

end MixLambdaPi
