import YoungDiagram.Theorem6.MixPiLambda.CaseAProp
import YoungDiagram.Theorem6.MixPiLambda.CaseProp5

/-!
# §16 Case A Branch A: the `g₃` sub-case assemblies for `Mix (Pi, Lambda)`.

This is the PL-specific `m = 1`, `b₁ = d₁` sub-case of §16 Case 2.  Here `g₁ = g(1)` is the
minimal (odd-rank) nonpolarized gene, `g₂ = g⁺(2n'+2)` is the minimal gene of `X - g₁`, and
`X - g₁ - g₂` contains a negative or nonpolarized gene `g₃` of minimal rank `t`.  The
mutation `g₂ + g₃ → g(2n'+1) + g(t+1)` (`t` even, `type7`) or
`g₂ + g₃ → g(2n'+1) + g⁺(t+1)` (`t` odd, `type6`) gives `Z ≤ Y`, using the level-1-anchored
`a`-propagation `branchA_g3_aprop` (odd `j`) and `half_le_sigma_diff_at_r` (even `j`).
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- `prime^[j] Y ≠ 0` for `j` below the rank of any gene of `X` (via dominance). -/
lemma Ywin_below_pl {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1) (gk : Gene)
    (hgk : 0 < X.1.1 gk) {j : ℕ} (hj : j < gk.rank) : Chromosome.prime^[j] Y.1.1 ≠ 0 := by
  intro hYzero
  have hXj : Chromosome.prime^[j] X.1.1 ≠ 0 := by
    intro hXzero
    have hle := prime_iterate_eq_zero_rank_le.mpr hXzero gk
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgk))
    omega
  have hsig := le_iff_dominates.mp hXY.le j
  rw [hYzero, map_zero] at hsig
  exact hXj (signature_eq_zero (le_antisymm hsig (signature_nonneg _)))

/-- **§16 g₃ existence**: when `g₁ = g(1)` and `g₂ = g⁺(2n'+2)` are the two minimal genes and
`a₁ < c₁` (`ha`), the remainder `X - g₁ - g₂` contains a negative or nonpolarized gene.
Otherwise every non-positive gene of `X` is `g₁` (rank `1`), and the `a`-propagation
`branchA_g3_aprop` forces `1 ≤ 0` at a level beyond `maxRank`. -/
lemma branchA_g3_exists {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ g₂ : Gene) (hg₁NP : g₁.type = .NonPolarized) (hg₁rank : g₁.rank = 1)
    (hmult1 : X.1.1 g₁ = 1) (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₂pos : g₂.type = .Positive) :
    ∃ g₃ ∈ (X.1.1 - Finsupp.single g₁ 1 - Finsupp.single g₂ 1).support,
      g₃.type ≠ .Positive := by
  by_contra hcon
  push_neg at hcon
  have hpar : ∀ g ∈ X.1.1.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank) := by
    intro g hg
    have hgpos : 0 < X.1.1 g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    exact ⟨fun hp => rank_even_of_polarized X.1.2 (by rw [hp]; decide) hgpos,
           fun hn => rank_even_of_polarized X.1.2 (by rw [hn]; decide) hgpos⟩
  have hk : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → (g.rank ≤ 1 ∨ (2 * N + 3) ≤ g.rank) := by
    intro g hg hgnp
    left
    have hgg₁ : g = g₁ := by
      by_contra hne
      by_cases hgg₂ : g = g₂
      · exact hgnp (hgg₂ ▸ hg₂pos)
      · have hpos : 0 < (X.1.1 - Finsupp.single g₁ 1 - Finsupp.single g₂ 1 : Chromosome) g := by
          rw [Finsupp.tsub_apply, Finsupp.tsub_apply,
            Finsupp.single_apply, if_neg (Ne.symm hne),
            Finsupp.single_apply, if_neg (Ne.symm hgg₂), Nat.sub_zero, Nat.sub_zero]
          exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
        exact hgnp (hcon g (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hpos)))
    rw [hgg₁, hg₁rank]
  have hprop := branchA_g3_aprop X Y hXY ha g₁ hg₁NP hg₁rank hmult1 hg₁min hpar (2 * N + 3) hk
    (2 * N + 3) ⟨N + 1, by ring⟩ (le_refl _)
  have hzero : ∀ Z : nMixPiLambda N, Chromosome.prime^[2 * N + 3] Z.1.1 = 0 := by
    intro Z
    apply prime_iterate_zero_of_maxRank_le
    have h2 := maxRank_le_rank Z.1.1
    rw [Z.2] at h2
    exact le_trans h2 (by omega)
  rw [show Sigma.sigma X.1.1 (2 * N + 3) =
        signature (Chromosome.prime^[2 * N + 3] X.1.1) from rfl,
    show Sigma.sigma Y.1.1 (2 * N + 3) =
        signature (Chromosome.prime^[2 * N + 3] Y.1.1) from rfl,
    hzero X, hzero Y, map_zero] at hprop
  simp only [Prod.fst_zero, zero_add] at hprop
  exact absurd hprop (by norm_num)

/-- Mirror of `one_le_signature_fst_of_contains_positive_mix` for the `b`-component:
a negative gene `g⁻(r)` forces `1 ≤ b`-signature at level `r - 1`. -/
lemma one_le_signature_snd_of_contains_negative_mix {X : Chromosome}
    {gneg : Gene} (hgneg : gneg.type = .Negative) (hXgneg : 0 < X gneg) :
    1 ≤ (signature (Chromosome.prime^[gneg.rank - 1] X)).2 := by
  let r := gneg.rank
  have hr : 1 ≤ r := gneg.rank_pos
  have hgneg_single : Gene.ofRank r .Negative = (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rw [hgneg] at h
    exact h
  have hprime_gneg : Chromosome.prime^[r - 1] (Finsupp.single gneg 1 : Chromosome) =
      Gene.ofRank 1 .Negative := by
    rw [← hgneg_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
  have hXeq : X = Finsupp.single gneg 1 + (X - Finsupp.single gneg 1) := by
    rw [add_comm, sub_single_add_single_eq hXgneg]
  calc (1 : ℚ)
      = (signature (Gene.ofRank 1 .Negative : Chromosome)).2 := by
        simp [signature_ofRank_one_negative]
    _ = (signature (Chromosome.prime^[r - 1] (Finsupp.single gneg 1 : Chromosome))).2 := by
        rw [hprime_gneg]
    _ ≤ (signature (Chromosome.prime^[r - 1] X)).2 := by
        conv_rhs => rw [hXeq]
        rw [iterate_map_add, map_add]
        exact le_add_of_nonneg_right (signature_nonneg _).2

/-- **§16 g₃ top boundary** (`type7`, `Mix (Pi, Lambda)`).  With `g₃ = g⁻(2nn+2)` a negative
gene of `X` (disjoint from `Y`) and `t = 2nn+2` even, `prime^[t] Y ≠ 0`: otherwise the level
`t-1` survivors of `Y` would all sit at rank `1` and, being neither `g⁻(t)` (disjoint) nor
`NP(t)` (even rank), contribute `0` to the `b`-component, contradicting the `b`-bound from
`g₃`. -/
lemma branchA_g3_Ynonzero_top {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (nn : ℕ) (g₃ : Gene) (hg₃_rank : g₃.rank = 2 * nn + 2)
    (hg₃_neg : g₃.type = .Negative) (hXg₃ : 0 < X.1.1 g₃) :
    Chromosome.prime^[2 * nn + 2] Y.1.1 ≠ 0 := by
  push_neg at hcommon
  intro hYzero
  have hbX : 1 ≤ (signature (Chromosome.prime^[2 * nn + 1] X.1.1)).2 := by
    have := one_le_signature_snd_of_contains_negative_mix hg₃_neg hXg₃
    rwa [hg₃_rank, show 2 * nn + 2 - 1 = 2 * nn + 1 from by omega] at this
  have hbY : 1 ≤ (signature (Chromosome.prime^[2 * nn + 1] Y.1.1)).2 :=
    le_trans hbX (le_iff_dominates.mp hXY.le (2 * nn + 1)).2
  set W := Chromosome.prime^[2 * nn + 1] Y.1.1 with hWdef
  have hWprime : Chromosome.prime W = 0 := by
    rw [hWdef, ← Function.iterate_succ_apply' Chromosome.prime (2 * nn + 1) Y.1.1]
    exact hYzero
  have hWmem : W ∈ Mix (Lambda, Pi) := by
    have hodd : ¬ Even (2 * nn + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨nn, by ring⟩
    have h := prime_mem_Mix_Pi_Lambda_iterate Y.1.2 (2 * nn + 1)
    rwa [if_neg hodd] at h
  have hWgenes : ∀ h ∈ W.support, h.signature.2 = 0 := by
    intro h hh
    have hr1 : h.rank = 1 := rank_one_of_prime_eq_zero hWprime hh
    -- `h` is polarized: `W ∈ Mix (Lambda, Pi)`, so its rank-1 (odd) part lies in `Pi`.
    have hpol : h.type ≠ .NonPolarized := by
      have hod : 0 < W.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos (by rw [hr1]; exact ⟨0, rfl⟩)]
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      exact IsPolarized_def'.mp (mem_Pi_iff.mp hWmem.2) h
        (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hod))
    -- `h` is not negative: a `g⁻(1)` in `W` would correspond to `g⁻(t) = g₃ ∈ Y`, excluded.
    have hnneg : h.type ≠ .Negative := by
      intro hneg
      have hWh : W h = Y.1.1 ⟨h.rank + (2 * nn + 1), h.type,
          Nat.le_add_right_of_le h.rank_pos⟩ := prime_iterate_coeff (2 * nn + 1) Y.1.1 h
      have hge : (⟨h.rank + (2 * nn + 1), h.type,
          Nat.le_add_right_of_le h.rank_pos⟩ : Gene) = g₃ :=
        Gene.ext (by show h.rank + (2 * nn + 1) = g₃.rank; rw [hg₃_rank]; omega)
          (by show h.type = g₃.type; rw [hneg, hg₃_neg])
      rw [hge] at hWh
      have hYg₃ : Y.1.1 g₃ = 0 := Nat.le_zero.mp (hcommon g₃ hXg₃)
      rw [hYg₃] at hWh
      exact (Finsupp.mem_support_iff.mp hh) hWh
    -- so `h` is positive, with `b`-signature `0`.
    have hpos : h.type = .Positive := by
      cases ht : h.type with
      | NonPolarized => exact absurd ht hpol
      | Positive => rfl
      | Negative => exact absurd ht hnneg
    rw [Gene.signature_of_positive hpos, if_neg (by rw [hr1]; decide)]
    simp [hr1]
  have hW0 : (signature W).2 = 0 := by
    rw [signature_snd, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro h hh
    rw [hWgenes h hh, smul_zero]
  rw [hW0] at hbY
  linarith

/-- **§16 g₃ assembly, `t` odd (`type6`)**: `g₂ + g₃ → g(2n'+1) + g⁺(t+1)`, with `g₂ = g⁺(2n'+2)`
and `g₃ = NP(2nn+3)`.  Odd levels absorb the `(1,0)` boost via the `a`-propagation; even levels
absorb the `(1/2,1/2)` via `half_le_sigma_diff_at_r`. -/
lemma branchA_g3_assembly_type6 {N : ℕ}
    (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (n' nn : ℕ) (hmn : n' ≤ nn)
    (g₂ g₃ : Gene)
    (hg₂_rank : g₂.rank = 2 * n' + 2) (hg₂_pos : g₂.type = .Positive)
    (hg₃_rank : g₃.rank = 2 * nn + 3) (hg₃_np : g₃.type = .NonPolarized)
    (hXg₂ : 0 < X.1.1 g₂)
    (hXg₃ : 0 < (X.1.1 - Finsupp.single g₂ 1 : Chromosome) g₃)
    (hne : g₂ ≠ g₃)
    (hprop_odd : ∀ j, 2 * n' + 1 ≤ j → j ≤ 2 * nn + 3 → Odd j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 2 * n' + 1 ≤ j → j < 2 * nn + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  push_neg at hsigeq
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y6' : Mix (Pi, Lambda) := Y6 hmn hε
  let restval : Chromosome := X.1.1 - Finsupp.single g₂ 1 - Finsupp.single g₃ 1
  have rest_mem : restval ∈ Mix (Pi, Lambda) :=
    sub_mem_Mix_Pi_Lambda _ (sub_mem_Mix_Pi_Lambda _ X.1.2)
  let rest_M : Mix (Pi, Lambda) := ⟨restval, rest_mem⟩
  have hg₂_eq : Gene.ofRank (2 * n' + 2) .Positive = (Finsupp.single g₂ 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g₂); rw [hg₂_rank, hg₂_pos] at h; exact h
  have hg₃_eq : Gene.ofRank (2 * nn + 3) .NonPolarized = (Finsupp.single g₃ 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g₃); rw [hg₃_rank, hg₃_np] at h; exact h
  have hX6_val : (X6 hmn hε).1 = Finsupp.single g₂ 1 + Finsupp.single g₃ 1 := by
    rw [X6_eq, hg₂_eq, hg₃_eq]
  have hXg₃' : 0 < X.1.1 g₃ := by
    have hval : (X.1.1 - Finsupp.single g₂ 1 : Chromosome) g₃ = X.1.1 g₃ := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXg₃
  have hX_eq : (X6 hmn hε).1 + restval = X.1.1 := by
    rw [hX6_val]; exact X_eq_X7_add_rest_mix hXg₂ hXg₃' hne
  let Z : Mix (Pi, Lambda) := ⟨Y6'.1 + restval, add_mem Y6'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X6 hmn hε : Mix (Pi, Lambda)) + rest_M = X.1) ▸
    MixPiLambda.Step.mk (X6 hmn hε) Y6' rest_M
      (MixPiLambda.Primitive.type6 GeneType.Positive hε hmn), ?_⟩
  change Y6'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X6 hmn hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * n' + 1
  · have h64 : signature (Chromosome.prime^[j] Y6'.1) =
        signature (Chromosome.prime^[j] (X6 hmn hε).1) :=
      (sigma_type6_eq_before hmn hε (hj := hj)).symm
    rw [h64, ← hdecomp]; exact hXYj
  · have h_not_before : 2 * n' + 1 < j := by omega
    by_cases hj_after : 2 * nn + 4 ≤ j
    · have h64 : signature (Chromosome.prime^[j] Y6'.1) =
          signature (Chromosome.prime^[j] (X6 hmn hε).1) :=
        (sigma_type6_eq_after hmn hε (hj := hj_after)).symm
      rw [h64, ← hdecomp]; exact hXYj
    · have h_mid : j < 2 * nn + 4 := by omega
      have hmid := sigma_type6_mid hmn hε h_not_before h_mid
      have hY6_eq : signature (Chromosome.prime^[j] Y6'.1) =
          signature (Chromosome.prime^[j] (X6 hmn hε).1) +
            (if Even (2 * nn + 3 - j) then signature (Gene.ofRank 1 GeneType.Positive)
             else ((1 : ℚ) / 2, (1 : ℚ) / 2)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY6_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * nn + 3 - j)
      · rw [if_pos hpar]
        have hodd_j : Odd j := by
          have hp : (2 * nn + 3 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.odd_iff]; omega
        rw [signature_ofRank_one_positive]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have h_sigma := hprop_odd j (by omega) (by omega) hodd_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · show (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · show (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          rw [add_zero]; exact hXYj.2
      · rw [if_neg hpar]
        have heven_j : Even j := by
          have hp : (2 * nn + 3 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.even_iff]; omega
        have hne' : signature (Chromosome.prime^[j] X.1.1) ≠
            signature (Chromosome.prime^[j] Y.1.1) := by
          intro h_eq
          exact hsigeq j (by omega) (hYwin j (by omega) (by obtain ⟨t, ht⟩ := heven_j; omega))
            (by simpa [Sigma.sigma] using h_eq)
        rw [add_comm]
        exact half_le_sigma_diff_at_r X.1.2 Y.1.2 heven_j hXYj hne'

/-- **§16 g₃ assembly, `t` even (`type7`)**: `g₂ + g₃ → g(2n'+1) + g(t+1)`, with `g₂ = g⁺(2n'+2)`
and `g₃ = g⁻(2nn+2)`.  Odd levels absorb the `(1,0)` via the `a`-propagation; even levels
(including the top `j = t`, gated by `hYwin`) absorb `(1/2,1/2)` via `half_le_sigma_diff_at_r`. -/
lemma branchA_g3_assembly_type7 {N : ℕ}
    (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (n' nn : ℕ) (hmn : n' ≤ nn)
    (g₂ g₃ : Gene)
    (hg₂_rank : g₂.rank = 2 * n' + 2) (hg₂_pos : g₂.type = .Positive)
    (hg₃_rank : g₃.rank = 2 * nn + 2) (hg₃_neg : g₃.type = .Negative)
    (hXg₂ : 0 < X.1.1 g₂)
    (hXg₃ : 0 < (X.1.1 - Finsupp.single g₂ 1 : Chromosome) g₃)
    (hne : g₂ ≠ g₃)
    (hprop_odd : ∀ j, 2 * n' + 1 ≤ j → j ≤ 2 * nn + 1 → Odd j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 2 * n' + 1 ≤ j → j ≤ 2 * nn + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  push_neg at hsigeq
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y7' : Mix (Pi, Lambda) := Y7 hmn
  let restval : Chromosome := X.1.1 - Finsupp.single g₂ 1 - Finsupp.single g₃ 1
  have rest_mem : restval ∈ Mix (Pi, Lambda) :=
    sub_mem_Mix_Pi_Lambda _ (sub_mem_Mix_Pi_Lambda _ X.1.2)
  let rest_M : Mix (Pi, Lambda) := ⟨restval, rest_mem⟩
  have hg₂_eq : Gene.ofRank (2 * n' + 2) .Positive = (Finsupp.single g₂ 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g₂); rw [hg₂_rank, hg₂_pos] at h; exact h
  have hg₃_eq : Gene.ofRank (2 * nn + 2) .Negative = (Finsupp.single g₃ 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g₃); rw [hg₃_rank, hg₃_neg] at h; exact h
  have hX7_val : (X7 hmn hε).1 = Finsupp.single g₂ 1 + Finsupp.single g₃ 1 := by
    rw [X7_eq, GeneType.neg_positive, hg₂_eq, hg₃_eq]
  have hXg₃' : 0 < X.1.1 g₃ := by
    have hval : (X.1.1 - Finsupp.single g₂ 1 : Chromosome) g₃ = X.1.1 g₃ := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXg₃
  have hX_eq : (X7 hmn hε).1 + restval = X.1.1 := by
    rw [hX7_val]; exact X_eq_X7_add_rest_mix hXg₂ hXg₃' hne
  let Z : Mix (Pi, Lambda) := ⟨Y7'.1 + restval, add_mem Y7'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X7 hmn hε : Mix (Pi, Lambda)) + rest_M = X.1) ▸
    MixPiLambda.Step.mk (X7 hmn hε) Y7' rest_M
      (MixPiLambda.Primitive.type7 GeneType.Positive hε hmn), ?_⟩
  change Y7'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X7 hmn hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * n' + 1
  · have h74 : signature (Chromosome.prime^[j] Y7'.1) =
        signature (Chromosome.prime^[j] (X7 hmn hε).1) :=
      (sigma_type7_eq_before hmn hε (hj := hj)).symm
    rw [h74, ← hdecomp]; exact hXYj
  · have h_not_before : 2 * n' + 1 < j := by omega
    by_cases hj_after : 2 * nn + 3 ≤ j
    · have h74 : signature (Chromosome.prime^[j] Y7'.1) =
          signature (Chromosome.prime^[j] (X7 hmn hε).1) :=
        (sigma_type7_eq_after hmn hε (hj := hj_after)).symm
      rw [h74, ← hdecomp]; exact hXYj
    · have h_mid : j < 2 * nn + 3 := by omega
      have hmid := sigma_type7_mid hmn hε h_not_before h_mid
      have hY7_eq : signature (Chromosome.prime^[j] Y7'.1) =
          signature (Chromosome.prime^[j] (X7 hmn hε).1) +
            (if Even (2 * nn + 2 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
             else signature (Gene.ofRank 1 GeneType.Positive)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY7_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * nn + 2 - j)
      · rw [if_pos hpar]
        have heven_j : Even j := by
          have hp : (2 * nn + 2 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.even_iff]; omega
        have hne' : signature (Chromosome.prime^[j] X.1.1) ≠
            signature (Chromosome.prime^[j] Y.1.1) := by
          intro h_eq
          exact hsigeq j (by omega) (hYwin j (by omega) (by obtain ⟨t, ht⟩ := heven_j; omega))
            (by simpa [Sigma.sigma] using h_eq)
        rw [add_comm]
        exact half_le_sigma_diff_at_r X.1.2 Y.1.2 heven_j hXYj hne'
      · rw [if_neg hpar]
        have hodd_j : Odd j := by
          have hp : (2 * nn + 2 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.odd_iff]; omega
        rw [signature_ofRank_one_positive]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have hjle : j ≤ 2 * nn + 1 := by rcases hodd_j with ⟨t, rfl⟩; omega
          have h_sigma := hprop_odd j (by omega) hjle hodd_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · show (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · show (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          rw [add_zero]; exact hXYj.2

end MixPiLambda
