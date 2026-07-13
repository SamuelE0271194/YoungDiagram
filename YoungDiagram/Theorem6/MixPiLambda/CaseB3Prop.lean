import YoungDiagram.Theorem6.MixPiLambda.CaseB

/-!
# §16 Case 3 type8 machinery for `Mix (Pi, Lambda)` (label 2).

Parity-mirror of the `MixLambdaPi/CaseBProp.lean` + `CaseB3.lean` type8 lemmas.  For
`Mix (Pi, Lambda)` the symmetric levels are EVEN (so the `(1,1)` deep-interior absorption is
parity-free at even `j`, and needs `a`- and `b`-propagation at odd `j`).  The `|Y| < |X|`
comparison is obtained from the self-dual rank gap (`rank_gap_one`) rather than level-1
symmetry.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- **Even-interior `(1,1)` absorption (parity-free).**  At even `j`, `Mix (Pi, Lambda)` has
`a = b`, so `rank = 2a`.  Given the odd-neighbor gaps `a_X(j-1)+1 ≤ a_Y(j-1)` and
`b_X(j-1)+1 ≤ b_Y(j-1)` (rank gap at `j-1` is `≥ 2`) and the alive-count comparison (`X`'s
rank-drop `≥ Y`'s at `j-1`), the rank gap at `j` is `≥ 2`, which halves to a full `(1,1)`. -/
lemma even_interior_absorb_neighbor {X Y : Chromosome}
    (hX : X ∈ Mix (Pi, Lambda)) (hY : Y ∈ Mix (Pi, Lambda)) {j : ℕ} (heven : Even j)
    (haodd : (Sigma.sigma X (j - 1)).1 + 1 ≤ (Sigma.sigma Y (j - 1)).1)
    (hbodd : (Sigma.sigma X (j - 1)).2 + 1 ≤ (Sigma.sigma Y (j - 1)).2)
    (halive : ((Sigma.sigma Y (j - 1)).1 + (Sigma.sigma Y (j - 1)).2) -
        ((Sigma.sigma Y j).1 + (Sigma.sigma Y j).2) ≤
        ((Sigma.sigma X (j - 1)).1 + (Sigma.sigma X (j - 1)).2) -
        ((Sigma.sigma X j).1 + (Sigma.sigma X j).2)) :
    ((1 : ℚ), (1 : ℚ)) + Sigma.sigma X j ≤ Sigma.sigma Y j := by
  have hXsym : (Sigma.sigma X j).1 = (Sigma.sigma X j).2 :=
    signature_prime_iterate_even_eq_components hX heven
  have hYsym : (Sigma.sigma Y j).1 = (Sigma.sigma Y j).2 :=
    signature_prime_iterate_even_eq_components hY heven
  constructor
  · simp only [Prod.fst_add]; linarith [haodd, hbodd, halive, hXsym, hYsym]
  · simp only [Prod.snd_add]; linarith [haodd, hbodd, halive, hXsym, hYsym]

/-- The total multiplicity of `prime^[i] Z` equals the total multiplicity of `Z`'s genes
of rank `> i` (those surviving `i` applications of `prime`). -/
lemma prime_iterate_sum_eq (Z : Chromosome) (i : ℕ) :
    (Chromosome.prime^[i] Z).sum (fun _ m => (m : ℚ)) =
      ∑ g ∈ Z.support.filter (fun g => i < g.rank), (Z g : ℚ) := by
  rw [Finsupp.sum]
  refine Finset.sum_bij'
    (fun g _ => (⟨g.rank + i, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
    (fun h hh => (⟨h.rank - i, h.type, by
      have := (Finset.mem_filter.mp hh).2; omega⟩ : Gene)) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rw [Finsupp.mem_support_iff] at hg
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨by rwa [← prime_iterate_coeff], by change i < g.rank + i; have := g.rank_pos; omega⟩
  · intro h hh
    rw [Finset.mem_filter, Finsupp.mem_support_iff] at hh
    rw [Finsupp.mem_support_iff, prime_iterate_coeff]
    have hle : i ≤ h.rank := le_of_lt hh.2
    convert hh.1 using 2
    exact Gene.ext (by change h.rank - i + i = h.rank; omega) rfl
  · intro g _; exact Gene.ext (by change g.rank + i - i = g.rank; omega) rfl
  · intro h hh
    have hle : i ≤ h.rank := le_of_lt (Finset.mem_filter.mp hh).2
    exact Gene.ext (by change h.rank - i + i = h.rank; omega) rfl
  · intro g _; rw [prime_iterate_coeff]

/-- **Alive-count comparison for §16 Case 3 type8** (`Mix (Pi, Lambda)`).  For `i + 1 ≤ k`,
`Y`'s rank-drop at level `i` is `≤` `X`'s: `Y`'s drop `≤ |Y| < |X| = |X-g₁| + 1`, while `X`'s
drop `≥ |X-g₁|`.  `|Y| < |X|` comes from the self-dual rank gap (`ha` + dominance), not
level-1 symmetry. -/
lemma branchB_case3_halive {N : ℕ} (X Y : nMixPiLambda N) (_ : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (g₁ : Gene) (hg₁mult : 1 ≤ X.1.1 g₁)
    (k : ℕ) (htail : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, k ≤ g.rank) :
    ∀ i, i + 1 ≤ k →
      ((Sigma.sigma Y.1.1 i).1 + (Sigma.sigma Y.1.1 i).2) -
          ((Sigma.sigma Y.1.1 (i + 1)).1 + (Sigma.sigma Y.1.1 (i + 1)).2) ≤
        ((Sigma.sigma X.1.1 i).1 + (Sigma.sigma X.1.1 i).2) -
          ((Sigma.sigma X.1.1 (i + 1)).1 + (Sigma.sigma X.1.1 (i + 1)).2) := by
  set X' : Chromosome := X.1.1 - Finsupp.single g₁ 1 with hX'def
  have hXadd : X.1.1 = X' + Finsupp.single g₁ 1 := by
    rw [hX'def]; ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : g₁ = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  have hcellsX : X.1.1.sum (fun _ m => (m : ℚ)) = X'.sum (fun _ m => (m : ℚ)) + 1 := by
    conv_lhs => rw [hXadd]
    rw [Finsupp.sum_add_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_single_index (by simp)]; push_cast; ring
  have hYcells : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
      ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) = Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hXcells : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
      ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) = X.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hrk0 : (X.1.1.rank : ℚ) = (Y.1.1.rank : ℚ) := by rw [X.2, Y.2]
  have hsX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
  have hYleX' : Y.1.1.sum (fun _ m => (m : ℚ)) ≤ X'.sum (fun _ m => (m : ℚ)) := by
    have hlt : Y.1.1.sum (fun _ m => (m : ℚ)) < X.1.1.sum (fun _ m => (m : ℚ)) := by
      rw [← hYcells, ← hXcells]; linarith [hsX0, hsY0, hrk0, hgap]
    rw [hcellsX] at hlt
    have hYn : ∃ n : ℕ, Y.1.1.sum (fun _ m => (m : ℚ)) = (n : ℚ) :=
      ⟨Y.1.1.sum (fun _ m => m), by rw [Finsupp.sum, Finsupp.sum]; push_cast; ring⟩
    have hXn : ∃ n : ℕ, X'.sum (fun _ m => (m : ℚ)) = (n : ℚ) :=
      ⟨X'.sum (fun _ m => m), by rw [Finsupp.sum, Finsupp.sum]; push_cast; ring⟩
    obtain ⟨ny, hny⟩ := hYn; obtain ⟨nx, hnx⟩ := hXn
    rw [hny, hnx] at hlt ⊢; have : ny < nx + 1 := by exact_mod_cast hlt
    exact_mod_cast (by omega : ny ≤ nx)
  intro i hi
  have hYd : (Sigma.sigma Y.1.1 i).1 + (Sigma.sigma Y.1.1 i).2 -
      ((Sigma.sigma Y.1.1 (i + 1)).1 + (Sigma.sigma Y.1.1 (i + 1)).2) ≤
      Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have := rank_drop_le Y.1.2 i; rw [← hYcells]; exact this
  have hX'd : (Sigma.sigma X' i).1 + (Sigma.sigma X' i).2 -
      ((Sigma.sigma X' (i + 1)).1 + (Sigma.sigma X' (i + 1)).2) =
      X'.sum (fun _ m => (m : ℚ)) := by
    have hr0 : (Sigma.sigma X' i).1 + (Sigma.sigma X' i).2 =
        ((Chromosome.prime^[i] X').rank : ℚ) := @signature_sum_eq_rank _
    have hr1 : (Sigma.sigma X' (i + 1)).1 + (Sigma.sigma X' (i + 1)).2 =
        ((Chromosome.prime^[i + 1] X').rank : ℚ) := @signature_sum_eq_rank _
    rw [hr0, hr1, Function.iterate_succ_apply' Chromosome.prime i X']
    rw [cells, prime_iterate_sum_eq,
      Finset.filter_true_of_mem (fun g hg => by have := htail g hg; omega), Finsupp.sum]
  have hsplit : ∀ n, (Sigma.sigma X.1.1 n).1 + (Sigma.sigma X.1.1 n).2 =
      ((Sigma.sigma X' n).1 + (Sigma.sigma X' n).2) +
      ((Sigma.sigma (Finsupp.single g₁ 1) n).1 + (Sigma.sigma (Finsupp.single g₁ 1) n).2) := by
    intro n; conv_lhs => rw [hXadd]
    rw [Sigma.sigma_linearity, Prod.fst_add, Prod.snd_add]; ring
  have hg₁anti : (Sigma.sigma (Finsupp.single g₁ 1) (i + 1)).1 +
      (Sigma.sigma (Finsupp.single g₁ 1) (i + 1)).2 ≤
      (Sigma.sigma (Finsupp.single g₁ 1) i).1 + (Sigma.sigma (Finsupp.single g₁ 1) i).2 := by
    have ha' := (Sigma.antitone (Finsupp.single g₁ 1) (Nat.le_succ i)).1
    have hb' := (Sigma.antitone (Finsupp.single g₁ 1) (Nat.le_succ i)).2
    linarith
  rw [hsplit i, hsplit (i + 1)]
  linarith [hYd, hX'd, hYleX', hg₁anti]

/-- `b`-drop at even index is bounded by the bottom `b`-drop (`Mix (Pi, Lambda)`, via the
two even/odd branches of (15.7)). -/
private lemma bdrop_even_le_pl {Y : Chromosome} (hY : Y ∈ Mix (Pi, Lambda)) (t : ℕ) :
    (Sigma.sigma Y (2 * t)).2 - (Sigma.sigma Y (2 * t + 1)).2 ≤
      (Sigma.sigma Y 0).2 - (Sigma.sigma Y 1).2 := by
  induction t with
  | zero => simp
  | succ k ih =>
    have hodd := cond_15_7_Mix_Pi_Lambda hY (2 * k + 1)
    rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨k, by ring⟩),
      show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show 2 * k + 1 + 2 = 2 * k + 3 from by ring] at hodd
    have heven := cond_15_7_Mix_Pi_Lambda hY (2 * k)
    rw [if_pos ⟨k, by ring⟩] at heven
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
      show 2 * k + 2 + 1 = 2 * k + 3 from by ring]
    linarith

/-- `Y` `b`-component 2-step drop at an odd start bounded by the bottom rank-drop `|Y|`
(`Mix (Pi, Lambda)`). -/
private lemma bdrop_two_step_odd_le_pl {Y : Chromosome} (hY : Y ∈ Mix (Pi, Lambda)) (u : ℕ) :
    (Sigma.sigma Y (2 * u + 1)).2 - (Sigma.sigma Y (2 * u + 3)).2 ≤
      ((Sigma.sigma Y 0).2 - (Sigma.sigma Y 1).2) +
      ((Sigma.sigma Y 0).1 - (Sigma.sigma Y 1).1) := by
  have c6 := cond_15_6_Mix_Pi_Lambda hY (2 * u)
  rw [if_pos ⟨u, by ring⟩] at c6
  have c7o := cond_15_7_Mix_Pi_Lambda hY (2 * u + 1)
  rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨u, by ring⟩),
    show 2 * u + 1 + 1 = 2 * u + 2 from by ring,
    show 2 * u + 1 + 2 = 2 * u + 3 from by ring] at c7o
  have c7e := cond_15_7_Mix_Pi_Lambda hY (2 * u)
  rw [if_pos ⟨u, by ring⟩] at c7e
  have ha2 := adrop_even_le hY u
  have hb2 := bdrop_even_le_pl hY u
  linarith [c6, c7o, c7e, ha2, hb2]

/-- **§16 Case 3 type8 `b`-anchor** (`Mix (Pi, Lambda)`): `b_X(2m'+1) + 1 ≤ b_Y(2m'+1)`.
With `g₁ = g⁺(2m'+2)` minimal (`m' ≥ 1`), `X`'s `b`-2-step drop at `2m'-1` is `|X|` (all genes
survive), `Y`'s is `≤ |Y| < |X|`, so the strict integer gap at the odd level `2m'+1` is `≥ 1`. -/
lemma branchB_case3_banchor_pl {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (m' : ℕ) (hm'pos : 1 ≤ m')
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank) :
    (Sigma.sigma X.1.1 (2 * m' + 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (2 * m' + 1)).2 := by
  -- X b 2-step drop at 2m'-1 = |X|
  have hXtw : (Sigma.sigma X.1.1 (2 * m' - 1)).2 - (Sigma.sigma X.1.1 (2 * m' + 1)).2 =
      X.1.1.sum (fun _ m => (m : ℚ)) := by
    have := twostep_snd (W := X.1.1) (i := 2 * m' - 1)
      (fun g hg => by have := hmin g hg; omega)
    rwa [show 2 * m' - 1 + 2 = 2 * m' + 1 from by omega] at this
  -- Y b 2-step drop at 2m'-1 ≤ |Y|
  have hYcells : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
      ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) = Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hYtw : (Sigma.sigma Y.1.1 (2 * m' - 1)).2 - (Sigma.sigma Y.1.1 (2 * m' + 1)).2 ≤
      Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h := bdrop_two_step_odd_le_pl Y.1.2 (m' - 1)
    rw [show 2 * (m' - 1) + 1 = 2 * m' - 1 from by omega,
      show 2 * (m' - 1) + 3 = 2 * m' + 1 from by omega] at h
    rw [← hYcells]; linarith
  -- |Y| < |X| (rank gap)
  have hXcells : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
      ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) = X.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hrk0 : (X.1.1.rank : ℚ) = (Y.1.1.rank : ℚ) := by rw [X.2, Y.2]
  have hsX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
  have hYltX : Y.1.1.sum (fun _ m => (m : ℚ)) < X.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [← hYcells, ← hXcells]; linarith [hsX0, hsY0, hrk0, hgap]
  have hDom : (Sigma.sigma X.1.1 (2 * m' - 1)).2 ≤ (Sigma.sigma Y.1.1 (2 * m' - 1)).2 :=
    (le_iff_dominates.mp hXY.le (2 * m' - 1)).2
  -- strict, then integrality at the odd level 2m'+1
  have hlt : (Sigma.sigma X.1.1 (2 * m' + 1)).2 < (Sigma.sigma Y.1.1 (2 * m' + 1)).2 := by
    linarith [hXtw, hYtw, hYltX, hDom]
  obtain ⟨zX, hzX⟩ := sig_snd_isInt_odd X.1.2 (show Odd (2 * m' + 1) from ⟨m', by ring⟩)
  obtain ⟨zY, hzY⟩ := sig_snd_isInt_odd Y.1.2 (show Odd (2 * m' + 1) from ⟨m', by ring⟩)
  rw [hzX, hzY] at hlt ⊢
  have hz : zX < zY := by exact_mod_cast hlt
  have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
  linarith

/-- **Deep-interior `b`-propagation for §16 Case 3 type8** (`Mix (Pi, Lambda)`).  Propagates
the odd-level anchor `b_X(2m'+1) + 1 ≤ b_Y(2m'+1)` upward to every odd level
`j = 2m'+1+2t ≤ k`, where `g₁ = g⁺(2m'+2)` is the unique minimal gene (mult 1) and all other
genes have rank `≥ k`.  Parity-mirror of `MixLambdaPi.branchB_case3_deep_bprop`; `|Y| < |X|`
is from the self-dual rank gap. -/
lemma branchB_case3_deep_bprop {N : ℕ} (X Y : nMixPiLambda N) (_ : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (m' : ℕ) (g₁ : Gene) (hg₁mult : 1 ≤ X.1.1 g₁)
    (k : ℕ) (htail : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, k ≤ g.rank)
    (hbanchor : (Sigma.sigma X.1.1 (2 * m' + 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (2 * m' + 1)).2) :
    ∀ t, 2 * m' + 1 + 2 * t ≤ k →
        (Sigma.sigma X.1.1 (2 * m' + 1 + 2 * t)).2 + 1 ≤
          (Sigma.sigma Y.1.1 (2 * m' + 1 + 2 * t)).2 := by
  set X' : Chromosome := X.1.1 - Finsupp.single g₁ 1 with hX'def
  have hXadd : X.1.1 = X' + Finsupp.single g₁ 1 := by
    rw [hX'def]; ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : g₁ = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  set CX' : ℚ := X'.sum (fun _ m => (m : ℚ)) with hCX'def
  have hcellsX : X.1.1.sum (fun _ m => (m : ℚ)) = CX' + 1 := by
    conv_lhs => rw [hXadd]
    rw [Finsupp.sum_add_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_single_index (by simp)]; push_cast; ring
  -- bottom rank-drop facts
  have hYcells : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
      ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) = Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hXcells : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
      ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) = X.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hrk0 : (X.1.1.rank : ℚ) = (Y.1.1.rank : ℚ) := by rw [X.2, Y.2]
  have hsX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
  have hcellsYlt : Y.1.1.sum (fun _ m => (m : ℚ)) ≤ CX' := by
    have hlt : Y.1.1.sum (fun _ m => (m : ℚ)) < X.1.1.sum (fun _ m => (m : ℚ)) := by
      rw [← hYcells, ← hXcells]; linarith [hsX0, hsY0, hrk0, hgap]
    rw [hcellsX] at hlt
    have hYn : ∃ n : ℕ, Y.1.1.sum (fun _ m => (m : ℚ)) = (n : ℚ) :=
      ⟨Y.1.1.sum (fun _ m => m), by rw [Finsupp.sum, Finsupp.sum]; push_cast; ring⟩
    have hXn : ∃ n : ℕ, CX' = (n : ℚ) :=
      ⟨X'.sum (fun _ m => m), by rw [hCX'def, Finsupp.sum, Finsupp.sum]; push_cast; ring⟩
    obtain ⟨ny, hny⟩ := hYn; obtain ⟨nx, hnx⟩ := hXn
    rw [hny, hnx] at hlt ⊢; have : ny < nx + 1 := by exact_mod_cast hlt
    exact_mod_cast (by omega : ny ≤ nx)
  -- Y b 2-step drop (odd start) ≤ |Y|
  have hYdrop : ∀ s, (Sigma.sigma Y.1.1 (2 * m' + 1 + 2 * s)).2 -
      (Sigma.sigma Y.1.1 (2 * m' + 1 + 2 * s + 2)).2 ≤ Y.1.1.sum (fun _ m => (m : ℚ)) := by
    intro s
    set u := m' + s with hu
    have e1 : 2 * m' + 1 + 2 * s + 2 = 2 * u + 3 := by omega
    have e0 : 2 * m' + 1 + 2 * s = 2 * u + 1 := by omega
    rw [e1, e0]
    have c6 := cond_15_6_Mix_Pi_Lambda Y.1.2 (2 * u)
    rw [if_pos ⟨u, by ring⟩] at c6
    have c7o := cond_15_7_Mix_Pi_Lambda Y.1.2 (2 * u + 1)
    rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨u, by ring⟩),
      show 2 * u + 1 + 1 = 2 * u + 2 from by ring,
      show 2 * u + 1 + 2 = 2 * u + 3 from by ring] at c7o
    have c7e := cond_15_7_Mix_Pi_Lambda Y.1.2 (2 * u)
    rw [if_pos ⟨u, by ring⟩] at c7e
    have ha2 := adrop_even_le Y.1.2 u
    have hb2 := bdrop_even_le_pl Y.1.2 u
    have hYc : (Sigma.sigma Y.1.1 0).2 - (Sigma.sigma Y.1.1 1).2 +
        ((Sigma.sigma Y.1.1 0).1 - (Sigma.sigma Y.1.1 1).1) = Y.1.1.sum (fun _ m => (m : ℚ)) := by
      rw [← hYcells]; ring
    -- c6: b(2u+1)-b(2u+2) ≤ a(2u)-a(2u+1); c7o: b(2u+2)-b(2u+3) ≤ a(2u+1)-a(2u+2);
    -- c7e: a(2u+1)-a(2u+2) ≤ b(2u)-b(2u+1); ha2: a(2u)-a(2u+1) ≤ a0-a1; hb2: b(2u)-b(2u+1) ≤ b0-b1
    rw [show 2 * u + 1 + 1 = 2 * u + 2 from by ring] at c6
    linarith [c6, c7o, c7e, ha2, hb2, hYc]
  -- X b 2-step drop (odd start) ≥ CX'
  have hXdrop : ∀ s, 2 * m' + 1 + 2 * s + 2 ≤ k →
      CX' ≤ (Sigma.sigma X.1.1 (2 * m' + 1 + 2 * s)).2 -
        (Sigma.sigma X.1.1 (2 * m' + 1 + 2 * s + 2)).2 := by
    intro s hs
    have htw : (Sigma.sigma X' (2 * m' + 1 + 2 * s)).2 -
        (Sigma.sigma X' (2 * m' + 1 + 2 * s + 2)).2 = CX' :=
      twostep_snd (W := X') (i := 2 * m' + 1 + 2 * s) (fun g hg => le_trans hs (htail g hg))
    have hg₁anti : (Sigma.sigma (Finsupp.single g₁ 1) (2 * m' + 1 + 2 * s + 2)).2 ≤
        (Sigma.sigma (Finsupp.single g₁ 1) (2 * m' + 1 + 2 * s)).2 :=
      (Sigma.antitone (Finsupp.single g₁ 1) (by omega)).2
    have hsplit : ∀ i, (Sigma.sigma X.1.1 i).2 =
        (Sigma.sigma X' i).2 + (Sigma.sigma (Finsupp.single g₁ 1) i).2 := by
      intro i; conv_lhs => rw [hXadd]
      rw [Sigma.sigma_linearity, Prod.snd_add]
    rw [hsplit, hsplit, ← htw]; linarith [hg₁anti]
  intro t
  induction t with
  | zero => intro _; simpa using hbanchor
  | succ s ih =>
    intro hbound
    have hih := ih (by omega)
    have hYd := hYdrop s
    have hXd := hXdrop s (by omega)
    have e2 : 2 * m' + 1 + 2 * (s + 1) = 2 * m' + 1 + 2 * s + 2 := by ring
    rw [e2]
    linarith [hih, hYd, hXd, hcellsYlt]

/-- **Assembly** of §16 Branch B Case 3, `g₂ = g⁺(k)` (type8, `Mix (Pi, Lambda)`).  Builds
`g⁺(m) + g⁺(k) → g⁺(m-2) + g⁺(k+2)` over the window `2p < j < 2q+4`: bottom `j=2p+1` `(0,1)`
by `hbanchor`; deep interior `(1,1)` (even by `hevenabsorb`, odd by `haodd`+`hbodd`); top
`j=2q+3` `(1,0)` by `haodd`. -/
lemma branchB_case3_assembly_type8 {N : ℕ}
    (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (p q : ℕ) (h_le : p ≤ q)
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * p + 2) (hgm_pos : gm.type = .Positive)
    (hgk_rank : gk.rank = 2 * q + 2) (hgk_pos : gk.type = .Positive)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hbanchor : (Sigma.sigma X.1.1 (2 * p + 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (2 * p + 1)).2)
    (haodd : ∀ j, Odd j → 2 * p + 3 ≤ j → j ≤ 2 * q + 3 →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hbodd : ∀ j, Odd j → 2 * p + 3 ≤ j → j ≤ 2 * q + 1 →
        (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2)
    (hevenabsorb : ∀ j, Even j → 2 * p + 2 ≤ j → j ≤ 2 * q + 2 →
        ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y8' : Mix (Pi, Lambda) := Y8 h_le hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Pi, Lambda) :=
    sub_mem_Mix_Pi_Lambda _ (sub_mem_Mix_Pi_Lambda _ X.1.2)
  let rest_M : Mix (Pi, Lambda) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * p + 2) .Positive = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_pos] at h; exact h
  have hgk_eq : Gene.ofRank (2 * q + 2) .Positive = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_pos] at h; exact h
  have hX8_val : (X8 h_le hε).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X8_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X8 h_le hε).1 + restval = X.1.1 := by
    rw [hX8_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Pi, Lambda) := ⟨Y8'.1 + restval, add_mem Y8'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X8 h_le hε : Mix (Pi, Lambda)) + rest_M = X.1) ▸
    MixPiLambda.Step.mk (X8 h_le hε) Y8' rest_M
      (MixPiLambda.Primitive.type8 GeneType.Positive hε h_le), ?_⟩
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
  by_cases hj : j ≤ 2 * p
  · have h88 : signature (Chromosome.prime^[j] Y8'.1) =
        signature (Chromosome.prime^[j] (X8 h_le hε).1) :=
      (sigma_type8_eq_before h_le hε (hj := hj)).symm
    rw [h88, ← hdecomp]; exact hXYj
  · by_cases hj_after : 2 * q + 4 ≤ j
    · have h88 : signature (Chromosome.prime^[j] Y8'.1) =
          signature (Chromosome.prime^[j] (X8 h_le hε).1) :=
        (sigma_type8_eq_after h_le hε (hj := hj_after)).symm
      rw [h88, ← hdecomp]; exact hXYj
    · have hj1 : 2 * p < j := by omega
      have hj2 : j < 2 * q + 4 := by omega
      have hmid := sigma_type8_mid h_le hε hj1 hj2
      have hY8_eq : signature (Chromosome.prime^[j] Y8'.1) =
          signature (Chromosome.prime^[j] (X8 h_le hε).1) +
            ((if j ≤ 2 * q + 2 then (1, 1) else signature (Gene.ofRank 1 GeneType.Positive)) +
             (if 2 * p + 2 ≤ j then 0 else -signature (Gene.ofRank 1 GeneType.Positive))) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY8_eq, add_right_comm, ← hdecomp]
      rw [signature_ofRank_one_positive]
      by_cases hbot : 2 * p + 2 ≤ j
      · rw [if_pos hbot, add_zero]
        by_cases htop : j ≤ 2 * q + 2
        · rw [if_pos htop]
          by_cases hpar : Even j
          · rw [add_comm]
            have := hevenabsorb j hpar hbot htop
            simpa [Sigma.sigma] using this
          · have hodd : Odd j := Nat.not_even_iff_odd.mp hpar
            have hj3 : 2 * p + 3 ≤ j := by obtain ⟨t, ht⟩ := hodd; omega
            have hjle : j ≤ 2 * q + 1 := by obtain ⟨t, ht⟩ := hodd; omega
            refine ⟨?_, ?_⟩
            · simp only [Prod.fst_add]
              have := haodd j hodd hj3 (by omega)
              simpa [Sigma.sigma] using this
            · simp only [Prod.snd_add]
              have := hbodd j hodd hj3 hjle
              simpa [Sigma.sigma] using this
        · rw [if_neg htop]
          have hjeq : j = 2 * q + 3 := by omega
          have hodd : Odd j := by rw [hjeq]; exact ⟨q + 1, by ring⟩
          refine ⟨?_, ?_⟩
          · simp only [Prod.fst_add]
            have := haodd j hodd (by omega) (by omega)
            simpa [Sigma.sigma] using this
          · simp only [Prod.snd_add, add_zero]; exact hXYj.2
      · rw [if_neg hbot]
        have htop : j ≤ 2 * q + 2 := by omega
        rw [if_pos htop,
          show ((1:ℚ),(1:ℚ)) + (-((1:ℚ),(0:ℚ))) = ((0:ℚ),(1:ℚ)) from by norm_num]
        have hjeq : j = 2 * p + 1 := by omega
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add]; rw [add_zero]; exact hXYj.1
        · simp only [Prod.snd_add]
          rw [hjeq]
          have hb := hbanchor
          rw [Sigma.sigma, Sigma.sigma] at hb
          linarith [hb]

/-- **Assembly** of §16 Branch B Case 3, diagonal `X ⊇ 2g₁` (type8 `p = q`,
`Mix (Pi, Lambda)`).  Builds `2g⁺(m) → g⁺(m-2) + g⁺(m+2)`. -/
lemma branchB_case3_assembly_type8_double {N : ℕ}
    (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (p : ℕ) (g₁ : Gene)
    (hg₁rank : g₁.rank = 2 * p + 2) (hg₁pos : g₁.type = .Positive)
    (hXg₁2 : 2 ≤ X.1.1 g₁)
    (hbanchor : (Sigma.sigma X.1.1 (2 * p + 1)).2 + 1 ≤ (Sigma.sigma Y.1.1 (2 * p + 1)).2)
    (haodd : ∀ j, Odd j → 2 * p + 3 ≤ j → j ≤ 2 * p + 3 →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hevenabsorb : ∀ j, Even j → 2 * p + 2 ≤ j → j ≤ 2 * p + 2 →
        ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[j] X.1.1) ≤
          signature (Chromosome.prime^[j] Y.1.1)) :
    ∃ Z : Mix (Pi, Lambda), MixPiLambda.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y8' : Mix (Pi, Lambda) := Y8 (le_refl p) hε
  let restval : Chromosome := X.1.1 - Finsupp.single g₁ 1 - Finsupp.single g₁ 1
  have rest_mem : restval ∈ Mix (Pi, Lambda) :=
    sub_mem_Mix_Pi_Lambda _ (sub_mem_Mix_Pi_Lambda _ X.1.2)
  let rest_M : Mix (Pi, Lambda) := ⟨restval, rest_mem⟩
  have hg₁_eq : Gene.ofRank (2 * p + 2) .Positive = (Finsupp.single g₁ 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g₁); rw [hg₁rank, hg₁pos] at h; exact h
  have hX8_val : (X8 (le_refl p) hε).1 = Finsupp.single g₁ 1 + Finsupp.single g₁ 1 := by
    rw [X8_eq, hg₁_eq]
  have hX_eq : (X8 (le_refl p) hε).1 + restval = X.1.1 := by
    rw [hX8_val]; exact X_eq_double_add_rest hXg₁2
  let Z : Mix (Pi, Lambda) := ⟨Y8'.1 + restval, add_mem Y8'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X8 (le_refl p) hε : Mix (Pi, Lambda)) + rest_M = X.1) ▸
    MixPiLambda.Step.mk (X8 (le_refl p) hε) Y8' rest_M
      (MixPiLambda.Primitive.type8 GeneType.Positive hε (le_refl p)), ?_⟩
  change Y8'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X8 (le_refl p) hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * p
  · have h88 : signature (Chromosome.prime^[j] Y8'.1) =
        signature (Chromosome.prime^[j] (X8 (le_refl p) hε).1) :=
      (sigma_type8_eq_before (le_refl p) hε (hj := hj)).symm
    rw [h88, ← hdecomp]; exact hXYj
  · by_cases hj_after : 2 * p + 4 ≤ j
    · have h88 : signature (Chromosome.prime^[j] Y8'.1) =
          signature (Chromosome.prime^[j] (X8 (le_refl p) hε).1) :=
        (sigma_type8_eq_after (le_refl p) hε (hj := hj_after)).symm
      rw [h88, ← hdecomp]; exact hXYj
    · have hj1 : 2 * p < j := by omega
      have hj2 : j < 2 * p + 4 := by omega
      have hmid := sigma_type8_mid (le_refl p) hε hj1 hj2
      have hY8_eq : signature (Chromosome.prime^[j] Y8'.1) =
          signature (Chromosome.prime^[j] (X8 (le_refl p) hε).1) +
            ((if j ≤ 2 * p + 2 then (1, 1) else signature (Gene.ofRank 1 GeneType.Positive)) +
             (if 2 * p + 2 ≤ j then 0 else -signature (Gene.ofRank 1 GeneType.Positive))) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY8_eq, add_right_comm, ← hdecomp]
      rw [signature_ofRank_one_positive]
      by_cases hbot : 2 * p + 2 ≤ j
      · rw [if_pos hbot, add_zero]
        by_cases htop : j ≤ 2 * p + 2
        · rw [if_pos htop]
          have hjeven : Even j := ⟨p + 1, by omega⟩
          rw [add_comm]
          have := hevenabsorb j hjeven hbot htop
          simpa [Sigma.sigma] using this
        · rw [if_neg htop]
          have hjeq : j = 2 * p + 3 := by omega
          have hodd : Odd j := by rw [hjeq]; exact ⟨p + 1, by ring⟩
          refine ⟨?_, ?_⟩
          · simp only [Prod.fst_add]
            have := haodd j hodd (by omega) (by omega)
            simpa [Sigma.sigma] using this
          · simp only [Prod.snd_add, add_zero]; exact hXYj.2
      · rw [if_neg hbot]
        have htop : j ≤ 2 * p + 2 := by omega
        rw [if_pos htop,
          show ((1:ℚ),(1:ℚ)) + (-((1:ℚ),(0:ℚ))) = ((0:ℚ),(1:ℚ)) from by norm_num]
        have hjeq : j = 2 * p + 1 := by omega
        refine ⟨?_, ?_⟩
        · simp only [Prod.fst_add]; rw [add_zero]; exact hXYj.1
        · simp only [Prod.snd_add]
          rw [hjeq]
          have hb := hbanchor
          rw [Sigma.sigma, Sigma.sigma] at hb
          linarith [hb]

/-- `Y` `a`-component 2-step drop at an odd start bounded by the bottom rank-drop `|Y|`
(`Mix (Pi, Lambda)`).  `a`-mirror of `bdrop_two_step_odd_le_pl`. -/
private lemma adrop_two_step_odd_le_pl {Y : Chromosome} (hY : Y ∈ Mix (Pi, Lambda)) (u : ℕ) :
    (Sigma.sigma Y (2 * u + 1)).1 - (Sigma.sigma Y (2 * u + 3)).1 ≤
      ((Sigma.sigma Y 0).1 - (Sigma.sigma Y 1).1) +
      ((Sigma.sigma Y 0).2 - (Sigma.sigma Y 1).2) := by
  have c7e := cond_15_7_Mix_Pi_Lambda hY (2 * u)
  rw [if_pos ⟨u, by ring⟩] at c7e
  have c6o := cond_15_6_Mix_Pi_Lambda hY (2 * u + 1)
  rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨u, by ring⟩),
    show 2 * u + 1 + 1 = 2 * u + 2 from by ring,
    show 2 * u + 1 + 2 = 2 * u + 3 from by ring] at c6o
  have c6 := cond_15_6_Mix_Pi_Lambda hY (2 * u)
  rw [if_pos ⟨u, by ring⟩] at c6
  rw [show 2 * u + 1 + 1 = 2 * u + 2 from by ring] at c6
  have ha2 := adrop_even_le hY u
  have hb2 := bdrop_even_le_pl hY u
  linarith [c7e, c6o, c6, ha2, hb2]

/-- `a`-component 2-step drop from level 1 equals `|W|`, provided every gene has rank `≥ 2`
and every rank-`2` gene is positive (so each gene contributes exactly `1` to the `a`-drop;
a negative rank-`2` gene would contribute `0`). -/
lemma a13_drop_eq_cells {W : Chromosome}
    (hW : ∀ g ∈ W.support, 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive)) :
    (Sigma.sigma W 1).1 - (Sigma.sigma W 3).1 = W.sum (fun _ m => (m : ℚ)) := by
  induction W using Finsupp.induction with
  | zero => simp [Sigma.sigma]
  | single_add g n f hg hn ih =>
    have hgr : 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive) := hW g (by simp [hn])
    have hf : ∀ g' ∈ f.support, 2 ≤ g'.rank ∧ (g'.rank = 2 → g'.type = .Positive) := by
      intro g' hg'
      apply hW
      simp only [Finsupp.mem_support_iff, Finsupp.add_apply]
      have hz : (Finsupp.single g n) g' = 0 := by
        rw [Finsupp.single_apply, if_neg]; rintro rfl; exact hg hg'
      rw [hz, zero_add]; exact Finsupp.mem_support_iff.mp hg'
    have he : (Finsupp.single g n : Chromosome) = n • Gene.ofRank g.rank g.type := by
      rw [Gene.ofRank_eq_gene]; simp
    have e1 : Chromosome.prime^[1] (Finsupp.single g n) =
        n • Gene.ofRank (g.rank - 1) g.type := by rw [he, iterate_map_nsmul, prime_iterate_ofRank]
    have e3 : Chromosome.prime^[3] (Finsupp.single g n) =
        n • Gene.ofRank (g.rank - 3) g.type := by rw [he, iterate_map_nsmul, prime_iterate_ofRank]
    have hsingle : (Sigma.sigma (Finsupp.single g n) 1).1 -
        (Sigma.sigma (Finsupp.single g n) 3).1 = (n : ℚ) := by
      simp only [Sigma.sigma, e1, e3, map_nsmul]
      rcases Nat.lt_or_ge g.rank 3 with hlt | hge
      · have hr2 : g.rank = 2 := by omega
        have hpos : g.type = .Positive := hgr.2 hr2
        rw [hr2, hpos, show (2 - 1 : ℕ) = 1 from rfl, show (2 - 3 : ℕ) = 0 from rfl,
          signature_ofRank_one_positive, signature_ofRank_zero]
        simp
      · rw [show g.rank - 1 = (g.rank - 3) + 2 from by omega, signature_ofRank_eq₂']
        simp only [Prod.smul_fst, Prod.fst_add]; ring
    rw [Finsupp.sum_add_index (by simp) (by intros; simp), Finsupp.sum_single_index (by simp)]
    rw [Sigma.sigma_linearity, Sigma.sigma_linearity, Prod.fst_add, Prod.fst_add]
    rw [show (Sigma.sigma (Finsupp.single g n) 1).1 + (Sigma.sigma f 1).1 -
        ((Sigma.sigma (Finsupp.single g n) 3).1 + (Sigma.sigma f 3).1) =
        ((Sigma.sigma (Finsupp.single g n) 1).1 - (Sigma.sigma (Finsupp.single g n) 3).1) +
        ((Sigma.sigma f 1).1 - (Sigma.sigma f 3).1) by ring]
    rw [hsingle, ih hf]

/-- **`a`-anchor from the total gap** (`Mix (Pi, Lambda)`): `a_X(2m'+1) + 1 ≤ a_Y(2m'+1)`.
`a`-mirror of `branchB_case3_banchor_pl`. -/
lemma branchB_a_anchor_totalgap {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (m' : ℕ) (hm'pos : 1 ≤ m')
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank) :
    (Sigma.sigma X.1.1 (2 * m' + 1)).1 + 1 ≤ (Sigma.sigma Y.1.1 (2 * m' + 1)).1 := by
  have hXtw : (Sigma.sigma X.1.1 (2 * m' - 1)).1 - (Sigma.sigma X.1.1 (2 * m' + 1)).1 =
      X.1.1.sum (fun _ m => (m : ℚ)) := by
    have := twostep (W := X.1.1) (i := 2 * m' - 1)
      (fun g hg => by have := hmin g hg; omega)
    rwa [show 2 * m' - 1 + 2 = 2 * m' + 1 from by omega] at this
  have hYcells : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
      ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) = Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hYtw : (Sigma.sigma Y.1.1 (2 * m' - 1)).1 - (Sigma.sigma Y.1.1 (2 * m' + 1)).1 ≤
      Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h := adrop_two_step_odd_le_pl Y.1.2 (m' - 1)
    rw [show 2 * (m' - 1) + 1 = 2 * m' - 1 from by omega,
      show 2 * (m' - 1) + 3 = 2 * m' + 1 from by omega] at h
    rw [← hYcells]; linarith
  have hXcells : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
      ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) = X.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hrk0 : (X.1.1.rank : ℚ) = (Y.1.1.rank : ℚ) := by rw [X.2, Y.2]
  have hsX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
  have hYltX : Y.1.1.sum (fun _ m => (m : ℚ)) < X.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [← hYcells, ← hXcells]; linarith [hsX0, hsY0, hrk0, hgap]
  have hDom : (Sigma.sigma X.1.1 (2 * m' - 1)).1 ≤ (Sigma.sigma Y.1.1 (2 * m' - 1)).1 :=
    (le_iff_dominates.mp hXY.le (2 * m' - 1)).1
  have hlt : (Sigma.sigma X.1.1 (2 * m' + 1)).1 < (Sigma.sigma Y.1.1 (2 * m' + 1)).1 := by
    linarith [hXtw, hYtw, hYltX, hDom]
  obtain ⟨zX, hzX⟩ := sig_fst_isInt_odd X.1.2 (show Odd (2 * m' + 1) from ⟨m', by ring⟩)
  obtain ⟨zY, hzY⟩ := sig_fst_isInt_odd Y.1.2 (show Odd (2 * m' + 1) from ⟨m', by ring⟩)
  rw [hzX, hzY] at hlt ⊢
  have hz : zX < zY := by exact_mod_cast hlt
  have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
  linarith

/-- **Deep-interior `a`-propagation from the total gap** (`Mix (Pi, Lambda)`).  `a`-mirror of
`branchB_case3_deep_bprop`: propagates the odd-level anchor `a_X(2m'+1) + 1 ≤ a_Y(2m'+1)`
upward to every odd level `2m'+1+2t ≤ k`. -/
lemma branchB_deep_aprop {N : ℕ} (X Y : nMixPiLambda N) (_ : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (m' : ℕ) (g₁ : Gene) (hg₁mult : X.1.1 g₁ = 1)
    (k : ℕ) (htail : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, k ≤ g.rank)
    (hanchor : (Sigma.sigma X.1.1 (2 * m' + 1)).1 + 1 ≤ (Sigma.sigma Y.1.1 (2 * m' + 1)).1) :
    ∀ t, 2 * m' + 1 + 2 * t ≤ k →
        (Sigma.sigma X.1.1 (2 * m' + 1 + 2 * t)).1 + 1 ≤
          (Sigma.sigma Y.1.1 (2 * m' + 1 + 2 * t)).1 := by
  set X' : Chromosome := X.1.1 - Finsupp.single g₁ 1 with hX'def
  have hXadd : X.1.1 = X' + Finsupp.single g₁ 1 := by
    rw [hX'def]; ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hg : g₁ = g
    · subst hg; rw [if_pos rfl]; omega
    · rw [if_neg hg]; omega
  set CX' : ℚ := X'.sum (fun _ m => (m : ℚ)) with hCX'def
  have hcellsX : X.1.1.sum (fun _ m => (m : ℚ)) = CX' + 1 := by
    conv_lhs => rw [hXadd]
    rw [Finsupp.sum_add_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_single_index (by simp)]; push_cast; ring
  have hYcells : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
      ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) = Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hXcells : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
      ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) = X.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hrk0 : (X.1.1.rank : ℚ) = (Y.1.1.rank : ℚ) := by rw [X.2, Y.2]
  have hsX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
  have hcellsYlt : Y.1.1.sum (fun _ m => (m : ℚ)) ≤ CX' := by
    have hlt : Y.1.1.sum (fun _ m => (m : ℚ)) < X.1.1.sum (fun _ m => (m : ℚ)) := by
      rw [← hYcells, ← hXcells]; linarith [hsX0, hsY0, hrk0, hgap]
    rw [hcellsX] at hlt
    have hYn : ∃ n : ℕ, Y.1.1.sum (fun _ m => (m : ℚ)) = (n : ℚ) :=
      ⟨Y.1.1.sum (fun _ m => m), by rw [Finsupp.sum, Finsupp.sum]; push_cast; ring⟩
    have hXn : ∃ n : ℕ, CX' = (n : ℚ) :=
      ⟨X'.sum (fun _ m => m), by rw [hCX'def, Finsupp.sum, Finsupp.sum]; push_cast; ring⟩
    obtain ⟨ny, hny⟩ := hYn; obtain ⟨nx, hnx⟩ := hXn
    rw [hny, hnx] at hlt ⊢; have : ny < nx + 1 := by exact_mod_cast hlt
    exact_mod_cast (by omega : ny ≤ nx)
  have hYdrop : ∀ s, (Sigma.sigma Y.1.1 (2 * m' + 1 + 2 * s)).1 -
      (Sigma.sigma Y.1.1 (2 * m' + 1 + 2 * s + 2)).1 ≤ Y.1.1.sum (fun _ m => (m : ℚ)) := by
    intro s
    have h := adrop_two_step_odd_le_pl Y.1.2 (m' + s)
    rw [show 2 * (m' + s) + 1 = 2 * m' + 1 + 2 * s from by ring,
      show 2 * (m' + s) + 3 = 2 * m' + 1 + 2 * s + 2 from by ring] at h
    rw [← hYcells]; linarith
  have hXdrop : ∀ s, 2 * m' + 1 + 2 * s + 2 ≤ k →
      CX' ≤ (Sigma.sigma X.1.1 (2 * m' + 1 + 2 * s)).1 -
        (Sigma.sigma X.1.1 (2 * m' + 1 + 2 * s + 2)).1 := by
    intro s hs
    have htw : (Sigma.sigma X' (2 * m' + 1 + 2 * s)).1 -
        (Sigma.sigma X' (2 * m' + 1 + 2 * s + 2)).1 = CX' :=
      twostep (W := X') (i := 2 * m' + 1 + 2 * s) (fun g hg => le_trans hs (htail g hg))
    have hg₁anti : (Sigma.sigma (Finsupp.single g₁ 1) (2 * m' + 1 + 2 * s + 2)).1 ≤
        (Sigma.sigma (Finsupp.single g₁ 1) (2 * m' + 1 + 2 * s)).1 :=
      (Sigma.antitone (Finsupp.single g₁ 1) (by omega)).1
    have hsplit : ∀ i, (Sigma.sigma X.1.1 i).1 =
        (Sigma.sigma X' i).1 + (Sigma.sigma (Finsupp.single g₁ 1) i).1 := by
      intro i; conv_lhs => rw [hXadd]
      rw [Sigma.sigma_linearity, Prod.fst_add]
    rw [hsplit, hsplit, ← htw]; linarith [hg₁anti]
  intro t
  induction t with
  | zero => intro _; simpa using hanchor
  | succ s ih =>
    intro hbound
    have hih := ih (by omega)
    have hYd := hYdrop s
    have hXd := hXdrop s (by omega)
    have e2 : 2 * m' + 1 + 2 * (s + 1) = 2 * m' + 1 + 2 * s + 2 := by ring
    rw [e2]
    linarith [hih, hYd, hXd, hcellsYlt]

/-- **§16 Case 4 `a`-anchor at level 3** (`Mix (Pi, Lambda)`): with `g₁ = g⁺(2)` the unique
minimal gene (mult 1) and every other gene of rank `≥ 3`, the total gap forces
`a_X(3) + 1 ≤ a_Y(3)`.  This is the `c₁-c₃` chain: `X`'s `a`-2-step drop `a_X(1)-a_X(3) = |X|`
(the boundary gene `g⁺(2)` contributes `1`), `Y`'s is `≤ |Y| < |X|`. -/
lemma branchB_case4_a3_anchor {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (hX2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive)) :
    (Sigma.sigma X.1.1 3).1 + 1 ≤ (Sigma.sigma Y.1.1 3).1 := by
  have hXtw : (Sigma.sigma X.1.1 1).1 - (Sigma.sigma X.1.1 3).1 =
      X.1.1.sum (fun _ m => (m : ℚ)) := a13_drop_eq_cells hX2
  -- Y a-2-step drop ≤ |Y|, and |Y| < |X|
  have hYcells : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
      ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) = Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hYtw : (Sigma.sigma Y.1.1 1).1 - (Sigma.sigma Y.1.1 3).1 ≤
      Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h := adrop_two_step_odd_le_pl Y.1.2 0
    simp only [Nat.mul_zero, Nat.zero_add] at h
    rw [← hYcells]; linarith
  have hXcells : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
      ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) = X.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hrk0 : (X.1.1.rank : ℚ) = (Y.1.1.rank : ℚ) := by rw [X.2, Y.2]
  have hsX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
  have hYltX : Y.1.1.sum (fun _ m => (m : ℚ)) < X.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [← hYcells, ← hXcells]; linarith [hsX0, hsY0, hrk0, hgap]
  have hDom : (Sigma.sigma X.1.1 1).1 ≤ (Sigma.sigma Y.1.1 1).1 :=
    (le_iff_dominates.mp hXY.le 1).1
  have hlt : (Sigma.sigma X.1.1 3).1 < (Sigma.sigma Y.1.1 3).1 := by
    linarith [hXtw, hYtw, hYltX, hDom]
  obtain ⟨zX, hzX⟩ := sig_fst_isInt_odd X.1.2 (show Odd 3 from ⟨1, by ring⟩)
  obtain ⟨zY, hzY⟩ := sig_fst_isInt_odd Y.1.2 (show Odd 3 from ⟨1, by ring⟩)
  rw [hzX, hzY] at hlt ⊢
  have hz : zX < zY := by exact_mod_cast hlt
  have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
  linarith

/-- **§16 Case 4 `a`-propagation from the total gap** (`Mix (Pi, Lambda)`): combines the
level-3 anchor with `branchB_deep_aprop` to give `a_X(j) + 1 ≤ a_Y(j)` for every odd `1 < j ≤ k`,
with `g₁ = g⁺(2)` the unique minimal gene (mult 1) and all other genes of rank `≥ k ≥ 3`. -/
lemma branchB_case4_aprop_totalgap {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (g₁ : Gene) (hg₁mult : X.1.1 g₁ = 1)
    (hX2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank ∧ (g.rank = 2 → g.type = .Positive))
    (k : ℕ) (htailk : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, k ≤ g.rank) :
    ∀ j, 1 < j → j ≤ k → Odd j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
  have h3 := branchB_case4_a3_anchor X Y hXY hgap hX2
  have hdeep := branchB_deep_aprop X Y hXY hgap 1 g₁ hg₁mult k htailk
    (by simpa using h3)
  intro j hj1 hjk hoj
  obtain ⟨t, ht⟩ : ∃ t, j = 3 + 2 * t := by
    obtain ⟨r, hr⟩ := hoj; exact ⟨r - 1, by omega⟩
  subst ht
  have := hdeep t (by omega)
  simpa [show 2 * 1 + 1 + 2 * t = 3 + 2 * t from by ring] using this

/-- **Level-2 `(1,1)` absorption from the total gap** (`Mix (Pi, Lambda)`).  With every `X`-gene
of rank `≥ 2`, `X`'s rank 2-step drop is `2|X|`, `Y`'s is `≤ 2|Y| < 2|X|`, so the rank gap at
level `2` is `≥ 2`, which (since level 2 is even, `a = b`) halves to a full `(1,1)`.  Used for
the bottom even level of §16 Case 4 type8, where the odd neighbor `j-1 = 1` is `a`-balanced. -/
lemma even2_absorb_totalgap {N : ℕ} (X Y : nMixPiLambda N) (_ : X.1 < Y.1)
    (hgap : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 <
      (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2)
    (hmin2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank) :
    ((1 : ℚ), (1 : ℚ)) + Sigma.sigma X.1.1 2 ≤ Sigma.sigma Y.1.1 2 := by
  have hXa : (Sigma.sigma X.1.1 0).1 - (Sigma.sigma X.1.1 2).1 =
      X.1.1.sum (fun _ m => (m : ℚ)) := by
    have := twostep (W := X.1.1) (i := 0) (fun g hg => by
      have := hmin2 g hg
      omega)
    simpa using this
  have hXb : (Sigma.sigma X.1.1 0).2 - (Sigma.sigma X.1.1 2).2 =
      X.1.1.sum (fun _ m => (m : ℚ)) := by
    have := twostep_snd (W := X.1.1) (i := 0) (fun g hg => by have := hmin2 g hg; omega)
    simpa using this
  have hY01 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
      ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) = Y.1.1.sum (fun _ m => (m : ℚ)) := by
    have h0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells
  have hconv : (Chromosome.prime^[1] Y.1.1).prime = Chromosome.prime^[2] Y.1.1 :=
    (Function.iterate_succ_apply' Chromosome.prime 1 Y.1.1).symm
  have hY12 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 -
      ((Sigma.sigma Y.1.1 2).1 + (Sigma.sigma Y.1.1 2).2) =
      (Chromosome.prime^[1] Y.1.1).sum (fun _ m => (m : ℚ)) := by
    have h1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
        ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
    have h2 : (Sigma.sigma Y.1.1 2).1 + (Sigma.sigma Y.1.1 2).2 =
        ((Chromosome.prime^[1] Y.1.1).prime.rank : ℚ) := by
      rw [hconv]; exact @signature_sum_eq_rank _
    rw [h1, h2]; exact cells
  have hprimeYle : (Chromosome.prime^[1] Y.1.1).sum (fun _ m => (m : ℚ)) ≤
      Y.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [prime_iterate_sum_eq, Finsupp.sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun g _ _ => by positivity)
  have hr0X : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma, X.2] using this
  have hr0Y : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma, Y.2] using this
  have hYcellsdef : Y.1.1.sum (fun _ m => (m : ℚ)) =
      (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 -
        ((Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2) := hY01.symm
  have hXcellsdef : X.1.1.sum (fun _ m => (m : ℚ)) =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) := by
    have h0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma] using this
    have h1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
        ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
    rw [h0, h1, Function.iterate_one]; exact cells.symm
  have hYltX : Y.1.1.sum (fun _ m => (m : ℚ)) < X.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [hYcellsdef, hXcellsdef]; linarith [hr0X, hr0Y]
  -- rank gap at level 2 is ≥ 2 (uses integrality of |X| - |Y| ≥ 1)
  have hYXint : X.1.1.sum (fun _ m => (m : ℚ)) - Y.1.1.sum (fun _ m => (m : ℚ)) ≥ 1 := by
    have hXn : ∃ n : ℕ, X.1.1.sum (fun _ m => (m : ℚ)) = (n : ℚ) :=
      ⟨X.1.1.sum (fun _ m => m), by rw [Finsupp.sum, Finsupp.sum]; push_cast; ring⟩
    have hYn : ∃ n : ℕ, Y.1.1.sum (fun _ m => (m : ℚ)) = (n : ℚ) :=
      ⟨Y.1.1.sum (fun _ m => m), by rw [Finsupp.sum, Finsupp.sum]; push_cast; ring⟩
    obtain ⟨nx, hnx⟩ := hXn; obtain ⟨ny, hny⟩ := hYn
    rw [hnx, hny] at hYltX ⊢
    have : ny < nx := by exact_mod_cast hYltX
    have : (ny : ℚ) + 1 ≤ nx := by exact_mod_cast (by omega : ny + 1 ≤ nx)
    linarith
  have hrankgap : (Sigma.sigma X.1.1 2).1 + (Sigma.sigma X.1.1 2).2 + 2 ≤
      (Sigma.sigma Y.1.1 2).1 + (Sigma.sigma Y.1.1 2).2 := by
    linarith [hXa, hXb, hY01, hY12, hprimeYle, hr0X, hr0Y, hYXint]
  have hXsym : (Sigma.sigma X.1.1 2).1 = (Sigma.sigma X.1.1 2).2 :=
    signature_prime_iterate_even_eq_components X.1.2 ⟨1, rfl⟩
  have hYsym : (Sigma.sigma Y.1.1 2).1 = (Sigma.sigma Y.1.1 2).2 :=
    signature_prime_iterate_even_eq_components Y.1.2 ⟨1, rfl⟩
  constructor
  · simp only [Prod.fst_add]; linarith [hrankgap, hXsym, hYsym]
  · simp only [Prod.snd_add]; linarith [hrankgap, hXsym, hYsym]

end MixPiLambda
