import YoungDiagram.Theorem6.MixLambdaPi.Case1
import YoungDiagram.Theorem6.MixLambdaPi.Case3
import YoungDiagram.Theorem6.MixLambdaPi.Drops
import YoungDiagram.Theorem6.MixLambdaPi.SigmaWindow
import YoungDiagram.Theorem6.MixLambdaPi.Propagation

/-!
# §16 Case A core for `Mix (Lambda, Pi)` (label 1).

This file dispatches the Case A core of §15.10 / §16 on the polarization of the
minimal-rank gene `g₁` of `X`, mirroring `Pi.exists_mutation_le_fifteen_ten_caseA`
in `YoungDiagram/Theorem6/Pi/CaseA.lean`.

Following §16 (Djoković), after the disjoint / sigma-agreement / polarized-pair
reductions (handled by the dispatcher in `MixVarietyJoint`), we let `g₁` be a gene
of minimal rank `m` in `X` and split:

* **Branch A** (`g₁ = g(m)` nonpolarized): paper Cases 1–2 (primitives type4–7);
* **Branch B** (`g₁ = g^±(m)` polarized): paper Cases 3–5 (primitives type6–8).

Each branch propagates a single strict level `a_m < c_m` / `b_m < d_m` across a
window using `cond_15_6/7_Mix_Lambda_Pi` (`Drops.lean`) and the window signature
identities in `SigmaWindow.lean`, half-integer increments handled as in
`half_le_sigma_diff_at_r`.  The two branches are the current formalization
targets.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-! ### Branch A infrastructure: R2 reduction `X ⊇ 2g(m)` (type4 diagonal). -/

/-- A nonpolarized gene of `X ∈ Mix (Lambda, Pi)` has even rank (mirror of
`Case3.rank_odd_of_polarized`). -/
lemma rank_even_of_nonpolarized_mem {X : Chromosome} (hX : X ∈ Mix (Lambda, Pi))
    {g : Gene} (hNP : g.type = .NonPolarized) (hgX : 0 < X g) :
    Even g.rank := by
  by_contra hnot
  rw [Nat.not_even_iff_odd] at hnot
  have hod : 0 < X.oddPart g := by
    rw [oddPart_eq, Finsupp.filter_apply, if_pos hnot]; exact hgX
  have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp hX.2) g
    (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hod))
  rw [hNP] at hpol
  exact hpol rfl

/-- If `X` contains a nonpolarized gene `g`, then `signature (prime^[g.rank-1] X).1 ≥ 1/2`
(the rank-1 nonpolarized residue contributes `(1/2, 1/2)`). -/
lemma half_le_signature_fst_of_contains_nonpolarized_mix {X : Chromosome}
    {g : Gene} (hNP : g.type = .NonPolarized) (hXg : 0 < X g) :
    (1 : ℚ) / 2 ≤ (signature (Chromosome.prime^[g.rank - 1] X)).1 := by
  have hr : 1 ≤ g.rank := g.rank_pos
  have hg_single : Gene.ofRank g.rank .NonPolarized = (Finsupp.single g 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g); rw [hNP] at h; exact h
  have hprime : Chromosome.prime^[g.rank - 1] (Finsupp.single g 1 : Chromosome) =
      Gene.ofRank 1 .NonPolarized := by
    rw [← hg_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
  have hXeq : X = Finsupp.single g 1 + (X - Finsupp.single g 1) := by
    rw [add_comm, sub_single_add_single_eq hXg]
  calc (1 : ℚ) / 2
      = (signature (Gene.ofRank 1 .NonPolarized : Chromosome)).1 := by
        simp [signature_ofRank_nonPolarized]
    _ = (signature (Chromosome.prime^[g.rank - 1] (Finsupp.single g 1 : Chromosome))).1 := by
        rw [hprime]
    _ ≤ (signature (Chromosome.prime^[g.rank - 1] X)).1 := by
        conv_rhs => rw [hXeq]
        rw [iterate_map_add, map_add]
        exact le_add_of_nonneg_right (signature_nonneg _).1

/-- For disjoint `X, Y ∈ Mix (Lambda, Pi)`, if `X` has a nonpolarized gene `g₁` of even
rank `r`, then `Y` has no gene of rank `r` (the unique even-rank gene shape is the
nonpolarized `g₁`, which `Y` cannot share). -/
lemma Y_no_gene_of_even_rank_mix {X Y : Chromosome}
    (hYmem : Y ∈ Mix (Lambda, Pi))
    (hcommon : ∀ g, 0 < X g → Y g ≤ 0)
    (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized) (hXg₁ : 0 < X g₁)
    {r : ℕ} (hr : g₁.rank = r) (hrev : Even r)
    (g : Gene) (hgr : g.rank = r) : Y g = 0 := by
  by_contra hne
  have hgY : 0 < Y g := Nat.pos_of_ne_zero hne
  have hgY_even : 0 < Y.evenPart g := by
    rw [evenPart_eq, Finsupp.filter_apply, if_pos (hgr ▸ hrev)]; exact hgY
  have hg_NP : g.type = .NonPolarized :=
    IsNonPolarized_def'.mp (mem_Lambda_iff.mp hYmem.1) g
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgY_even))
  have hgeq : g = g₁ := Gene.ext (hgr.trans hr.symm) (hg_NP.trans hg₁NP.symm)
  subst hgeq
  have := hcommon g hXg₁
  omega

/-- The second sigma component is an integer at even levels for `Mix (Lambda, Pi)`. -/
lemma sig_snd_isInt_even {Z : Chromosome} (hZ : Z ∈ Mix (Lambda, Pi))
    {i : ℕ} (hi : Even i) : ∃ z : ℤ, (Sigma.sigma Z i).2 = (z : ℚ) := by
  obtain ⟨a, ha⟩ := sig_fst_isInt_even hZ hi
  have hsum : (signature (Chromosome.prime^[i] Z)).1 + (signature (Chromosome.prime^[i] Z)).2 =
      ((Chromosome.prime^[i] Z).rank : ℚ) := signature_sum_eq_rank
  refine ⟨((Chromosome.prime^[i] Z).rank : ℤ) - a, ?_⟩
  have : (Sigma.sigma Z i).2 = ((Chromosome.prime^[i] Z).rank : ℚ) - (Sigma.sigma Z i).1 := by
    change (signature (Chromosome.prime^[i] Z)).2 = _
    have : (Sigma.sigma Z i).1 = (signature (Chromosome.prime^[i] Z)).1 := rfl
    rw [this] at *; linarith
  rw [this, ha]; push_cast; ring

/-- Even-level strict `<` upgrades to `+1 ≤` on the first sigma component (integrality). -/
lemma add_one_le_sigma_fst_of_lt_even {A B : Chromosome}
    (hA : A ∈ Mix (Lambda, Pi)) (hB : B ∈ Mix (Lambda, Pi)) {i : ℕ} (hi : Even i)
    (hlt : (Sigma.sigma A i).1 < (Sigma.sigma B i).1) :
    (Sigma.sigma A i).1 + 1 ≤ (Sigma.sigma B i).1 := by
  obtain ⟨a, ha⟩ := sig_fst_isInt_even hA hi
  obtain ⟨b, hb⟩ := sig_fst_isInt_even hB hi
  rw [ha, hb] at hlt ⊢
  have hab : a < b := by exact_mod_cast hlt
  have : (a : ℚ) + 1 ≤ b := by exact_mod_cast hab
  linarith

/-- Even-level strict `<` upgrades to `+1 ≤` on the second sigma component (integrality). -/
lemma add_one_le_sigma_snd_of_lt_even {A B : Chromosome}
    (hA : A ∈ Mix (Lambda, Pi)) (hB : B ∈ Mix (Lambda, Pi)) {i : ℕ} (hi : Even i)
    (hlt : (Sigma.sigma A i).2 < (Sigma.sigma B i).2) :
    (Sigma.sigma A i).2 + 1 ≤ (Sigma.sigma B i).2 := by
  obtain ⟨a, ha⟩ := sig_snd_isInt_even hA hi
  obtain ⟨b, hb⟩ := sig_snd_isInt_even hB hi
  rw [ha, hb] at hlt ⊢
  have hab : a < b := by exact_mod_cast hlt
  have : (a : ℚ) + 1 ≤ b := by exact_mod_cast hab
  linarith

/-- Decomposition `2g + (X - 2g) = X` when `X` has multiplicity `≥ 2` at `g`. -/
lemma X_eq_double_add_rest {X : Chromosome} {g : Gene} (hXg : 2 ≤ X g) :
    Finsupp.single g 1 + Finsupp.single g 1 +
      (X - Finsupp.single g 1 - Finsupp.single g 1) = X := by
  ext g'
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases h1 : g = g'
  · subst h1; simp; omega
  · simp [if_neg h1]

/-- **R2 reduction, single step.** Given that the single in-window difference
`signature (ofRank 1 (-ε))` at level `r = 2m'+2` is dominated (`hboost`), the type4
diagonal mutation `2g(m) → g^{-ε}(m-1) + g^ε(m+1)` produces `Z ≤ Y`. -/
lemma branchA_R2_step {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (m' : ℕ) (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized)
    (hg₁rank : g₁.rank = 2 * m' + 2) (hXg₁2 : 2 ≤ X.1.1 g₁)
    (ε : GeneType) (hε : ε ≠ .NonPolarized)
    (hboost : signature (Gene.ofRank 1 (-ε)) +
        signature (Chromosome.prime^[2 * m' + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * m' + 2] Y.1.1)) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let X4' : Mix (Lambda, Pi) := X4 (le_refl m')
  let Y4' : Mix (Lambda, Pi) := Y4 (le_refl m') hε
  have hg₁_eq : Gene.ofRank (2 * m' + 2) .NonPolarized = (Finsupp.single g₁ 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := g₁); rw [hg₁rank, hg₁NP] at h; exact h
  have hX4_val : X4'.1 = Finsupp.single g₁ 1 + Finsupp.single g₁ 1 := by
    change (X4 (le_refl m')).1 = _
    rw [X4_eq, hg₁_eq]
  let restval : Chromosome := X.1.1 - Finsupp.single g₁ 1 - Finsupp.single g₁ 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hX_eq : X4'.1 + restval = X.1.1 := by
    rw [hX4_val]; exact X_eq_double_add_rest hXg₁2
  let Z : Mix (Lambda, Pi) := ⟨Y4'.1 + restval, add_mem Y4'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X4 (le_refl m') : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X4 (le_refl m')) Y4' rest_M
      (MixLambdaPi.Primitive.type4 ε hε (le_refl m')), ?_⟩
  change Y4'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] X4'.1) + signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) :=
    le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m' + 1
  · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
        signature (Chromosome.prime^[j] X4'.1) :=
      (sigma_type4_eq_before (le_refl m') hε (hj := hj)).symm
    rw [hY4X4, ← hdecomp]; exact hXYj
  · by_cases hj_after : 2 * m' + 3 ≤ j
    · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
          signature (Chromosome.prime^[j] X4'.1) :=
        (sigma_type4_eq_after (le_refl m') hε (hj := hj_after)).symm
      rw [hY4X4, ← hdecomp]; exact hXYj
    · have hjeq : j = 2 * m' + 2 := by omega
      subst hjeq
      have hmid := sigma_type4_mid (le_refl m') hε (j := 2 * m' + 2) (by omega) (by omega)
      rw [show 2 * m' + 2 - (2 * m' + 2) = 0 from by omega, if_pos (by decide : Even 0)] at hmid
      have hY4_eq : signature (Chromosome.prime^[2 * m' + 2] Y4'.1) =
          signature (Chromosome.prime^[2 * m' + 2] X4'.1) + signature (Gene.ofRank 1 (-ε)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY4_eq]
      have heq : signature (Chromosome.prime^[2 * m' + 2] X4'.1) + signature (Gene.ofRank 1 (-ε))
            + signature (Chromosome.prime^[2 * m' + 2] restval)
          = signature (Gene.ofRank 1 (-ε)) + signature (Chromosome.prime^[2 * m' + 2] X.1.1) := by
        rw [hdecomp]; abel
      rw [heq]; exact hboost

/-- **R2 reduction.** When `X` contains `2g(m)` (the minimal-rank nonpolarized gene `g₁`
has multiplicity `≥ 2`), the §16 step `2g(m) → g^{-ε}(m-1) + g^ε(m+1)` applies: by
disjointness `Y` has no gene of rank `m`, so `prime^[m] Y ≠ 0` and `(16.1)` gives
`r_m < s_m`, hence `a_m < c_m` or `b_m < d_m`; choose `ε` accordingly. -/
lemma branchA_R2 {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' : ℕ) (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized)
    (hg₁rank : g₁.rank = 2 * m' + 2) (hXg₁2 : 2 ≤ X.1.1 g₁) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hcommon := hcommon
  have hsigeq := hsigeq
  push Not at hcommon hsigeq
  have hrev : Even (2 * m' + 2) := ⟨m' + 1, by ring⟩
  have hr1 : 1 ≤ 2 * m' + 2 := by omega
  have hXg₁ : 0 < X.1.1 g₁ := by omega
  -- Y has no gene of rank 2m'+2.
  have hY_no_gene : ∀ g : Gene, g.rank = 2 * m' + 2 → Y.1.1 g = 0 :=
    fun g hgr => Y_no_gene_of_even_rank_mix Y.1.2 hcommon g₁ hg₁NP hXg₁ hg₁rank hrev g hgr
  -- prime^[2m'+1] Y ≠ 0.
  have h_half : (1 : ℚ) / 2 ≤ (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).1 := by
    have := half_le_signature_fst_of_contains_nonpolarized_mix hg₁NP hXg₁
    rwa [hg₁rank, show 2 * m' + 2 - 1 = 2 * m' + 1 from by omega] at this
  have hYr1 : Chromosome.prime^[2 * m' + 1] Y.1.1 ≠ 0 := by
    intro heq
    have hdom : (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).1 ≤
        (signature (Chromosome.prime^[2 * m' + 1] Y.1.1)).1 :=
      (le_iff_dominates.mp hXY.le (2 * m' + 1)).1
    rw [heq, map_zero] at hdom
    simp only [Prod.fst_zero] at hdom
    linarith
  have hYr : Chromosome.prime^[2 * m' + 2] Y.1.1 ≠ 0 := by
    have := prime_ne_zero_of_Y_no_gene_mix hr1 hY_no_gene
      (show Chromosome.prime^[(2 * m' + 2) - 1] Y.1.1 ≠ 0 by
        rwa [show 2 * m' + 2 - 1 = 2 * m' + 1 from by omega])
    exact this
  -- (16.1): r_m < s_m, so a_m < c_m or b_m < d_m.
  have hsig_ne : Sigma.sigma X.1.1 (2 * m' + 2) ≠ Sigma.sigma Y.1.1 (2 * m' + 2) :=
    hsigeq (2 * m' + 2) (by omega) hYr
  have hle_r : Sigma.sigma X.1.1 (2 * m' + 2) ≤ Sigma.sigma Y.1.1 (2 * m' + 2) :=
    le_iff_dominates.mp hXY.le (2 * m' + 2)
  have hdich : (Sigma.sigma X.1.1 (2 * m' + 2)).1 < (Sigma.sigma Y.1.1 (2 * m' + 2)).1 ∨
      (Sigma.sigma X.1.1 (2 * m' + 2)).2 < (Sigma.sigma Y.1.1 (2 * m' + 2)).2 := by
    rcases lt_or_eq_of_le hle_r.1 with h | h
    · exact Or.inl h
    · rcases lt_or_eq_of_le hle_r.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd (Prod.ext h h2) hsig_ne
  rcases hdich with hlt | hlt
  · -- a_m < c_m: ε = Negative, -ε = Positive, boost = (1, 0).
    have hint : (Sigma.sigma X.1.1 (2 * m' + 2)).1 + 1 ≤ (Sigma.sigma Y.1.1 (2 * m' + 2)).1 :=
      add_one_le_sigma_fst_of_lt_even X.1.2 Y.1.2 hrev hlt
    refine branchA_R2_step X Y hXY m' g₁ hg₁NP hg₁rank hXg₁2 .Negative (by decide) ?_
    rw [GeneType.neg_negative, signature_ofRank_one_positive]
    refine ⟨?_, ?_⟩
    · change (1 : ℚ) + (signature (Chromosome.prime^[2 * m' + 2] X.1.1)).1 ≤
        (signature (Chromosome.prime^[2 * m' + 2] Y.1.1)).1
      have : (Sigma.sigma X.1.1 (2 * m' + 2)).1 =
          (signature (Chromosome.prime^[2 * m' + 2] X.1.1)).1 := rfl
      have h2 : (Sigma.sigma Y.1.1 (2 * m' + 2)).1 =
          (signature (Chromosome.prime^[2 * m' + 2] Y.1.1)).1 := rfl
      rw [this, h2] at hint; linarith
    · change (0 : ℚ) + (signature (Chromosome.prime^[2 * m' + 2] X.1.1)).2 ≤
        (signature (Chromosome.prime^[2 * m' + 2] Y.1.1)).2
      rw [zero_add]; exact hle_r.2
  · -- b_m < d_m: ε = Positive, -ε = Negative, boost = (0, 1).
    have hint : (Sigma.sigma X.1.1 (2 * m' + 2)).2 + 1 ≤ (Sigma.sigma Y.1.1 (2 * m' + 2)).2 :=
      add_one_le_sigma_snd_of_lt_even X.1.2 Y.1.2 hrev hlt
    refine branchA_R2_step X Y hXY m' g₁ hg₁NP hg₁rank hXg₁2 .Positive (by decide) ?_
    rw [GeneType.neg_positive, signature_ofRank_one_negative]
    refine ⟨?_, ?_⟩
    · change (0 : ℚ) + (signature (Chromosome.prime^[2 * m' + 2] X.1.1)).1 ≤
        (signature (Chromosome.prime^[2 * m' + 2] Y.1.1)).1
      rw [zero_add]; exact hle_r.1
    · change (1 : ℚ) + (signature (Chromosome.prime^[2 * m' + 2] X.1.1)).2 ≤
        (signature (Chromosome.prime^[2 * m' + 2] Y.1.1)).2
      have : (Sigma.sigma X.1.1 (2 * m' + 2)).2 =
          (signature (Chromosome.prime^[2 * m' + 2] X.1.1)).2 := rfl
      have h2 : (Sigma.sigma Y.1.1 (2 * m' + 2)).2 =
          (signature (Chromosome.prime^[2 * m' + 2] Y.1.1)).2 := rfl
      rw [this, h2] at hint; linarith

/-- **Branch A dichotomy.** For the minimal nonpolarized gene `g₁` (rank `2m'+2`,
even), disjointness gives `Y` no gene of rank `2m'+2`, hence `prime^[2m'+2] Y ≠ 0`,
and `(16.1)` forces `r_m < s_m`; so `a_m < c_m` or `b_m < d_m`. -/
lemma branchA_dichotomy {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' : ℕ) (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized)
    (hg₁rank : g₁.rank = 2 * m' + 2) (hXg₁ : 0 < X.1.1 g₁) :
    (Sigma.sigma X.1.1 (2 * m' + 2)).1 < (Sigma.sigma Y.1.1 (2 * m' + 2)).1 ∨
    (Sigma.sigma X.1.1 (2 * m' + 2)).2 < (Sigma.sigma Y.1.1 (2 * m' + 2)).2 := by
  have hcommon := hcommon
  push Not at hcommon hsigeq
  have hrev : Even (2 * m' + 2) := ⟨m' + 1, by ring⟩
  have hr1 : 1 ≤ 2 * m' + 2 := by omega
  have hY_no_gene : ∀ g : Gene, g.rank = 2 * m' + 2 → Y.1.1 g = 0 :=
    fun g hgr => Y_no_gene_of_even_rank_mix Y.1.2 hcommon g₁ hg₁NP hXg₁ hg₁rank hrev g hgr
  have h_half : (1 : ℚ) / 2 ≤ (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).1 := by
    have := half_le_signature_fst_of_contains_nonpolarized_mix hg₁NP hXg₁
    rwa [hg₁rank, show 2 * m' + 2 - 1 = 2 * m' + 1 from by omega] at this
  have hYr1 : Chromosome.prime^[2 * m' + 1] Y.1.1 ≠ 0 := by
    intro heq
    have hdom : (signature (Chromosome.prime^[2 * m' + 1] X.1.1)).1 ≤
        (signature (Chromosome.prime^[2 * m' + 1] Y.1.1)).1 :=
      (le_iff_dominates.mp hXY.le (2 * m' + 1)).1
    rw [heq, map_zero] at hdom
    simp only [Prod.fst_zero] at hdom; linarith
  have hYr : Chromosome.prime^[2 * m' + 2] Y.1.1 ≠ 0 :=
    prime_ne_zero_of_Y_no_gene_mix hr1 hY_no_gene
      (show Chromosome.prime^[(2 * m' + 2) - 1] Y.1.1 ≠ 0 by
        rwa [show 2 * m' + 2 - 1 = 2 * m' + 1 from by omega])
  have hsig_ne : Sigma.sigma X.1.1 (2 * m' + 2) ≠ Sigma.sigma Y.1.1 (2 * m' + 2) :=
    hsigeq (2 * m' + 2) (by omega) hYr
  have hle_r : Sigma.sigma X.1.1 (2 * m' + 2) ≤ Sigma.sigma Y.1.1 (2 * m' + 2) :=
    le_iff_dominates.mp hXY.le (2 * m' + 2)
  rcases lt_or_eq_of_le hle_r.1 with h | h
  · exact Or.inl h
  · rcases lt_or_eq_of_le hle_r.2 with h2 | h2
    · exact Or.inr h2
    · exact absurd (Prod.ext h h2) hsig_ne

/-- **Propagation core** of §16 Branch A Case 1.  From the strict start
`a_X(2m'+2) < a_Y(2m'+2)` (`ha_m`), the level-1 gap `ha`, and the fact that `X` has
no gene of rank strictly between `2m'+2` and `2n'+2` (`h2nd`, giving `X` a constant
sigma drop on the window), the §16 inequality chain
`c_i - c_{i+2} ≤ s_i - s_{i+1} ≤ s_0 - s_1 ≤ r_0 - r_1 - 1 = r_i - r_{i+1} = a_i - a_{i+2}`
propagates the strict *integer* inequality `a_X(j) + 1 ≤ a_Y(j)` to every even level
`j` in `[2m'+2, 2n'+2]`; and `Y` is nonzero throughout the window.  This is the hard,
reusable core; the assembly below consumes its two conclusions. -/
lemma exists_mutation_le_caseA_branchA_case1_propagate {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (_ : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (_ : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 2 ≤ g.rank)
    (ha_m : (Sigma.sigma X.1.1 (2 * m' + 2)).1 < (Sigma.sigma Y.1.1 (2 * m' + 2)).1) :
    (∀ j, 2 * m' + 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1) ∧
    (∀ j, 2 * m' + 2 ≤ j → j < 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0) := by
  refine ⟨?_, ?_⟩
  · -- Goal 1 (hprop_even): the §16 drop-chain telescoping (proved in Propagation.lean).
    exact branchA_case1_hprop_even X Y hXY ha m' n' hmn gm gk hgm_rank hgm_np hgk_rank hgk_np
      hXgm hXgk hne hmin h2nd ha_m
  · -- Goal 2 (hYwin): Y is nonzero on the window since X has gene gk of rank
    -- 2n'+2 > j, so prime^[j] X ≠ 0, and Y dominates X.
    intro j _ hj2
    have hXgk0 : 0 < X.1.1 gk :=
      lt_of_lt_of_le hXgk (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
    have hgk_supp : gk ∈ X.1.1.support :=
      Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hXgk0)
    have hXj : Chromosome.prime^[j] X.1.1 ≠ 0 := by
      intro hzero
      have hle := (prime_iterate_eq_zero_rank_le).mpr hzero gk hgk_supp
      rw [hgk_rank] at hle
      omega
    intro hYzero
    have hsig_le : signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
    rw [hYzero, map_zero] at hsig_le
    exact hXj (signature_eq_zero (le_antisymm hsig_le (signature_nonneg _)))

/-- **Assembly** of §16 Branch A Case 1, given the propagation outputs
(`hprop_even`, `hYwin`).  Builds the `type4` step `g(m)+g(k) → g⁻(m-1)+g⁺(k+1)`
(ε = `.Negative`) and proves `Z ≤ Y` over the window via
`sigma_type4_eq_before/_eq_after/_mid`: outside the window the source/target
signatures agree (reduce to `hXY`); inside, the even-level difference `(1,0)` is
absorbed by `hprop_even` and the odd-level difference `(1/2,1/2)` by
`half_le_sigma_diff_at_r` (its `≠` hypothesis from `hsigeq` + `hYwin`).  Template:
`MixLambdaPi.exists_mutation_le_disjoint_pair` in `Case3.lean`. -/
lemma exists_mutation_le_caseA_branchA_case1 {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_even : ∀ j, 2 * m' + 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1)
    (hYwin : ∀ j, 2 * m' + 2 ≤ j → j < 2 * n' + 2 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hsigeq
  have hε : GeneType.Negative ≠ .NonPolarized := by decide
  let Y4' : Mix (Lambda, Pi) := Y4 hmn hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * m' + 2) .NonPolarized = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm)
    rw [hgm_rank, hgm_np] at h
    exact h
  have hgk_eq : Gene.ofRank (2 * n' + 2) .NonPolarized = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk)
    rw [hgk_rank, hgk_np] at h
    exact h
  have hX4_val : (X4 hmn).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X4_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X4 hmn).1 + restval = X.1.1 := by
    rw [hX4_val]
    exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Lambda, Pi) := ⟨Y4'.1 + restval, add_mem Y4'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X4 hmn : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X4 hmn) Y4' rest_M
      (MixLambdaPi.Primitive.type4 GeneType.Negative hε hmn), ?_⟩
  change Y4'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X4 hmn).1) + signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) :=
    le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m' + 1
  · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
        signature (Chromosome.prime^[j] (X4 hmn).1) :=
      (sigma_type4_eq_before hmn hε (hj := hj)).symm
    rw [hY4X4, ← hdecomp]
    exact hXYj
  · have h_not_before : 2 * m' + 1 < j := by omega
    by_cases hj_after : 2 * n' + 3 ≤ j
    · have hY4X4 : signature (Chromosome.prime^[j] Y4'.1) =
          signature (Chromosome.prime^[j] (X4 hmn).1) :=
        (sigma_type4_eq_after hmn hε (hj := hj_after)).symm
      rw [hY4X4, ← hdecomp]
      exact hXYj
    · have h_mid : j < 2 * n' + 3 := by omega
      have hmid := sigma_type4_mid hmn hε h_not_before h_mid
      have hY4_eq : signature (Chromosome.prime^[j] Y4'.1) =
          signature (Chromosome.prime^[j] (X4 hmn).1) +
            (if Even (2 * n' + 2 - j) then signature (Gene.ofRank 1 (-GeneType.Negative))
             else ((1 : ℚ) / 2, (1 : ℚ) / 2)) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY4_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 2 - j)
      · rw [if_pos hpar]
        have h_even_j : Even j := by
          have hp : (2 * n' + 2 - j) % 2 = 0 := Nat.even_iff.mp hpar
          rw [Nat.even_iff]; omega
        have h_sig_pos : signature (Gene.ofRank 1 (-GeneType.Negative)) = ((1 : ℚ), (0 : ℚ)) := by
          rw [GeneType.neg_negative, signature_ofRank_one_positive]
        rw [h_sig_pos]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1 := by
          have h_sigma := hprop_even j (by omega) (by omega) h_even_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · change (signature (Chromosome.prime^[j] X.1.1)).1 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          exact h_sigXj
        · change (signature (Chromosome.prime^[j] X.1.1)).2 + 0 ≤
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

/-- **Assembly** of §16 Branch A Case 2 (`g₂ = g⁺(k)`), given the `b`-propagation
outputs.  Builds the `type5` step `g(m)+g⁺(k) → g⁺(m-1)+g(k+1)` (ε = `.Positive`) and
proves `Z ≤ Y` over the window `2m'+1 < j < 2n'+4` via `sigma_type5_eq_before/_eq_after/_mid`:
outside the window source/target agree; inside, the even-level difference `(0,1)` is
absorbed by `hprop_even` (on the `b`-component) and the odd-level `(1/2,1/2)` by
`half_le_sigma_diff_at_r`.  Mirror of `exists_mutation_le_caseA_branchA_case1`. -/
lemma exists_mutation_le_caseA_branchA_case2_assembly {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 3) (hgk_pos : gk.type = .Positive)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hprop_even : ∀ j, 2 * m' + 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2)
    (hYwin : ∀ j, 2 * m' + 2 ≤ j → j ≤ 2 * n' + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hsigeq
  have hε : GeneType.Positive ≠ .NonPolarized := by decide
  let Y5' : Mix (Lambda, Pi) := Y5 hmn hε
  let restval : Chromosome := X.1.1 - Finsupp.single gm 1 - Finsupp.single gk 1
  have rest_mem : restval ∈ Mix (Lambda, Pi) :=
    sub_mem_Mix_Lambda_Pi _ (sub_mem_Mix_Lambda_Pi _ X.1.2)
  let rest_M : Mix (Lambda, Pi) := ⟨restval, rest_mem⟩
  have hgm_eq : Gene.ofRank (2 * m' + 2) .NonPolarized = (Finsupp.single gm 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gm); rw [hgm_rank, hgm_np] at h; exact h
  have hgk_eq : Gene.ofRank (2 * n' + 3) .Positive = (Finsupp.single gk 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gk); rw [hgk_rank, hgk_pos] at h; exact h
  have hX5_val : (X5 hmn hε).1 = Finsupp.single gm 1 + Finsupp.single gk 1 := by
    rw [X5_eq, hgm_eq, hgk_eq]
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hX_eq : (X5 hmn hε).1 + restval = X.1.1 := by
    rw [hX5_val]; exact X_eq_X7_add_rest_mix hXgm hXgk' hne
  let Z : Mix (Lambda, Pi) := ⟨Y5'.1 + restval, add_mem Y5'.2 rest_mem⟩
  refine ⟨Z, (Subtype.ext hX_eq : (X5 hmn hε : Mix (Lambda, Pi)) + rest_M = X.1) ▸
    MixLambdaPi.Step.mk (X5 hmn hε) Y5' rest_M
      (MixLambdaPi.Primitive.type5 GeneType.Positive hε hmn), ?_⟩
  change Y5'.1 + restval ≤ Y.1.1
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp : signature (Chromosome.prime^[j] X.1.1) =
      signature (Chromosome.prime^[j] (X5 hmn hε).1) +
        signature (Chromosome.prime^[j] restval) := by
    rw [← hX_eq, iterate_map_add, map_add]
  have hXYj : signature (Chromosome.prime^[j] X.1.1) ≤
      signature (Chromosome.prime^[j] Y.1.1) := le_iff_dominates.mp hXY.le j
  by_cases hj : j ≤ 2 * m' + 1
  · have h54 : signature (Chromosome.prime^[j] Y5'.1) =
        signature (Chromosome.prime^[j] (X5 hmn hε).1) :=
      (sigma_type5_eq_before hmn hε (hj := hj)).symm
    rw [h54, ← hdecomp]; exact hXYj
  · have h_not_before : 2 * m' + 1 < j := by omega
    by_cases hj_after : 2 * n' + 4 ≤ j
    · have h54 : signature (Chromosome.prime^[j] Y5'.1) =
          signature (Chromosome.prime^[j] (X5 hmn hε).1) :=
        (sigma_type5_eq_after hmn hε (hj := hj_after)).symm
      rw [h54, ← hdecomp]; exact hXYj
    · have h_mid : j < 2 * n' + 4 := by omega
      have hmid := sigma_type5_mid hmn hε h_not_before h_mid
      have hY5_eq : signature (Chromosome.prime^[j] Y5'.1) =
          signature (Chromosome.prime^[j] (X5 hmn hε).1) +
            (if Even (2 * n' + 3 - j) then ((1 : ℚ) / 2, (1 : ℚ) / 2)
             else signature (Gene.ofRank 1 (-GeneType.Positive))) :=
        sub_eq_iff_eq_add'.mp hmid
      rw [hY5_eq, add_right_comm, ← hdecomp]
      by_cases hpar : Even (2 * n' + 3 - j)
      · rw [if_pos hpar]
        have hodd_j : Odd j := by
          have hp : (2 * n' + 3 - j) % 2 = 0 := Nat.even_iff.mp hpar
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
          have hp : (2 * n' + 3 - j) % 2 = 1 :=
            Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hpar)
          rw [Nat.even_iff]; omega
        have h_sig_neg : signature (Gene.ofRank 1 (-GeneType.Positive)) = ((0 : ℚ), (1 : ℚ)) := by
          rw [GeneType.neg_positive, signature_ofRank_one_negative]
        rw [h_sig_neg]
        have h_sigXj : (signature (Chromosome.prime^[j] X.1.1)).2 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2 := by
          have hjle : j ≤ 2 * n' + 2 := by rcases h_even_j with ⟨t, rfl⟩; omega
          have h_sigma := hprop_even j (by omega) hjle h_even_j
          simpa [Sigma.sigma] using h_sigma
        refine ⟨?_, ?_⟩
        · change (signature (Chromosome.prime^[j] X.1.1)).1 + 0 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).1
          rw [add_zero]; exact hXYj.1
        · change (signature (Chromosome.prime^[j] X.1.1)).2 + 1 ≤
            (signature (Chromosome.prime^[j] Y.1.1)).2
          exact h_sigXj

/-- **b-propagation core for §16 Branch A Case 2.**  The `b`-component analogue of
`branchA_case1_hprop_even`, obtained by applying the gk-free `branchA_hprop_even_gen`
to `(-X, -Y)` (where `a_{-X} = b_X`) and transporting back.  Propagates `b_m < d_m`
to a full-unit `b`-gap at every even level of `[2m'+2, 2n'+2]`. -/
lemma branchA_case2_bprop {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm : Gene) (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgm1 : X.1.1 gm = 1)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 2 ≤ g.rank)
    (hb_m : (Sigma.sigma X.1.1 (2 * m' + 2)).2 < (Sigma.sigma Y.1.1 (2 * m' + 2)).2) :
    ∀ j, 2 * m' + 2 ≤ j → j ≤ 2 * n' + 2 → Even j →
        (Sigma.sigma X.1.1 j).2 + 1 ≤ (Sigma.sigma Y.1.1 j).2 := by
  have hg₁neg : (-gm : Gene) = gm :=
    Gene.ext (Gene.neg_rank gm) (by rw [Gene.neg_type, hgm_np]; rfl)
  set Xd : nMixLambdaPi N := ⟨- X.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, X.2]⟩ with Xd_def
  set Yd : nMixLambdaPi N := ⟨- Y.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, Y.2]⟩ with Yd_def
  have hXdYd : Xd.1 < Yd.1 := by change (- X.1) < (- Y.1); exact Chromosome.neg_lt_neg_iff.2 hXY
  have had : (Sigma.sigma Xd.1.1 1).1 < (Sigma.sigma Yd.1.1 1).1 := by
    change (signature (Chromosome.prime^[1] (- X.1.1))).1 <
      (signature (Chromosome.prime^[1] (- Y.1.1))).1
    rw [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
      signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    have hXsym : (signature (Chromosome.prime^[1] X.1.1)).1 =
        (signature (Chromosome.prime^[1] X.1.1)).2 :=
      signature_prime_iterate_odd_eq_components X.1.2 (by decide)
    have hYsym : (signature (Chromosome.prime^[1] Y.1.1)).1 =
        (signature (Chromosome.prime^[1] Y.1.1)).2 :=
      signature_prime_iterate_odd_eq_components Y.1.2 (by decide)
    rw [← hXsym, ← hYsym]; exact ha
  have hgm1_d : Xd.1.1 gm = 1 := by
    change (- X.1.1) gm = 1; rw [Chromosome.neg_apply, hg₁neg]; exact hgm1
  have hmin_d : ∀ g ∈ Xd.1.1.support, 2 * m' + 2 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff] at hg
    have hng : X.1.1 (-g) ≠ 0 := by
      change (- X.1.1) g ≠ 0 at hg; rwa [Chromosome.neg_apply] at hg
    have h := hmin (-g) (Finsupp.mem_support_iff.mpr hng); rwa [Gene.neg_rank] at h
  have hsingle_neg : ∀ g, (Finsupp.single gm 1 : Chromosome) g =
      (Finsupp.single gm 1 : Chromosome) (-g) := by
    intro g
    have hiff : (gm = g) ↔ (gm = -g) := by
      constructor
      · rintro rfl; exact hg₁neg.symm
      · intro h
        have h2 : -gm = g := by rw [h, neg_neg]
        rw [← hg₁neg]; exact h2
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : gm = g
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hval : ∀ g, (Xd.1.1 - Finsupp.single gm 1 : Chromosome) g
      = (X.1.1 - Finsupp.single gm 1 : Chromosome) (-g) := by
    intro g; rw [Finsupp.tsub_apply, Finsupp.tsub_apply, hsingle_neg g]; congr 1
  have h2nd_d : ∀ g ∈ (Xd.1.1 - Finsupp.single gm 1).support, 2 * n' + 2 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, hval g] at hg
    have h := h2nd (-g) (Finsupp.mem_support_iff.mpr hg); rwa [Gene.neg_rank] at h
  have ha_m_d : (Sigma.sigma Xd.1.1 (2 * m' + 2)).1 <
      (Sigma.sigma Yd.1.1 (2 * m' + 2)).1 := by
    change (signature (Chromosome.prime^[2 * m' + 2] (- X.1.1))).1 <
      (signature (Chromosome.prime^[2 * m' + 2] (- Y.1.1))).1
    rw [← @prime_iterate_neg (2 * m' + 2) X.1.1, ← @prime_iterate_neg (2 * m' + 2) Y.1.1,
      signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    exact hb_m
  have hgen := branchA_hprop_even_gen Xd Yd hXdYd had m' n' hmn gm hgm_rank hgm_np
    hgm1_d hmin_d h2nd_d ha_m_d
  intro j hj1 hj2 hej
  have hg := hgen j hj1 hj2 hej
  have hconvX : (Sigma.sigma Xd.1.1 j).1 = (Sigma.sigma X.1.1 j).2 := by
    change (signature (Chromosome.prime^[j] (- X.1.1))).1 =
      (signature (Chromosome.prime^[j] X.1.1)).2
    rw [← @prime_iterate_neg j X.1.1, signature_neg, Prod.fst_swap]
  have hconvY : (Sigma.sigma Yd.1.1 j).1 = (Sigma.sigma Y.1.1 j).2 := by
    change (signature (Chromosome.prime^[j] (- Y.1.1))).1 =
      (signature (Chromosome.prime^[j] Y.1.1)).2
    rw [← @prime_iterate_neg j Y.1.1, signature_neg, Prod.fst_swap]
  rw [hconvX, hconvY] at hg; exact hg

/-- **Top-boundary nonvanishing for §16 Branch A Case 2.**  `prime^[2n'+3] Y ≠ 0`.
If it vanished, `prime^[2n'+2] Y` would consist only of rank-1 genes, all polarized
(in `Mix (Lambda, Pi)`), and none positive — a positive one would be `g⁺(1)`, which by
`prime_iterate_coeff` traces to `Y gk` (zero by disjointness).  So its first signature
component is `0`, contradicting `a_X(2n'+2) ≥ 1` (the `g⁺(k)` residue) dominated by `Y`. -/
lemma branchA_case2_Ynonzero_top {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (n' : ℕ) (gk : Gene) (hgk_rank : gk.rank = 2 * n' + 3)
    (hgk_pos : gk.type = .Positive) (hXgk : 0 < X.1.1 gk) :
    Chromosome.prime^[2 * n' + 3] Y.1.1 ≠ 0 := by
  push Not at hcommon
  intro hYzero
  have haX : 1 ≤ (signature (Chromosome.prime^[2 * n' + 2] X.1.1)).1 := by
    have := one_le_signature_fst_of_contains_positive_mix X.1.2 hgk_pos hXgk
    rwa [hgk_rank, show 2 * n' + 3 - 1 = 2 * n' + 2 from by omega] at this
  have haY : 1 ≤ (signature (Chromosome.prime^[2 * n' + 2] Y.1.1)).1 :=
    le_trans haX (le_iff_dominates.mp hXY.le (2 * n' + 2)).1
  set W := Chromosome.prime^[2 * n' + 2] Y.1.1 with hWdef
  have hWprime : Chromosome.prime W = 0 := by
    rw [hWdef, ← Function.iterate_succ_apply' Chromosome.prime (2 * n' + 2) Y.1.1]
    exact hYzero
  have hWmem : W ∈ Mix (Lambda, Pi) := by
    have heven : Even (2 * n' + 2) := ⟨n' + 1, by ring⟩
    have h := prime_mem_Mix_Lambda_Pi_iterate Y.1.2 (2 * n' + 2)
    rwa [if_pos heven] at h
  have hWgenes : ∀ h ∈ W.support, h.signature.1 = 0 := by
    intro h hh
    have hr1 : h.rank = 1 := rank_one_of_prime_eq_zero hWprime hh
    have hpol : h.type ≠ .NonPolarized := by
      have hod : 0 < W.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos (by rw [hr1]; exact ⟨0, rfl⟩)]
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      exact IsPolarized_def'.mp (mem_Pi_iff.mp hWmem.2) h
        (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hod))
    have hnpos : h.type ≠ .Positive := by
      intro hpos
      have hWh : W h = Y.1.1 ⟨h.rank + (2 * n' + 2), h.type,
          Nat.le_add_right_of_le h.rank_pos⟩ := prime_iterate_coeff (2 * n' + 2) Y.1.1 h
      have hge : (⟨h.rank + (2 * n' + 2), h.type, Nat.le_add_right_of_le h.rank_pos⟩ : Gene) = gk :=
        Gene.ext (by change h.rank + (2 * n' + 2) = gk.rank; omega)
          (by change h.type = gk.type; rw [hpos, hgk_pos])
      rw [hge] at hWh
      have hYgk : Y.1.1 gk = 0 := Nat.le_zero.mp (hcommon gk hXgk)
      rw [hYgk] at hWh
      exact (Finsupp.mem_support_iff.mp hh) hWh
    have hneg : h.type = .Negative := by
      cases ht : h.type with
      | NonPolarized => exact absurd ht hpol
      | Positive => exact absurd ht hnpos
      | Negative => rfl
    rw [Gene.signature_of_negative hneg, if_neg (by rw [hr1]; decide)]
    simp [hr1]
  have hW0 : (signature W).1 = 0 := by
    rw [signature_fst, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro h hh
    rw [hWgenes h hh, smul_zero]
  rw [hW0] at haY
  linarith

/-- **§16 bottom-chain derivation of `b_m < d_m`** for Branch A Case 2 (`m = 2m'+2 ≥ 2`).
`b_Y(2m')-b_Y(2m'+2) ≤ s_Y(2m')-s_Y(2m'+1) ≤ s_Y(0)-s_Y(1) < r_X(0)-r_X(1) =
b_X(2m')-b_X(2m'+2)`, combined with `b_X(2m') ≤ b_Y(2m')`, gives `b_X(2m'+2) < b_Y(2m'+2)`.
Uses `cond_15_6`, rank antitonicity, the level-1 gap, and `twostep_snd = cells`. -/
lemma branchA_case2_bm_lt {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' : ℕ) (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank) :
    (Sigma.sigma X.1.1 (2 * m' + 2)).2 < (Sigma.sigma Y.1.1 (2 * m' + 2)).2 := by
  have heven : Even (2 * m') := ⟨m', by ring⟩
  have hcond := cond_15_6_Mix_Lambda_Pi Y.1.2 (2 * m')
  rw [if_pos heven] at hcond
  have hdrop := rank_drop_le Y.1.2 (2 * m')
  have hbX := twostep_snd (W := X.1.1) (i := 2 * m') (fun g hg => hmin g hg)
  have hcells : (X.1.1.rank : ℚ) - ((Chromosome.prime^[1] X.1.1).rank : ℚ) =
      X.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [Function.iterate_one]; exact cells
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
    simpa [Sigma.sigma] using this
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
    simpa [Sigma.sigma] using this
  have hXrank : (X.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast X.2
  have hYrank : (Y.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast Y.2
  have hb1 : (Sigma.sigma X.1.1 1).2 ≤ (Sigma.sigma Y.1.1 1).2 :=
    (le_iff_dominates.mp hXY.le 1).2
  have hbX2m : (Sigma.sigma X.1.1 (2 * m')).2 ≤ (Sigma.sigma Y.1.1 (2 * m')).2 :=
    (le_iff_dominates.mp hXY.le (2 * m')).2
  linarith

/-- `a`-component analogue of `branchA_case2_bm_lt`: derives `a_m < c_m` (for the
`g₂ = g⁻` charge via sign-duality). -/
lemma branchA_case2_am_lt {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' : ℕ) (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank) :
    (Sigma.sigma X.1.1 (2 * m' + 2)).1 < (Sigma.sigma Y.1.1 (2 * m' + 2)).1 := by
  have heven : Even (2 * m') := ⟨m', by ring⟩
  have hcond := cond_15_7_Mix_Lambda_Pi Y.1.2 (2 * m')
  rw [if_pos heven] at hcond
  have hdrop := rank_drop_le Y.1.2 (2 * m')
  have haX := twostep (W := X.1.1) (i := 2 * m') (fun g hg => hmin g hg)
  have hcells : (X.1.1.rank : ℚ) - ((Chromosome.prime^[1] X.1.1).rank : ℚ) =
      X.1.1.sum (fun _ m => (m : ℚ)) := by
    rw [Function.iterate_one]; exact cells
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
    simpa [Sigma.sigma] using this
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hsY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (Y.1.1.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
    simpa [Sigma.sigma] using this
  have hXrank : (X.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast X.2
  have hYrank : (Y.1.1.rank : ℚ) = (N : ℚ) := by exact_mod_cast Y.2
  have hb1 : (Sigma.sigma X.1.1 1).2 ≤ (Sigma.sigma Y.1.1 1).2 :=
    (le_iff_dominates.mp hXY.le 1).2
  have haX2m : (Sigma.sigma X.1.1 (2 * m')).1 ≤ (Sigma.sigma Y.1.1 (2 * m')).1 :=
    (le_iff_dominates.mp hXY.le (2 * m')).1
  linarith
lemma branchA_case2_full {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene) (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 3) (hgk_pos : gk.type = .Positive)
    (hgm1 : X.1.1 gm = 1) (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 3 ≤ g.rank)
    (hb_m : (Sigma.sigma X.1.1 (2 * m' + 2)).2 < (Sigma.sigma Y.1.1 (2 * m' + 2)).2) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gm ≠ gk := by intro h; rw [h, hgk_rank] at hgm_rank; omega
  have hXgk' : 0 < X.1.1 gk := by
    have hval : (X.1.1 - Finsupp.single gm 1 : Chromosome) gk = X.1.1 gk := by
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
    rwa [hval] at hXgk
  have hprop := branchA_case2_bprop X Y hXY ha m' n' hmn gm hgm_rank hgm_np hgm1 hmin
    (fun g hg => le_trans (by omega) (h2nd g hg)) hb_m
  have hYwin : ∀ j, 2 * m' + 2 ≤ j → j ≤ 2 * n' + 3 → Chromosome.prime^[j] Y.1.1 ≠ 0 := by
    intro j _ hj2
    by_cases hjtop : j = 2 * n' + 3
    · subst hjtop
      exact branchA_case2_Ynonzero_top X Y hXY hcommon n' gk hgk_rank hgk_pos hXgk'
    · intro hYzero
      have hXj : Chromosome.prime^[j] X.1.1 ≠ 0 := by
        intro hXzero
        have hle := prime_iterate_eq_zero_rank_le.mpr hXzero gk
          (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hXgk'))
        rw [hgk_rank] at hle; omega
      have hsig_le := le_iff_dominates.mp hXY.le j
      rw [hYzero, map_zero] at hsig_le
      exact hXj (signature_eq_zero (le_antisymm hsig_le (signature_nonneg _)))
  exact exists_mutation_le_caseA_branchA_case2_assembly X Y hXY hsigeq m' n' hmn gm gk
    hgm_rank hgm_np hgk_rank hgk_pos hXgm hXgk hne hprop hYwin

/-- **Branch A Case 1 driver.** Chains the propagation core and the type4 assembly:
given the minimal nonpolarized gene `gm` (rank `2m'+2`, multiplicity one), a second
nonpolarized gene `gk` (rank `2n'+2`, with `m' < n'`) of minimal rank in `X - gm`, and
the strict start `a_X(m) < a_Y(m)`, produces the mutation `Z ≤ Y`.  This is the fully
wired §16 Branch A Case 1 (`g₂` nonpolarized, `a_m < c_m`). -/
lemma exists_mutation_le_caseA_branchA_case1_full {N : ℕ}
    (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' n' : ℕ) (hmn : m' < n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 2) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 2 ≤ g.rank)
    (ha_m : (Sigma.sigma X.1.1 (2 * m' + 2)).1 < (Sigma.sigma Y.1.1 (2 * m' + 2)).1) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hne : gm ≠ gk := by
    intro h; rw [h, hgk_rank] at hgm_rank; omega
  obtain ⟨hprop_even, hYwin⟩ := exists_mutation_le_caseA_branchA_case1_propagate
    X Y hXY hcommon hsigeq ha m' n' (le_of_lt hmn) gm gk hgm_rank hgm_np hgk_rank hgk_np
    hXgm hXgk hne hmin h2nd ha_m
  exact exists_mutation_le_caseA_branchA_case1 X Y hXY hsigeq m' n' (le_of_lt hmn)
    gm gk hgm_rank hgm_np hgk_rank hgk_np hXgm hXgk hne hprop_even hYwin

/-- Branch A edge case: `X` is the single nonpolarized gene `g₁` (no second gene).
This is vacuous — `Y` of equal rank with `X ≤ Y` forces `Y = X` (the unique even-rank
gene shape), contradicting `X < Y`. -/
lemma branchA_single_gene (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (_ : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (g₁ : Gene) (_ : 0 < X.1.1 g₁) (hg₁NP : g₁.type = .NonPolarized)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 2) (_ : X.1.1 g₁ = 1)
    (hsingle : X.1.1 = Finsupp.single g₁ 1) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  exfalso
  have hg₁_rank_eq : g₁.rank = m + 2 := by
    have h : X.1.1.rank = g₁.rank := by rw [hsingle, rank_single, one_smul]
    rw [X.2] at h; exact h.symm
  have hX_ne : Chromosome.prime^[m + 1] X.1.1 ≠ 0 := by
    have hval : Chromosome.prime^[m + 1] X.1.1 = Gene.ofRank 1 g₁.type := by
      rw [hsingle, ← Gene.ofRank_eq_gene, prime_iterate_ofRank, hg₁_rank_eq,
        show m + 2 - (m + 1) = 1 from by omega]
    rw [hval, Gene.ofRank_eq_gene' (by norm_num)]
    simp
  have hY_ne : Chromosome.prime^[m + 1] Y.1.1 ≠ 0 := by
    intro hYzero
    have hle := le_iff_dominates.mp hXY.le (m + 1)
    rw [hYzero, map_zero] at hle
    exact hX_ne (signature_eq_zero (le_antisymm hle (signature_nonneg _)))
  have hmaxY_ge : m + 2 ≤ Y.1.1.maxRank := by
    by_contra hlt
    push Not at hlt
    exact hY_ne (prime_iterate_zero_of_maxRank_le (by omega))
  have hmaxY_le : Y.1.1.maxRank ≤ m + 2 := by
    have h := maxRank_le_rank Y.1.1; rwa [Y.2] at h
  have hmaxY : Y.1.1.maxRank = m + 2 := le_antisymm hmaxY_le hmaxY_ge
  obtain ⟨g₂, hg₂rank, hY_eq⟩ :=
    rank_eq_maxRank_single (by rw [Y.2, hmaxY]) (by rw [hmaxY]; omega)
  have hg₂rank' : g₂.rank = m + 2 := by rw [hg₂rank, hmaxY]
  have hg₂supp : g₂ ∈ Y.1.1.support := by rw [hY_eq]; simp
  have hg₂even : Even g₂.rank := by
    rw [hg₂rank', ← hg₁_rank_eq, hm']; exact ⟨m' + 1, by ring⟩
  have hg₂NP : g₂.type = .NonPolarized := by
    have hg₂Yeven : 0 < Y.1.1.evenPart g₂ := by
      rw [evenPart_eq, Finsupp.filter_apply, if_pos hg₂even]
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂supp)
    exact IsNonPolarized_def'.mp (mem_Lambda_iff.mp Y.1.2.1) g₂
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hg₂Yeven))
  have hg₂eq : g₂ = g₁ := Gene.ext (by rw [hg₂rank', hg₁_rank_eq]) (hg₂NP.trans hg₁NP.symm)
  rw [hg₂eq] at hY_eq
  have hXYeq : X.1.1 = Y.1.1 := by rw [hsingle, hY_eq]
  exact (ne_of_lt hXY) (Subtype.ext hXYeq)

/-- **Branch A Case 2 driver, `g₂ = g⁻(k)` charge** (via sign-duality to the `g⁺`
driver applied to `(-X, -Y)`). -/
lemma branchA_case2_full_neg {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene) (hgm_rank : gm.rank = 2 * m' + 2) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 3) (hgk_neg : gk.type = .Negative)
    (hgm1 : X.1.1 gm = 1) (hXgm : 0 < X.1.1 gm)
    (hXgk : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 3 ≤ g.rank) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg₁neg : (-gm : Gene) = gm :=
    Gene.ext (Gene.neg_rank gm) (by rw [Gene.neg_type, hgm_np]; rfl)
  set Xd : nMixLambdaPi N :=
    ⟨- X.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, X.2]⟩ with Xd_def
  set Yd : nMixLambdaPi N :=
    ⟨- Y.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, Y.2]⟩ with Yd_def
  have hXdYd : Xd.1 < Yd.1 := by change (- X.1) < (- Y.1); exact Chromosome.neg_lt_neg_iff.2 hXY
  have hcommond : ¬∃ g : Gene, 0 < Xd.1.1 g ∧ 0 < Yd.1.1 g := by
    refine fun ⟨g, hgX, hgY⟩ ↦ hcommon ⟨- g, ?_, ?_⟩
    · rw [← Chromosome.neg_apply]; convert hgX using 2; rfl
    · rw [← Chromosome.neg_apply]; convert hgY using 2; rfl
  have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Yd.1.1 ≠ 0 ∧
      Sigma.sigma Xd.1.1 k = Sigma.sigma Yd.1.1 k := by
    refine fun ⟨k, hkpos, hYd_ne, hsig⟩ ↦ hsigeq ⟨k, hkpos, ?_, ?_⟩
    · refine fun hYzero ↦ hYd_ne ?_
      change Chromosome.prime^[k] (- Y.1.1) = 0
      rw [← prime_iterate_neg, hYzero, _root_.neg_zero]
    · have hsig_swap : (signature (Chromosome.prime^[k] (- X.1.1))).swap =
        (signature (Chromosome.prime^[k] (- Y.1.1))).swap := congrArg Prod.swap hsig
      rwa [← @prime_iterate_neg k X.1.1, ← @prime_iterate_neg k Y.1.1,
        signature_neg, signature_neg, Prod.swap_swap, Prod.swap_swap] at hsig_swap
  have had : (Sigma.sigma Xd.1.1 1).1 < (Sigma.sigma Yd.1.1 1).1 := by
    change (signature (Chromosome.prime^[1] (- X.1.1))).1 <
      (signature (Chromosome.prime^[1] (- Y.1.1))).1
    rw [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
      signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    have hXsym : (signature (Chromosome.prime^[1] X.1.1)).1 =
        (signature (Chromosome.prime^[1] X.1.1)).2 :=
      signature_prime_iterate_odd_eq_components X.1.2 (by decide)
    have hYsym : (signature (Chromosome.prime^[1] Y.1.1)).1 =
        (signature (Chromosome.prime^[1] Y.1.1)).2 :=
      signature_prime_iterate_odd_eq_components Y.1.2 (by decide)
    rw [← hXsym, ← hYsym]; exact ha
  have hgm1_d : Xd.1.1 gm = 1 := by
    change (- X.1.1) gm = 1; rw [Chromosome.neg_apply, hg₁neg]; exact hgm1
  have hXgm_d : 0 < Xd.1.1 gm := by
    change 0 < (- X.1.1) gm; rw [Chromosome.neg_apply, hg₁neg]; exact hXgm
  have hsingle_neg : ∀ g, (Finsupp.single gm 1 : Chromosome) g =
      (Finsupp.single gm 1 : Chromosome) (-g) := by
    intro g
    have hiff : (gm = g) ↔ (gm = -g) := by
      constructor
      · rintro rfl; exact hg₁neg.symm
      · intro h
        have h2 : -gm = g := by rw [h, neg_neg]
        rw [← hg₁neg]; exact h2
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : gm = g
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hval : ∀ g, (Xd.1.1 - Finsupp.single gm 1 : Chromosome) g
      = (X.1.1 - Finsupp.single gm 1 : Chromosome) (-g) := by
    intro g; rw [Finsupp.tsub_apply, Finsupp.tsub_apply, hsingle_neg g]; congr 1
  have hgk'_rank : (-gk : Gene).rank = 2 * n' + 3 := by rw [Gene.neg_rank, hgk_rank]
  have hgk'_pos : (-gk : Gene).type = .Positive := by rw [Gene.neg_type, hgk_neg]; rfl
  have hXgk_d : 0 < (Xd.1.1 - Finsupp.single gm 1 : Chromosome) (-gk) := by
    rw [hval (-gk), neg_neg]; exact hXgk
  have hmin_d : ∀ g ∈ Xd.1.1.support, 2 * m' + 2 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff] at hg
    have hng : X.1.1 (-g) ≠ 0 := by
      change (- X.1.1) g ≠ 0 at hg; rwa [Chromosome.neg_apply] at hg
    have h := hmin (-g) (Finsupp.mem_support_iff.mpr hng); rwa [Gene.neg_rank] at h
  have h2nd_d : ∀ g ∈ (Xd.1.1 - Finsupp.single gm 1).support, 2 * n' + 3 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, hval g] at hg
    have h := h2nd (-g) (Finsupp.mem_support_iff.mpr hg); rwa [Gene.neg_rank] at h
  have ham := branchA_case2_am_lt X Y hXY ha m' hmin
  have hb_m_d : (Sigma.sigma Xd.1.1 (2 * m' + 2)).2 <
      (Sigma.sigma Yd.1.1 (2 * m' + 2)).2 := by
    change (signature (Chromosome.prime^[2 * m' + 2] (- X.1.1))).2 <
      (signature (Chromosome.prime^[2 * m' + 2] (- Y.1.1))).2
    rw [← @prime_iterate_neg (2 * m' + 2) X.1.1, ← @prime_iterate_neg (2 * m' + 2) Y.1.1,
      signature_neg, signature_neg, Prod.snd_swap, Prod.snd_swap]
    exact ham
  obtain ⟨W, hstepW, hWY⟩ := branchA_case2_full Xd Yd hXdYd hcommond hsigeqd had m' n' hmn
    gm (-gk) hgm_rank hgm_np hgk'_rank hgk'_pos hgm1_d hXgm_d hXgk_d hmin_d h2nd_d hb_m_d
  refine ⟨- W, ?_, ?_⟩
  · exact MixLambdaPi.Step.of_neg (by simpa only [neg_neg] using hstepW)
  · change (- W).1 ≤ Y.1.1
    rw [Mix.Lambda_Pi_neg_val]
    have hWY' : W.1 ≤ (- Y.1).1 := hWY
    rw [Mix.Lambda_Pi_neg_val] at hWY'
    simpa only [neg_neg] using Chromosome.neg_le_neg_iff.2 hWY'

/-- Branch A Case 2: the second gene `g₂` of `X - g₁` is polarized (§16 Case 2,
primitives type5/type6). -/
lemma branchA_case2 (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (_ : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 2) (hmult1 : X.1.1 g₁ = 1)
    (g₂ : Gene) (hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂)
    (hg₂min : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, g₂.rank ≤ g.rank)
    (hg₂pol : g₂.type ≠ .NonPolarized) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hXg₂' : 0 < X.1.1 g₂ :=
    lt_of_lt_of_le hXg₂ (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
  have hg₂supp : g₂ ∈ X.1.1.support := Finsupp.mem_support_iff.mpr (by omega)
  have hg₂odd : Odd g₂.rank := rank_odd_of_polarized X.1.2 hg₂pol hXg₂'
  obtain ⟨n', hn'⟩ : ∃ n', g₂.rank = 2 * n' + 3 := by
    have hge : 2 * m' + 2 ≤ g₂.rank := by rw [← hm']; exact hg₁min g₂ hg₂supp
    rcases hg₂odd with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  have hmn : m' ≤ n' := by
    have hge : 2 * m' + 2 ≤ g₂.rank := by rw [← hm']; exact hg₁min g₂ hg₂supp
    omega
  have hmin' : ∀ g ∈ X.1.1.support, 2 * m' + 2 ≤ g.rank := fun g hg => hm' ▸ hg₁min g hg
  have h2nd' : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * n' + 3 ≤ g.rank :=
    fun g hg => hn' ▸ hg₂min g hg
  cases hch : g₂.type with
  | NonPolarized => exact absurd hch hg₂pol
  | Positive =>
    exact branchA_case2_full X Y hXY hcommon hsigeq ha m' n' hmn g₁ g₂ hm' hg₁NP hn' hch
      hmult1 hXg₁ hXg₂ hmin' h2nd' (branchA_case2_bm_lt X Y hXY ha m' hmin')
  | Negative =>
    exact branchA_case2_full_neg X Y hXY hcommon hsigeq ha m' n' hmn g₁ g₂ hm' hg₁NP hn' hch
      hmult1 hXg₁ hXg₂ hmin' h2nd'

/-- Branch A Case 1, `b`-component sub-branch (`b_m < d_m`): the sign-dual of
`case1_full` (apply Case 1 to `-X`, `-Y`, then negate).  Remaining leaf. -/
lemma branchA_case1_neg (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 2) (_ : X.1.1 g₁ = 1)
    (g₂ : Gene) (n' : ℕ) (hg₂rank : g₂.rank = 2 * n' + 2)
    (hg₂NP : g₂.type = .NonPolarized) (hmn : m' < n')
    (hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂)
    (hg₂min : ∀ g ∈ (X.1.1 - Finsupp.single g₁ 1).support, 2 * n' + 2 ≤ g.rank)
    (hb_m : (Sigma.sigma X.1.1 (2 * m' + 2)).2 < (Sigma.sigma Y.1.1 (2 * m' + 2)).2) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  -- Nonpolarized genes are their own negatives.
  have hg₁neg : (-g₁ : Gene) = g₁ := Gene.ext (Gene.neg_rank g₁) (by rw [Gene.neg_type, hg₁NP]; rfl)
  have hg₂neg : (-g₂ : Gene) = g₂ := Gene.ext (Gene.neg_rank g₂) (by rw [Gene.neg_type, hg₂NP]; rfl)
  set Xd : nMixLambdaPi (m + 2) :=
    ⟨- X.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, X.2]⟩ with Xd_def
  set Yd : nMixLambdaPi (m + 2) :=
    ⟨- Y.1, by rw [Mix.Lambda_Pi_neg_val, rank_neg, Y.2]⟩ with Yd_def
  have hcommond : ¬∃ g : Gene, 0 < Xd.1.1 g ∧ 0 < Yd.1.1 g := by
    refine fun ⟨g, hgX, hgY⟩ ↦ hcommon ⟨- g, ?_, ?_⟩
    · rw [← Chromosome.neg_apply]; convert hgX using 2; rfl
    · rw [← Chromosome.neg_apply]; convert hgY using 2; rfl
  have hsigeqd : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Yd.1.1 ≠ 0 ∧
      Sigma.sigma Xd.1.1 k = Sigma.sigma Yd.1.1 k := by
    refine fun ⟨k, hkpos, hYd_ne, hsig⟩ ↦ hsigeq ⟨k, hkpos, ?_, ?_⟩
    · refine fun hYzero ↦ hYd_ne ?_
      change Chromosome.prime^[k] (- Y.1.1) = 0
      rw [← prime_iterate_neg, hYzero, _root_.neg_zero]
    · have hsig_swap : (signature (Chromosome.prime^[k] (- X.1.1))).swap =
        (signature (Chromosome.prime^[k] (- Y.1.1))).swap := congrArg Prod.swap hsig
      rwa [← @prime_iterate_neg k X.1.1, ← @prime_iterate_neg k Y.1.1,
        signature_neg, signature_neg, Prod.swap_swap, Prod.swap_swap] at hsig_swap
  have had : (Sigma.sigma Xd.1.1 1).1 < (Sigma.sigma Yd.1.1 1).1 := by
    change (signature (Chromosome.prime^[1] (- X.1.1))).1 <
      (signature (Chromosome.prime^[1] (- Y.1.1))).1
    rw [← @prime_iterate_neg 1 X.1.1, ← @prime_iterate_neg 1 Y.1.1,
      signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    have hXsym : (signature (Chromosome.prime^[1] X.1.1)).1 =
        (signature (Chromosome.prime^[1] X.1.1)).2 :=
      signature_prime_iterate_odd_eq_components X.1.2 (by decide)
    have hYsym : (signature (Chromosome.prime^[1] Y.1.1)).1 =
        (signature (Chromosome.prime^[1] Y.1.1)).2 :=
      signature_prime_iterate_odd_eq_components Y.1.2 (by decide)
    rw [← hXsym, ← hYsym]; exact ha
  -- single g₁ 1 is invariant under the `g ↦ -g` relabelling (since -g₁ = g₁).
  have hsingle_neg : ∀ g, (Finsupp.single g₁ 1 : Chromosome) g =
      (Finsupp.single g₁ 1 : Chromosome) (-g) := by
    intro g
    have hiff : (g₁ = g) ↔ (g₁ = -g) := by
      constructor
      · rintro rfl; exact hg₁neg.symm
      · intro h
        have h2 : -g₁ = g := by rw [h, neg_neg]
        rw [← hg₁neg]; exact h2
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : g₁ = g
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hval : ∀ g, (Xd.1.1 - Finsupp.single g₁ 1 : Chromosome) g
      = (X.1.1 - Finsupp.single g₁ 1 : Chromosome) (-g) := by
    intro g
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply, hsingle_neg g]
    congr 1
  have hXgm : 0 < Xd.1.1 g₁ := by
    change 0 < (- X.1.1) g₁
    rw [Chromosome.neg_apply, hg₁neg]; exact hXg₁
  have hXgk : 0 < (Xd.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := by
    rw [hval g₂, hg₂neg]; exact hXg₂
  have hmin : ∀ g ∈ Xd.1.1.support, 2 * m' + 2 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff] at hg
    have hng : X.1.1 (-g) ≠ 0 := by
      change (- X.1.1) g ≠ 0 at hg; rwa [Chromosome.neg_apply] at hg
    have h := hg₁min (-g) (Finsupp.mem_support_iff.mpr hng)
    rw [hm', Gene.neg_rank] at h; exact h
  have h2nd : ∀ g ∈ (Xd.1.1 - Finsupp.single g₁ 1).support, 2 * n' + 2 ≤ g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, hval g] at hg
    have h := hg₂min (-g) (Finsupp.mem_support_iff.mpr hg)
    rwa [Gene.neg_rank] at h
  have ha_m_d : (Sigma.sigma Xd.1.1 (2 * m' + 2)).1 <
      (Sigma.sigma Yd.1.1 (2 * m' + 2)).1 := by
    change (signature (Chromosome.prime^[2 * m' + 2] (- X.1.1))).1 <
      (signature (Chromosome.prime^[2 * m' + 2] (- Y.1.1))).1
    rw [← @prime_iterate_neg (2 * m' + 2) X.1.1, ← @prime_iterate_neg (2 * m' + 2) Y.1.1,
      signature_neg, signature_neg, Prod.fst_swap, Prod.fst_swap]
    exact hb_m
  have hXdYd : Xd.1 < Yd.1 := by
    change (- X.1) < (- Y.1)
    exact Chromosome.neg_lt_neg_iff.2 hXY
  obtain ⟨W, hstepW, hWY⟩ := exists_mutation_le_caseA_branchA_case1_full Xd Yd hXdYd
    hcommond hsigeqd had m' n' hmn g₁ g₂ hm' hg₁NP hg₂rank hg₂NP hXgm hXgk hmin h2nd ha_m_d
  refine ⟨- W, ?_, ?_⟩
  · exact MixLambdaPi.Step.of_neg (by simpa only [neg_neg] using hstepW)
  · change (- W).1 ≤ Y.1.1
    rw [Mix.Lambda_Pi_neg_val]
    have hWY' : W.1 ≤ (- Y.1).1 := hWY
    rw [Mix.Lambda_Pi_neg_val] at hWY'
    simpa only [neg_neg] using Chromosome.neg_le_neg_iff.2 hWY'

/-- Branch A, multiplicity-one sub-case (`X g₁ = 1`): the minimal nonpolarized gene
is simple.  If there is no second gene, the single-gene edge case is vacuous; otherwise
extract `g₂` of minimal rank in `X - g₁` and split on its polarization (§16 Cases 1–2).
The nonpolarized `a_m < c_m` leaf is fully wired through `case1_full`. -/
lemma branchA_mult_one (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized)
    (m' : ℕ) (hm' : g₁.rank = 2 * m' + 2) (hmult1 : X.1.1 g₁ = 1) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  by_cases hsupp : (X.1.1 - Finsupp.single g₁ 1).support.Nonempty
  · obtain ⟨g₂, hg₂mem, hg₂min⟩ := Finset.exists_min_image _ Gene.rank hsupp
    rw [Finsupp.mem_support_iff] at hg₂mem
    have hXg₂ : 0 < (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g₂ := Nat.pos_of_ne_zero hg₂mem
    have hg₂ne : g₂ ≠ g₁ := by
      intro h; subst h
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl, hmult1] at hXg₂
      simp at hXg₂
    have hXg₂' : 0 < X.1.1 g₂ :=
      lt_of_lt_of_le hXg₂ (by rw [Finsupp.tsub_apply]; exact Nat.sub_le _ _)
    have hg₂supp : g₂ ∈ X.1.1.support := Finsupp.mem_support_iff.mpr (by omega)
    by_cases hg₂pol : g₂.type = .NonPolarized
    · have hg₂even : Even g₂.rank := rank_even_of_nonpolarized_mem X.1.2 hg₂pol hXg₂'
      have hge : 2 * m' + 2 ≤ g₂.rank := by rw [← hm']; exact hg₁min g₂ hg₂supp
      have hne_rank : g₂.rank ≠ 2 * m' + 2 := by
        intro heq
        exact hg₂ne (Gene.ext (by rw [heq, hm']) (hg₂pol.trans hg₁NP.symm))
      obtain ⟨n', hn'⟩ : ∃ n', g₂.rank = 2 * n' + 2 := by
        obtain ⟨k, hk⟩ := hg₂even; exact ⟨k - 1, by omega⟩
      have hmn : m' < n' := by omega
      rcases branchA_dichotomy X Y hXY hcommon hsigeq m' g₁ hg₁NP hm' hXg₁ with ha_m | hb_m
      · exact exists_mutation_le_caseA_branchA_case1_full X Y hXY hcommon hsigeq ha
          m' n' hmn g₁ g₂ hm' hg₁NP hn' hg₂pol hXg₁ hXg₂
          (fun g hg => hm' ▸ hg₁min g hg)
          (fun g hg => hn' ▸ hg₂min g hg) ha_m
      · exact branchA_case1_neg m X Y hXY hcommon hsigeq ha g₁ hXg₁ hg₁min hg₁NP m' hm'
          hmult1 g₂ n' hn' hg₂pol hmn hXg₂ (fun g hg => hn' ▸ hg₂min g hg) hb_m
    · exact branchA_case2 m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hg₁NP m' hm'
        hmult1 g₂ hXg₂ hg₂min hg₂pol
  · rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hsupp
    have hsingle : X.1.1 = Finsupp.single g₁ 1 := by
      ext g
      rcases eq_or_ne g g₁ with rfl | hgne
      · rw [Finsupp.single_apply, if_pos rfl, hmult1]
      · have hz : (X.1.1 - Finsupp.single g₁ 1 : Chromosome) g = 0 := by rw [hsupp]; rfl
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (fun h => hgne h.symm),
          Nat.sub_zero] at hz
        rw [hz, Finsupp.single_apply, if_neg (fun h => hgne h.symm)]
    exact branchA_single_gene m X Y hXY hcommon g₁ hXg₁ hg₁NP m' hm' hmult1 hsingle

/-- **Branch A** of §16 Case A: the minimal-rank gene `g₁` of `X` is nonpolarized
(`g₁ = g(m)`, so `m` is even).  Paper Cases 1–2: dispatch on whether `X ⊇ 2g(m)`. -/
lemma exists_mutation_le_caseA_branchA (m : ℕ)
    (X Y : nMixLambdaPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.1.1 ≠ 0 ∧
      Sigma.sigma X.1.1 k = Sigma.sigma Y.1.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧ 0 < X.1.1 g ∧ 0 < X.1.1 h)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hXg₁ : 0 < X.1.1 g₁)
    (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hg₁NP : g₁.type = .NonPolarized) :
    ∃ Z : Mix (Lambda, Pi), MixLambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨m', hm'⟩ : ∃ m', g₁.rank = 2 * m' + 2 := by
    have hev : Even g₁.rank := rank_even_of_nonpolarized_mem X.1.2 hg₁NP hXg₁
    have hpos : 1 ≤ g₁.rank := g₁.rank_pos
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  by_cases hmult : 2 ≤ X.1.1 g₁
  · exact branchA_R2 X Y hXY hcommon hsigeq m' g₁ hg₁NP hm' hmult
  · exact branchA_mult_one m X Y hXY hcommon hsigeq hXpn ha g₁ hXg₁ hg₁min hg₁NP m' hm'
      (by omega)

end MixLambdaPi
