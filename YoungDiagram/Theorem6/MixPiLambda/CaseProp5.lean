import YoungDiagram.Theorem6.MixPiLambda.Drops
import YoungDiagram.Theorem6.MixPiLambda.Propagation

/-!
# §16 "Case-5 style" level-1-anchored a-propagation for `Mix (Pi, Lambda)`.

Parity-mirror of the `MixLambdaPi/CaseBProp.lean` machinery, used by the Branch A
`g₃` sub-case (and later Branch B Case 4).  For `Mix (Pi, Lambda)` the relevant per-gene
identity is: at an even step `(i, i+1)` (`i ≥ 2`), the `a`-drop of a gene equals its
`b`-drop at the `(1, 2)` step — because positive/negative genes sit at even rank and
nonpolarized at odd rank.  Summing over `X` (whose nonpolarized/negative genes sit at
rank `1` or `≥ t`) gives a constant `X` a-drop.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- Per-gene exact identity behind the §16 g₃ `a`-drop constancy (`Mix (Pi, Lambda)`).
For even `i ≥ 2` and a gene of rank `r`, type `t` with the `Mix (Pi, Lambda)` parity
(`Pos/Neg ↦ even r`, `NP ↦ odd r`) where non-positive genes avoid the dead zone
`[2, i]` (`r ≤ 1` or `i+1 ≤ r`), the `a`-drop at the `(i, i+1)` step equals the `b`-drop
at the `(1, 2)` step. -/
lemma pergene_adrop_pl {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (r : ℕ) (t : GeneType)
    (hposeven : t = .Positive → Even r) (hnegeven : t = .Negative → Even r)
    (hsurv : t ≠ .Positive → (r ≤ 1 ∨ i + 1 ≤ r)) :
    (Gene.ofRank (r - i) t).signature.1 - (Gene.ofRank (r - (i + 1)) t).signature.1 =
    (Gene.ofRank (r - 1) t).signature.2 - (Gene.ofRank (r - 2) t).signature.2 := by
  match t with
  | .NonPolarized =>
    rcases hsurv (by decide) with hr | hr
    · -- collapsed: r ≤ 1, all four residues are rank 0
      rw [show r - i = 0 from by omega, show r - (i + 1) = 0 from by omega,
        show r - 1 = 0 from by omega, show r - 2 = 0 from by omega]
      simp
    · -- surviving: r ≥ i+1 ≥ 3
      rw [signature_ofRank_nonPolarized, signature_ofRank_nonPolarized,
        signature_ofRank_nonPolarized, signature_ofRank_nonPolarized]
      push_cast [Nat.cast_sub (show i ≤ r by omega), Nat.cast_sub (show i + 1 ≤ r by omega),
        Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_sub (show 2 ≤ r by omega)]
      ring
  | .Positive =>
    have hre : Even r := hposeven rfl
    -- positive genes (even rank) have `a`-drop 0 at every step; `b`-drop 0 at the (1,2) step
    by_cases hri : i + 1 ≤ r
    · -- surviving
      have h1 : (Gene.ofRank (r - i) .Positive).signature.1 -
          (Gene.ofRank (r - (i + 1)) .Positive).signature.1 = 0 := by
        have hk : 1 ≤ r - i := by omega
        have hstep := signature_ofRank_eq' (k := r - i) (ε := GeneType.Positive) hk (by decide)
        have he : r - i - 1 = r - (i + 1) := by omega
        rw [he] at hstep
        have heven : Even (r - i) := by
          rcases hre with ⟨s, hs⟩; rcases hi with ⟨u, hu⟩; rw [Nat.even_iff]; omega
        rw [hstep, if_pos heven, GeneType.neg_positive, signature_ofRank_one_negative]
        simp
      have h2 : (Gene.ofRank (r - 1) .Positive).signature.2 -
          (Gene.ofRank (r - 2) .Positive).signature.2 = 0 := by
        have hk : 1 ≤ r - 1 := by omega
        have hstep := signature_ofRank_eq' (k := r - 1) (ε := GeneType.Positive) hk (by decide)
        have he : r - 1 - 1 = r - 2 := by omega
        rw [he] at hstep
        have hodd : ¬ Even (r - 1) := by
          rcases hre with ⟨s, hs⟩; rw [Nat.not_even_iff_odd, Nat.odd_iff]; omega
        rw [hstep, if_neg hodd, signature_ofRank_one_positive]
        simp
      rw [h1, h2]
    · -- collapsed
      have hrle : r ≤ i := by omega
      have hLHS : (Gene.ofRank (r - i) .Positive).signature.1 -
          (Gene.ofRank (r - (i + 1)) .Positive).signature.1 = 0 := by
        rw [show r - i = 0 from by omega, show r - (i + 1) = 0 from by omega,
          signature_ofRank_zero]; simp
      have hRHS : (Gene.ofRank (r - 1) .Positive).signature.2 -
          (Gene.ofRank (r - 2) .Positive).signature.2 = 0 := by
        by_cases hr2 : 2 ≤ r
        · have hk : 1 ≤ r - 1 := by omega
          have hstep := signature_ofRank_eq' (k := r - 1) (ε := GeneType.Positive) hk (by decide)
          have he : r - 1 - 1 = r - 2 := by omega
          rw [he] at hstep
          have hodd : ¬ Even (r - 1) := by
            rcases hre with ⟨s, hs⟩; rw [Nat.not_even_iff_odd, Nat.odd_iff]; omega
          rw [hstep, if_neg hodd, signature_ofRank_one_positive]; simp
        · rw [show r - 1 = 0 from by omega, show r - 2 = 0 from by omega]; simp
      rw [hLHS, hRHS]
  | .Negative =>
    have hre : Even r := hnegeven rfl
    rcases hsurv (by decide) with hr | hr
    · -- collapsed: r ≤ 1, but Negative even ⇒ r = 0
      have hr0 : r = 0 := by rcases hre with ⟨s, hs⟩; omega
      rw [hr0]
      simp
    · -- surviving: negative even, a-drop at even step = 1 = b-drop at (1,2)
      have h1 : (Gene.ofRank (r - i) .Negative).signature.1 -
          (Gene.ofRank (r - (i + 1)) .Negative).signature.1 = 1 := by
        have hk : 1 ≤ r - i := by omega
        have hstep := signature_ofRank_eq' (k := r - i) (ε := GeneType.Negative) hk (by decide)
        have he : r - i - 1 = r - (i + 1) := by omega
        rw [he] at hstep
        have heven : Even (r - i) := by
          rcases hre with ⟨s, hs⟩; rcases hi with ⟨u, hu⟩; rw [Nat.even_iff]; omega
        rw [hstep, if_pos heven, GeneType.neg_negative, signature_ofRank_one_positive]
        simp
      have h2 : (Gene.ofRank (r - 1) .Negative).signature.2 -
          (Gene.ofRank (r - 2) .Negative).signature.2 = 1 := by
        have hk : 1 ≤ r - 1 := by omega
        have hstep := signature_ofRank_eq' (k := r - 1) (ε := GeneType.Negative) hk (by decide)
        have he : r - 1 - 1 = r - 2 := by omega
        rw [he] at hstep
        have hodd : ¬ Even (r - 1) := by
          rcases hre with ⟨s, hs⟩; rw [Nat.not_even_iff_odd, Nat.odd_iff]; omega
        rw [hstep, if_neg hodd, signature_ofRank_one_negative]
        simp
      rw [h1, h2]

/-- `signature (prime^[m] X)` as a sum over the genes of `X`. -/
private lemma sig_iterate_eq_sum (X : Chromosome) (m : ℕ) :
    signature (Chromosome.prime^[m] X) =
    X.sum (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature) := by
  cases m with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.sub_zero]
    rw [signature_def]
    apply Finsupp.sum_congr
    intro g _
    rw [Gene.ofRank_eq_gene]
    congr 1
    rw [signature_def, Finsupp.sum_single_index (by simp)]
    simp
  | succ k =>
    rw [signature_prime_iterate]
    apply Finsupp.sum_congr
    intro g _
    rw [primeGene_def, prime_iterate_ofRank]
    congr 3
    omega

private lemma sig_iterate_fst_sum (X : Chromosome) (m : ℕ) :
    (signature (Chromosome.prime^[m] X)).1 =
    X.sum (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature.1) := by
  rw [sig_iterate_eq_sum X m]
  exact map_finsuppSum (AddMonoidHom.fst ℚ ℚ) X
    (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature)

private lemma sig_iterate_snd_sum (X : Chromosome) (m : ℕ) :
    (signature (Chromosome.prime^[m] X)).2 =
    X.sum (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature.2) := by
  rw [sig_iterate_eq_sum X m]
  exact map_finsuppSum (AddMonoidHom.snd ℚ ℚ) X
    (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature)

/-- **§16 g₃ exact `a`-drop** (`Mix (Pi, Lambda)`).  For even `i ≥ 2`, with PL parity and
non-positive genes avoiding the dead zone `[2, i]`, the `a`-drop at `(i, i+1)` equals the
`b`-drop at `(1, 2)`. -/
lemma xdrop_eq_pl {X : Chromosome} {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i)
    (hpar : ∀ g ∈ X.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank))
    (hsurv : ∀ g ∈ X.support, g.type ≠ .Positive → (g.rank ≤ 1 ∨ i + 1 ≤ g.rank)) :
    (signature (Chromosome.prime^[i] X)).1 - (signature (Chromosome.prime^[i + 1] X)).1 =
    (signature (Chromosome.prime^[1] X)).2 - (signature (Chromosome.prime^[2] X)).2 := by
  rw [sig_iterate_fst_sum X i, sig_iterate_fst_sum X (i + 1),
    sig_iterate_snd_sum X 1, sig_iterate_snd_sum X 2]
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← smul_sub, ← smul_sub]
  congr 1
  have hp := hpar g hg
  have hs := hsurv g hg
  exact pergene_adrop_pl hi hi2 g.rank g.type hp.1 hp.2 hs

/-- Per-gene identity: for `r ≥ 2` with PL parity, the `a`-drop at `(0,1)` equals the
`b`-drop at `(1,2)`. -/
lemma pergene_xshift_pl (r : ℕ) (hr2 : 2 ≤ r) (t : GeneType)
    (hposeven : t = .Positive → Even r) (hnegeven : t = .Negative → Even r) :
    (Gene.ofRank r t).signature.1 - (Gene.ofRank (r - 1) t).signature.1 =
    (Gene.ofRank (r - 1) t).signature.2 - (Gene.ofRank (r - 2) t).signature.2 := by
  match t with
  | .NonPolarized =>
    simp only [signature_ofRank_nonPolarized]
    push_cast [Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_sub (show 2 ≤ r by omega)]
    ring
  | .Positive =>
    have hre : Even r := hposeven rfl
    have h1 : (Gene.ofRank r .Positive).signature.1 -
        (Gene.ofRank (r - 1) .Positive).signature.1 = 0 := by
      have hstep := signature_ofRank_eq' (k := r) (ε := GeneType.Positive) (by omega) (by decide)
      rw [hstep, if_pos hre, GeneType.neg_positive, signature_ofRank_one_negative]; simp
    have h2 : (Gene.ofRank (r - 1) .Positive).signature.2 -
        (Gene.ofRank (r - 2) .Positive).signature.2 = 0 := by
      have hstep := signature_ofRank_eq' (k := r - 1)
        (ε := GeneType.Positive) (by omega) (by decide)
      have he : r - 1 - 1 = r - 2 := by omega
      rw [he] at hstep
      have hodd : ¬ Even (r - 1) := by
        rcases hre with ⟨s, hs⟩; rw [Nat.not_even_iff_odd, Nat.odd_iff]; omega
      rw [hstep, if_neg hodd, signature_ofRank_one_positive]; simp
    rw [h1, h2]
  | .Negative =>
    have hre : Even r := hnegeven rfl
    have h1 : (Gene.ofRank r .Negative).signature.1 -
        (Gene.ofRank (r - 1) .Negative).signature.1 = 1 := by
      have hstep := signature_ofRank_eq' (k := r) (ε := GeneType.Negative) (by omega) (by decide)
      rw [hstep, if_pos hre, GeneType.neg_negative, signature_ofRank_one_positive]; simp
    have h2 : (Gene.ofRank (r - 1) .Negative).signature.2 -
        (Gene.ofRank (r - 2) .Negative).signature.2 = 1 := by
      have hstep := signature_ofRank_eq' (k := r - 1)
        (ε := GeneType.Negative) (by omega) (by decide)
      have he : r - 1 - 1 = r - 2 := by omega
      rw [he] at hstep
      have hodd : ¬ Even (r - 1) := by
        rcases hre with ⟨s, hs⟩; rw [Nat.not_even_iff_odd, Nat.odd_iff]; omega
      rw [hstep, if_neg hodd, signature_ofRank_one_negative]; simp
    rw [h1, h2]

/-- **§16 g₃ gap**: `a_X(0) - a_X(1) - (b_X(1) - b_X(2)) = 1/2`.  Only the unique rank-1
nonpolarized gene `g₁` (multiplicity one) contributes; all other genes (rank ≥ 2) have
`a`-drop`(0,1)` = `b`-drop`(1,2)`. -/
lemma xgap_pl {X : Chromosome} (g₁ : Gene)
    (hg₁NP : g₁.type = .NonPolarized) (hg₁rank : g₁.rank = 1) (hg₁mult : X g₁ = 1)
    (hg₁min : ∀ g ∈ X.support, g₁.rank ≤ g.rank)
    (hpar : ∀ g ∈ X.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank)) :
    (signature X).1 - (signature (Chromosome.prime^[1] X)).1 -
      ((signature (Chromosome.prime^[1] X)).2 - (signature (Chromosome.prime^[2] X)).2) =
      (1 : ℚ) / 2 := by
  have h0 : signature X = signature (Chromosome.prime^[0] X) := rfl
  rw [h0, sig_iterate_fst_sum X 0, sig_iterate_fst_sum X 1,
    sig_iterate_snd_sum X 1, sig_iterate_snd_sum X 2]
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hg₁mem : g₁ ∈ X.support := Finsupp.mem_support_iff.mpr (by omega)
  rw [Finset.sum_eq_single_of_mem g₁ hg₁mem]
  · -- the g₁ term equals 1/2
    rw [hg₁mult, hg₁NP, hg₁rank]
    simp only [Nat.cast_one, one_smul, Nat.sub_zero]
    simp [signature_ofRank_nonPolarized]
  · -- every other gene (rank ≥ 2) contributes 0
    intro g hg hgne
    have hrank2 : 2 ≤ g.rank := by
      rcases Nat.lt_or_ge g.rank 2 with h | h
      · exfalso
        have hge : g₁.rank ≤ g.rank := hg₁min g hg
        rw [hg₁rank] at hge
        have hr1 : g.rank = 1 := by omega
        have hgNP : g.type = .NonPolarized := by
          by_contra hgpol
          have hp := hpar g hg
          rcases (by cases hgt : g.type with
            | NonPolarized => exact absurd hgt hgpol
            | Positive => exact Or.inl (hp.1 hgt)
            | Negative => exact Or.inr (hp.2 hgt) : Even g.rank ∨ Even g.rank) with he | he <;>
            (rw [hr1] at he; exact absurd he (by decide))
        exact hgne (Gene.ext (by rw [hr1, hg₁rank]) (by rw [hgNP, hg₁NP]))
      · exact h
    have hgp := hpar g hg
    have hxs := pergene_xshift_pl g.rank hrank2 g.type hgp.1 hgp.2
    simp only [Nat.sub_zero]
    rw [← smul_sub, ← smul_sub, ← smul_sub, hxs, sub_self, smul_zero]

/-- `Y` `a`-component drop at even index is bounded by the bottom `a`-drop. -/
lemma adrop_even_le {Y : Chromosome} (hY : Y ∈ Mix (Pi, Lambda)) (t : ℕ) :
    (Sigma.sigma Y (2 * t)).1 - (Sigma.sigma Y (2 * t + 1)).1 ≤
      (Sigma.sigma Y 0).1 - (Sigma.sigma Y 1).1 := by
  induction t with
  | zero => simp
  | succ k ih =>
    have hodd := cond_15_6_Mix_Pi_Lambda hY (2 * k + 1)
    rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨k, by ring⟩),
      show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show 2 * k + 1 + 2 = 2 * k + 3 from by ring] at hodd
    have heven := cond_15_6_Mix_Pi_Lambda hY (2 * k)
    rw [if_pos ⟨k, by ring⟩] at heven
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
      show 2 * k + 2 + 1 = 2 * k + 3 from by ring]
    linarith

/-- **§16 g₃ level-1-anchored `a`-propagation** (`Mix (Pi, Lambda)`).  With `g₁` the unique
rank-1 (nonpolarized, multiplicity one) gene and all other non-positive genes of rank
`≥ T`, the strict start `a_X(1) < a_Y(1)` propagates to `a_X(j) + 1 ≤ a_Y(j)` for every odd
`j < T`.  The increment at each even step is `≥ 1/2` (gap), so a single step plus dominance
gives strictness. -/
lemma branchA_g3_aprop {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (g₁ : Gene) (hg₁NP : g₁.type = .NonPolarized) (hg₁rank : g₁.rank = 1)
    (hg₁mult : X.1.1 g₁ = 1) (hg₁min : ∀ g ∈ X.1.1.support, g₁.rank ≤ g.rank)
    (hpar : ∀ g ∈ X.1.1.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank))
    (T : ℕ) (hsurv : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → (g.rank ≤ 1 ∨ T ≤ g.rank)) :
    ∀ j, Odd j → j ≤ T → (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
  -- level-0 a-components agree
  have ha0 : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 := by
    have hXr : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      simpa [Sigma.sigma, X.2] using this
    have hYr : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      simpa [Sigma.sigma, Y.2] using this
    have h1 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 :=
      (le_iff_dominates.mp hXY.le 0).1
    have h2 : (Sigma.sigma X.1.1 0).2 ≤ (Sigma.sigma Y.1.1 0).2 :=
      (le_iff_dominates.mp hXY.le 0).2
    linarith
  have hgap := xgap_pl g₁ hg₁NP hg₁rank hg₁mult hg₁min hpar
  -- integral level-1 strict
  have ha1lt : (Sigma.sigma X.1.1 1).1 + 1 ≤ (Sigma.sigma Y.1.1 1).1 := by
    obtain ⟨zX, hzX⟩ := sig_fst_isInt_odd X.1.2 (by decide : Odd 1)
    obtain ⟨zY, hzY⟩ := sig_fst_isInt_odd Y.1.2 (by decide : Odd 1)
    rw [hzX, hzY] at ha ⊢
    have : zX < zY := by exact_mod_cast ha
    have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
    linarith
  -- single-step increment ≥ 1/2 at even i
  have hstep : ∀ i, Even i → 2 ≤ i → i < T →
      (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma X.1.1 i).1 + (1 : ℚ) / 2 ≤
        (Sigma.sigma Y.1.1 (i + 1)).1 - (Sigma.sigma X.1.1 (i + 1)).1 := by
    intro i hei hi2 hiT
    have hsurv' : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → (g.rank ≤ 1 ∨ i + 1 ≤ g.rank) :=
      fun g hg hgp => (hsurv g hg hgp).imp id (fun h => le_trans (by omega) h)
    have hxd := xdrop_eq_pl hei hi2 hpar hsurv'
    obtain ⟨t, ht⟩ := hei
    have hadrop := adrop_even_le Y.1.2 t
    rw [show 2 * t = i from by omega] at hadrop
    -- hxd : a_X(i) - a_X(i+1) = b_X(1) - b_X(2)
    -- hadrop : a_Y(i) - a_Y(i+1) ≤ a_Y(0) - a_Y(1)
    have hsX : (Sigma.sigma X.1.1 i).1 = (signature (Chromosome.prime^[i] X.1.1)).1 := rfl
    have hsX1 : (Sigma.sigma X.1.1 (i + 1)).1 =
        (signature (Chromosome.prime^[i + 1] X.1.1)).1 := rfl
    have hxd' : (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 1)).1 =
        (Sigma.sigma X.1.1 1).2 - (Sigma.sigma X.1.1 2).2 := by
      rw [hsX, hsX1]; exact hxd
    have hgap' : (Sigma.sigma X.1.1 0).1 - (Sigma.sigma X.1.1 1).1 -
        ((Sigma.sigma X.1.1 1).2 - (Sigma.sigma X.1.1 2).2) = (1 : ℚ) / 2 := hgap
    linarith [ha0, hgap', ha1lt, hadrop, hxd']
  intro j hoj hjT
  have hfpos : (Sigma.sigma X.1.1 j).1 < (Sigma.sigma Y.1.1 j).1 := by
    by_cases hj1 : j = 1
    · subst hj1; exact ha
    · have hj3 : 3 ≤ j := by rcases hoj with ⟨s, rfl⟩; omega
      have hjm1_even : Even (j - 1) := by rcases hoj with ⟨s, rfl⟩; rw [Nat.even_iff]; omega
      have hstep_j := hstep (j - 1) hjm1_even (by omega) (by omega)
      rw [show j - 1 + 1 = j from by omega] at hstep_j
      have hdom : (Sigma.sigma X.1.1 (j - 1)).1 ≤ (Sigma.sigma Y.1.1 (j - 1)).1 :=
        (le_iff_dominates.mp hXY.le (j - 1)).1
      linarith
  obtain ⟨zX, hzX⟩ := sig_fst_isInt_odd X.1.2 hoj
  obtain ⟨zY, hzY⟩ := sig_fst_isInt_odd Y.1.2 hoj
  rw [hzX, hzY] at hfpos ⊢
  have hz : zX < zY := by exact_mod_cast hfpos
  have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
  linarith

/-- **§16 Case 4 gap = 0**: when `X` has no rank-`1` gene, every gene (rank ≥ 2) has
`a`-drop`(0,1)` = `b`-drop`(1,2)`, so `a_X(0) - a_X(1) - (b_X(1) - b_X(2)) = 0`. -/
lemma xgap_zero_pl {X : Chromosome}
    (hmin2 : ∀ g ∈ X.support, 2 ≤ g.rank)
    (hpar : ∀ g ∈ X.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank)) :
    (signature X).1 - (signature (Chromosome.prime^[1] X)).1 -
      ((signature (Chromosome.prime^[1] X)).2 - (signature (Chromosome.prime^[2] X)).2) =
      0 := by
  have h0 : signature X = signature (Chromosome.prime^[0] X) := rfl
  rw [h0, sig_iterate_fst_sum X 0, sig_iterate_fst_sum X 1,
    sig_iterate_snd_sum X 1, sig_iterate_snd_sum X 2]
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro g hg
  have hrank2 : 2 ≤ g.rank := hmin2 g hg
  have hgp := hpar g hg
  have hxs := pergene_xshift_pl g.rank hrank2 g.type hgp.1 hgp.2
  simp only [Nat.sub_zero]
  rw [← smul_sub, ← smul_sub, ← smul_sub, hxs, sub_self, smul_zero]

/-- **§16 Case 4 a-propagation** (`Mix (Pi, Lambda)`).  With `X` having minimal gene rank
`≥ 2` (no rank-`1` gene) and every nonpositive gene of rank `≥ k`, the strict integer start
`a_X(1) < a_Y(1)` propagates to `a_X(j) + 1 ≤ a_Y(j)` for every odd `j ≤ k`.  Single-step
bound (mirror of LP `branchB_case5_aprop_gen`): X's a-drop `a_X(j-1)-a_X(j) = b_X(1)-b_X(2)
= a_X(0)-a_X(1)` (gap = 0) strictly exceeds Y's a-drop (antitone, bounded by `a_Y(0)-a_Y(1)`). -/
lemma branchB_case4_aprop_gen {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (hmin2 : ∀ g ∈ X.1.1.support, 2 ≤ g.rank)
    (hpar : ∀ g ∈ X.1.1.support,
      (g.type = .Positive → Even g.rank) ∧ (g.type = .Negative → Even g.rank))
    (k : ℕ) (hk : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → k ≤ g.rank) :
    ∀ j, 1 ≤ j → j ≤ k → Odd j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
  have ha0 : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 := by
    have hXr : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      simpa [Sigma.sigma, X.2] using this
    have hYr : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
      have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      simpa [Sigma.sigma, Y.2] using this
    have h1 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 :=
      (le_iff_dominates.mp hXY.le 0).1
    have h2 : (Sigma.sigma X.1.1 0).2 ≤ (Sigma.sigma Y.1.1 0).2 :=
      (le_iff_dominates.mp hXY.le 0).2
    linarith
  have hgap0 : (Sigma.sigma X.1.1 0).1 - (Sigma.sigma X.1.1 1).1 -
      ((Sigma.sigma X.1.1 1).2 - (Sigma.sigma X.1.1 2).2) = 0 := xgap_zero_pl hmin2 hpar
  intro j hj1 hjk hoj
  by_cases hj1eq : j = 1
  · subst hj1eq
    obtain ⟨zX, hzX⟩ := sig_fst_isInt_odd X.1.2 (by decide : Odd 1)
    obtain ⟨zY, hzY⟩ := sig_fst_isInt_odd Y.1.2 (by decide : Odd 1)
    rw [hzX, hzY] at ha ⊢
    have hz : zX < zY := by exact_mod_cast ha
    have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
    linarith
  · have hj3 : 3 ≤ j := by rcases hoj with ⟨r, rfl⟩; omega
    have hjm1_even : Even (j - 1) := by rcases hoj with ⟨r, rfl⟩; exact ⟨r, by omega⟩
    have hsurv' : ∀ g ∈ X.1.1.support, g.type ≠ .Positive →
        (g.rank ≤ 1 ∨ (j - 1) + 1 ≤ g.rank) :=
      fun g hg hgnp => Or.inr (by have := hk g hg hgnp; omega)
    have hxd := xdrop_eq_pl hjm1_even (by omega) hpar hsurv'
    rw [show (j - 1) + 1 = j from by omega] at hxd
    have hxd' : (Sigma.sigma X.1.1 (j - 1)).1 - (Sigma.sigma X.1.1 j).1 =
        (Sigma.sigma X.1.1 1).2 - (Sigma.sigma X.1.1 2).2 := hxd
    obtain ⟨t, ht⟩ : ∃ t, j - 1 = 2 * t := by rcases hjm1_even with ⟨r, hr⟩; exact ⟨r, by omega⟩
    have hYanti := adrop_even_le Y.1.2 t
    rw [show 2 * t = j - 1 from ht.symm, show j - 1 + 1 = j from by omega] at hYanti
    have hD : (Sigma.sigma X.1.1 (j - 1)).1 ≤ (Sigma.sigma Y.1.1 (j - 1)).1 :=
      (le_iff_dominates.mp hXY.le (j - 1)).1
    have hlt : (Sigma.sigma X.1.1 j).1 < (Sigma.sigma Y.1.1 j).1 := by
      linarith [ha0, hgap0, hYanti, hxd', hD, ha]
    obtain ⟨zX, hzX⟩ := sig_fst_isInt_odd X.1.2 hoj
    obtain ⟨zY, hzY⟩ := sig_fst_isInt_odd Y.1.2 hoj
    rw [hzX, hzY] at hlt ⊢
    have hz : zX < zY := by exact_mod_cast hlt
    have : (zX : ℚ) + 1 ≤ zY := by exact_mod_cast (by omega : zX + 1 ≤ zY)
    linarith

end MixPiLambda
