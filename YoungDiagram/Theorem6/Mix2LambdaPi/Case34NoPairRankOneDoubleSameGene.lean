import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps
import YoungDiagram.Theorem6.Mix2LambdaPi.Case34NegPartner
import YoungDiagram.Theorem6.Mix2LambdaPi.Type14
import YoungDiagram.Theorem6.Mix2LambdaPi.Type16

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma same_gene_prime_iterate_Y_ne_of_X_gene_above
    {N j : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (g : Gene) (hgX : 0 < X.1.1 g) (hj : j < g.rank) :
    Chromosome.prime^[j] Y.1.1 ≠ 0 := by
  intro hYzero
  let z : Gene := ⟨g.rank - j, g.type, by omega⟩
  have hXj_pos : 0 < (Chromosome.prime^[j] X.1.1) z := by
    have hcoeff := prime_iterate_coeff j X.1.1 z
    change (Chromosome.prime^[j] X.1.1) z =
      X.1.1 ⟨z.rank + j, z.type, Nat.le_add_right_of_le z.rank_pos⟩ at hcoeff
    have hz_eq :
        (⟨z.rank + j, z.type, Nat.le_add_right_of_le z.rank_pos⟩ : Gene) = g := by
      apply Gene.ext
      · dsimp [z]
        omega
      · rfl
    rwa [hcoeff, hz_eq]
  have hle := le_iff_dominates.mp hXY.le j
  rw [hYzero, map_zero] at hle
  have hsig_zero :=
    signature_eq_zero (le_antisymm hle (signature_nonneg _))
  have hcoeff_zero : (Chromosome.prime^[j] X.1.1) z = 0 := by
    rw [hsig_zero]
    rfl
  omega

private lemma gene_signature_fst_nonneg (h : Gene) : 0 ≤ h.signature.1 := by
  have hge := Gene.signature_ge h
  have hr1 : (1 : ℚ) ≤ h.rank := by exact_mod_cast h.rank_pos
  have hbase : (0 : ℚ) ≤ ((h.rank : ℚ) - 1) / 2 := by nlinarith
  exact le_trans hbase hge.1

private lemma gene_signature_snd_nonneg (h : Gene) : 0 ≤ h.signature.2 := by
  have hge := Gene.signature_ge h
  have hr1 : (1 : ℚ) ≤ h.rank := by exact_mod_cast h.rank_pos
  have hbase : (0 : ℚ) ≤ ((h.rank : ℚ) - 1) / 2 := by nlinarith
  exact le_trans hbase hge.2

private lemma gene_signature_snd_eq_zero_iff_rank_one_positive (h : Gene)
    (hsnd : h.signature.2 = 0) : h.rank = 1 ∧ h.type = GeneType.Positive := by
  cases htype : h.type with
  | NonPolarized =>
      rw [Gene.signature_of_nonPolarized htype] at hsnd
      have hrpos : (0 : ℚ) < h.rank := by exact_mod_cast h.rank_pos
      nlinarith
  | Positive =>
      rw [Gene.signature_of_positive htype] at hsnd
      by_cases heven : Even h.rank
      · rw [if_pos heven] at hsnd
        have hrpos : (0 : ℚ) < h.rank := by exact_mod_cast h.rank_pos
        nlinarith
      · rw [if_neg heven] at hsnd
        have hr1 : h.rank = 1 := by
          have hcast : (h.rank : ℚ) = 1 := by nlinarith
          exact_mod_cast hcast
        exact ⟨hr1, rfl⟩
  | Negative =>
      rw [Gene.signature_of_negative htype] at hsnd
      by_cases heven : Even h.rank
      · rw [if_pos heven] at hsnd
        have hrpos : (0 : ℚ) < h.rank := by exact_mod_cast h.rank_pos
        nlinarith
      · rw [if_neg heven] at hsnd
        have hrpos : (0 : ℚ) < h.rank := by exact_mod_cast h.rank_pos
        nlinarith

private lemma gene_signature_fst_eq_zero_iff_rank_one_negative (h : Gene)
    (hfst : h.signature.1 = 0) : h.rank = 1 ∧ h.type = GeneType.Negative := by
  cases htype : h.type with
  | NonPolarized =>
      rw [Gene.signature_of_nonPolarized htype] at hfst
      have hrpos : (0 : ℚ) < h.rank := by exact_mod_cast h.rank_pos
      nlinarith
  | Positive =>
      rw [Gene.signature_of_positive htype] at hfst
      by_cases heven : Even h.rank
      · rw [if_pos heven] at hfst
        have hrpos : (0 : ℚ) < h.rank := by exact_mod_cast h.rank_pos
        nlinarith
      · rw [if_neg heven] at hfst
        have hrpos : (0 : ℚ) < h.rank := by exact_mod_cast h.rank_pos
        nlinarith
  | Negative =>
      rw [Gene.signature_of_negative htype] at hfst
      by_cases heven : Even h.rank
      · rw [if_pos heven] at hfst
        have hrpos : (0 : ℚ) < h.rank := by exact_mod_cast h.rank_pos
        nlinarith
      · rw [if_neg heven] at hfst
        have hr1 : h.rank = 1 := by
          have hcast : (h.rank : ℚ) = 1 := by nlinarith
          exact_mod_cast hcast
        exact ⟨hr1, rfl⟩

/-- §17 single-step alternating chain for `Mix (2 • Lambda, Pi)` (first
component of the level-1 gap vs. second component telescoped down): the mirror
of `Sigma.a1_ai_le_b0_bi_1` for the `Mix` conditions (15.6)/(15.7).  Used for the
paper's Case 3 monotone-growth argument. -/
private lemma mix_a1_ai_le_b0_bi_1 {Z : Chromosome} (hZ : Z ∈ Mix (2 • Lambda, Pi))
    {i : ℕ} (h : i ≥ 1) :
    (Sigma.sigma Z 0).2 - (Sigma.sigma Z (i - 1)).2 ≥
      (Sigma.sigma Z 1).1 - (Sigma.sigma Z i).1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => simp
  | succ j ih =>
    induction j with
    | zero =>
      have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi hZ 0
      rw [if_pos (by decide : Even 0)] at h
      simpa using h
    | succ j ih =>
      by_cases hei : Even (j + 2)
      · have hei1 : ¬ (Even (j + 1)) := Nat.even_add_one.mp hei
        have hstep : (Sigma.sigma Z (j + 1)).2 - (Sigma.sigma Z (j + 2)).2 ≥
            (Sigma.sigma Z (j + 2)).1 - (Sigma.sigma Z (j + 3)).1 := by
          have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi hZ (j + 1)
          rw [if_neg hei1] at h; exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
          show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
          show j + 3 - 1 = j + 2 from by omega]
        linarith
      · have hei1 : Even (j + 1) := by rwa [Nat.even_add_one, not_not] at hei
        have hstep : (Sigma.sigma Z (j + 1)).2 - (Sigma.sigma Z (j + 2)).2 ≥
            (Sigma.sigma Z (j + 2)).1 - (Sigma.sigma Z (j + 3)).1 := by
          have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi hZ (j + 1)
          rw [if_pos hei1] at h; exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
          show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
          show j + 3 - 1 = j + 2 from by omega]
        linarith

/-- Second-component mirror of `mix_a1_ai_le_b0_bi_1`. -/
private lemma mix_b1_bi_le_a0_ai_1 {Z : Chromosome} (hZ : Z ∈ Mix (2 • Lambda, Pi))
    {i : ℕ} (h : i ≥ 1) :
    (Sigma.sigma Z 0).1 - (Sigma.sigma Z (i - 1)).1 ≥
      (Sigma.sigma Z 1).2 - (Sigma.sigma Z i).2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => simp
  | succ j ih =>
    induction j with
    | zero =>
      have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi hZ 0
      rw [if_pos (by decide : Even 0)] at h
      simpa using h
    | succ j ih =>
      by_cases hei : Even (j + 2)
      · have hei1 : ¬ (Even (j + 1)) := Nat.even_add_one.mp hei
        have hstep : (Sigma.sigma Z (j + 1)).1 - (Sigma.sigma Z (j + 2)).1 ≥
            (Sigma.sigma Z (j + 2)).2 - (Sigma.sigma Z (j + 3)).2 := by
          have h := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi hZ (j + 1)
          rw [if_neg hei1] at h; exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
          show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
          show j + 3 - 1 = j + 2 from by omega]
        linarith
      · have hei1 : Even (j + 1) := by rwa [Nat.even_add_one, not_not] at hei
        have hstep : (Sigma.sigma Z (j + 1)).1 - (Sigma.sigma Z (j + 2)).1 ≥
            (Sigma.sigma Z (j + 2)).2 - (Sigma.sigma Z (j + 3)).2 := by
          have h := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi hZ (j + 1)
          rw [if_pos hei1] at h; exact h
        have ih' := ih (by omega)
        simp only [show 1 + (j + 1) = j + 2 from by omega,
          show j + 2 - 1 = j + 1 from by omega] at ih'
        simp only [show 1 + (j + 1 + 1) = j + 3 from by omega,
          show j + 3 - 1 = j + 2 from by omega]
        linarith

/-- Sigma columns of `-X` are the swapped columns of `X`. -/
private lemma sg_sigma_neg_swap (X : Chromosome) (k : ℕ) :
    Sigma.sigma (-X) k = (Sigma.sigma X k).swap := by
  simp only [Sigma.sigma, ← Chromosome.prime_iterate_neg, signature_neg]

/-- Second-component X-side telescoping identity, the negative-family mirror of
`Sigma.b0_bi_eq_a1_ai1`: when every gene of rank `≤ i` is negative, the
first-component prefix drop equals the second-component shifted drop. -/
private lemma sg_a0_ai_eq_b1_bi1 {X : Chromosome} (hX : X ∈ Variety.Pi) (i : ℕ)
    (hg : ∀ g ∈ X.support, g.rank ≤ i → g.type = .Negative) :
    (Sigma.sigma X 0).1 - (Sigma.sigma X i).1 =
      (Sigma.sigma X 1).2 - (Sigma.sigma X (i + 1)).2 := by
  have hnegX : (-X) ∈ Variety.Pi :=
    Variety.mem_Pi_iff.mpr
      (Chromosome.IsPolarized_iff_neg_polarized.mp (Variety.mem_Pi_iff.mp hX))
  have hgneg : ∀ g ∈ (-X).support, g.rank ≤ i → g.type = .Positive := by
    intro g hg_supp hrank
    rw [Finsupp.mem_support_iff, Chromosome.neg_apply] at hg_supp
    have hgX : (-g) ∈ X.support := Finsupp.mem_support_iff.mpr hg_supp
    have hneg := hg (-g) hgX (by rwa [Gene.neg_rank])
    have : -(g.type) = GeneType.Negative := by rw [← Gene.neg_type]; exact hneg
    cases hgt : g.type <;> simp_all
  have h := Sigma.b0_bi_eq_a1_ai1 (-X) hnegX i hgneg
  simp only [sg_sigma_neg_swap, Prod.snd_swap, Prod.fst_swap] at h
  exact h

/-- Removing a single negative gene of rank `≤ i` (with every other gene of rank
`≤ i` positive) drops the negative multiplicity count of `prime^[i]` by exactly
one.  This is the `neg_count_eq` bookkeeping with one exceptional negative gene. -/
private lemma sg_neg_count_kill_one {W : Chromosome} {gneg : Gene} {i : ℕ}
    (hgneg_one : W gneg = 1) (hgneg_type : gneg.type = .Negative)
    (hgneg_rank : gneg.rank ≤ i)
    (hothers : ∀ h ∈ W.support, h.rank ≤ i → h ≠ gneg → h.type = .Positive) :
    (Chromosome.prime^[i] W).sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
      W.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) - 1 := by
  set W' : Chromosome := W - Finsupp.single gneg 1 with hW'_def
  have hgpos : 0 < W gneg := by omega
  have hWsplit : W = W' + Finsupp.single gneg 1 := (sub_single_add_single_eq hgpos).symm
  have hnegadd : W.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) =
      W'.sum (fun g n => if g.type = .Negative then (n : ℚ) else 0) + 1 := by
    conv_lhs => rw [hWsplit]
    rw [Finsupp.sum_add_index (by intro g _; simp)
      (by intro g _ mm nn; split_ifs <;> push_cast <;> ring)]
    rw [Finsupp.sum_single_index (by simp)]
    simp [hgneg_type]
  have hkill : Chromosome.prime^[i] (Finsupp.single gneg 1) = 0 := by
    rw [← Gene.ofRank_eq_gene, prime_iterate_ofRank,
      show gneg.rank - i = 0 by omega, Gene.ofRank_zero]
  have hprime_eq : Chromosome.prime^[i] W = Chromosome.prime^[i] W' := by
    conv_lhs => rw [hWsplit]; rw [iterate_map_add, hkill, add_zero]
  have hW'pos : ∀ h ∈ W'.support, h.rank ≤ i → h.type = .Positive := by
    intro h hh hrank
    have hhne : h ≠ gneg := by
      intro he; subst he
      rw [hW'_def, Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_eq_same,
        hgneg_one] at hh
      simp at hh
    have hhW : h ∈ W.support := by
      rw [hW'_def, Finsupp.mem_support_iff, Finsupp.tsub_apply,
        Finsupp.single_apply, if_neg (fun he => hhne he.symm)] at hh
      exact Finsupp.mem_support_iff.mpr (by omega)
    exact hothers h hhW hrank hhne
  have hnegeq := Sigma.neg_count_eq (X := W') i hW'pos
  rw [hprime_eq, hnegeq, hnegadd]; ring

/-- Off-by-one telescoping identity: when a single opposite-sign (negative) gene
of rank `≤ i` gets annihilated by level `i` and all other genes of rank `≤ i` are
positive, the second-component prefix drop exceeds the shifted first-component
drop by exactly one.  This is `Sigma.b0_bi_eq_a1_ai1` with a `+1` correction. -/
private lemma sg_b0_bi_off_by_one {X : Chromosome} (hX : X ∈ Variety.Pi) {i : ℕ}
    {gneg : Gene} (hgneg_one : X gneg = 1) (hgneg_type : gneg.type = .Negative)
    (hgneg_rank : gneg.rank ≤ i)
    (hothers : ∀ h ∈ X.support, h.rank ≤ i → h ≠ gneg → h.type = .Positive) :
    (Sigma.sigma X 0).2 - (Sigma.sigma X i).2 =
      (Sigma.sigma X 1).1 - (Sigma.sigma X (i + 1)).1 + 1 := by
  have h0 := Sigma.bi_sum_ai1_eq_neg_count_1 X hX (i := 0)
  have hi := Sigma.bi_sum_ai1_eq_neg_count_1 X hX (i := i)
  have hkill := sg_neg_count_kill_one hgneg_one hgneg_type hgneg_rank hothers
  simp only [Sigma.sigma, Function.iterate_zero, id] at h0 hi ⊢
  rw [hkill] at hi
  linarith

/-- Negative-family mirror of `sg_b0_bi_off_by_one`: one opposite-sign (positive)
gene of rank `≤ i` killed, first-component prefix drop off by one. -/
private lemma sg_a0_ai_off_by_one {X : Chromosome} (hX : X ∈ Variety.Pi) {i : ℕ}
    {gpos : Gene} (hgpos_one : X gpos = 1) (hgpos_type : gpos.type = .Positive)
    (hgpos_rank : gpos.rank ≤ i)
    (hothers : ∀ h ∈ X.support, h.rank ≤ i → h ≠ gpos → h.type = .Negative) :
    (Sigma.sigma X 0).1 - (Sigma.sigma X i).1 =
      (Sigma.sigma X 1).2 - (Sigma.sigma X (i + 1)).2 + 1 := by
  have hnegX : (-X) ∈ Variety.Pi :=
    Variety.mem_Pi_iff.mpr
      (Chromosome.IsPolarized_iff_neg_polarized.mp (Variety.mem_Pi_iff.mp hX))
  have hkey := sg_b0_bi_off_by_one (X := -X) hnegX (i := i) (gneg := -gpos)
    (by rw [Chromosome.neg_apply, neg_neg]; exact hgpos_one)
    (by rw [Gene.neg_type, hgpos_type]; rfl)
    (by rw [Gene.neg_rank]; exact hgpos_rank)
    (by
      intro h hh hrank hne
      rw [Finsupp.mem_support_iff, Chromosome.neg_apply] at hh
      have hhX : (-h) ∈ X.support := Finsupp.mem_support_iff.mpr (by simpa using hh)
      have hhne : (-h) ≠ gpos := fun he => hne (by rw [← he, neg_neg])
      have hval := hothers (-h) hhX (by rwa [Gene.neg_rank]) hhne
      rw [Gene.neg_type] at hval
      cases hgt : h.type with
      | NonPolarized => rw [hgt] at hval; simp at hval
      | Positive => rfl
      | Negative => rw [hgt] at hval; simp at hval)
  rw [sg_sigma_neg_swap, sg_sigma_neg_swap, sg_sigma_neg_swap, sg_sigma_neg_swap] at hkey
  simpa [Prod.fst_swap, Prod.snd_swap] using hkey

lemma rank_one_double_same_gene_tail_cases
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_two : 2 ≤ X.1.1 g)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hXsig1_eq :
      (signature (Chromosome.prime^[1] X.1.1)).1 =
        (signature (Chromosome.prime^[1] X.1.1)).2)
    (hYsig1_eq :
      (signature (Chromosome.prime^[1] Y.1.1)).1 =
        (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hgap1 :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[1] X.1.1) ≤
        signature (Chromosome.prime^[1] Y.1.1))
    (restAfterDouble restAfterTriple tailAfterG : Chromosome)
    (hrestAfterDouble_eq :
      restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (hrestAfterDouble_ne : restAfterDouble ≠ 0)
    (hrestAfterDouble_mem : restAfterDouble ∈ Mix (2 • Lambda, Pi))
    (hprimeX_eq_restAfterDouble :
      Chromosome.prime^[1] X.1.1 =
        Chromosome.prime^[1] restAfterDouble)
    (hrestAfterDouble_total :
      restAfterDouble.sum (fun _ n => n) + 2 = X.1.1.sum (fun _ n => n))
    (hg₂_rest : 0 < restAfterDouble g₂)
    (hg₂min : ∀ g' : Gene, 0 < restAfterDouble g' → g₂.rank ≤ g'.rank)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_odd : Odd g₂.rank)
    (hX_rank_ge_three_of_ne_g :
      ∀ h : Gene, 0 < X.1.1 h → h ≠ g → 3 ≤ h.rank)
    (hg₂min_X_ne_g :
      ∀ h : Gene, 0 < X.1.1 h → h ≠ g → g₂.rank ≤ h.rank)
    (hg₂_same_extra : g₂ = g → 3 ≤ X.1.1 g)
    (hg₂_rank_ge_three_of_ne_g : g₂ ≠ g → 3 ≤ g₂.rank)
    (htype16_boundary :
      ∀ {q : ℕ} (gsingle : Gene),
        gsingle.type = -g.type →
        gsingle.rank = 2 * q + 1 →
        1 ≤ X.1.1 gsingle →
        (Y16 (Nat.zero_le q) hg_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
              Finsupp.single gsingle 1) ≤ Y.1.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (htype14_boundary :
      ∀ {q : ℕ} (gopp : Gene),
        gopp.type = -g.type →
        gopp.rank = 2 * q + 1 →
        2 ≤ X.1.1 gopp →
        (Y14 (Nat.zero_le q) hg_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
              Finsupp.single gopp 1 - Finsupp.single gopp 1) ≤ Y.1.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (hsame : g₂ = g)
    (hg_extra : 3 ≤ X.1.1 g)
    (hrestAfterTriple_eq :
      restAfterTriple =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
          Finsupp.single g 1)
    (hprimeX_eq_restAfterTriple :
      Chromosome.prime^[1] X.1.1 =
        Chromosome.prime^[1] restAfterTriple)
    (hrestAfterTriple_total :
      restAfterTriple.sum (fun _ n => n) + 3 = X.1.1.sum (fun _ n => n))
    (htailAfterG_def : tailAfterG = X.1.1 - Finsupp.single g (X.1.1 g))
    (htailAfterG_g_zero : tailAfterG g = 0)
    (htailAfterG_pos_X_ne :
      ∀ h : Gene, 0 < tailAfterG h → 0 < X.1.1 h ∧ h ≠ g)
      (htailAfterG_rank_ge_three :
        ∀ h : Gene, 0 < tailAfterG h → 3 ≤ h.rank) :
      (tailAfterG = 0 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) ∧
      (∀ gtail : Gene,
        0 < tailAfterG gtail →
        (∀ h : Gene, 0 < tailAfterG h → gtail.rank ≤ h.rank) →
        3 ≤ gtail.rank →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) := by
  have htail_empty_setup :
      tailAfterG = 0 →
        X.1.1 = Finsupp.single g (X.1.1 g) ∧
        X.1.1.rank = X.1.1 g ∧
        Chromosome.prime^[1] X.1.1 = 0 ∧
        Chromosome.prime^[1] Y.1.1 ≠ 0 ∧
        (2 : ℚ) ≤ ((Chromosome.prime^[1] Y.1.1).rank : ℚ) ∧
        (Chromosome.prime^[1] Y.1.1).rank < X.1.1 g := by
    intro htail_zero
    have hXeq : X.1.1 = Finsupp.single g (X.1.1 g) := by
      ext h
      have hz : tailAfterG h = 0 := by rw [htail_zero]; rfl
      rw [htailAfterG_def, Finsupp.tsub_apply, Finsupp.single_apply] at hz
      rw [Finsupp.single_apply]
      by_cases hh : g = h
      · rw [if_pos hh]
        subst hh
        rfl
      · rw [if_neg hh] at hz ⊢
        omega
    have hXrank : X.1.1.rank = X.1.1 g := by
      rw [hXeq, rank_single, hg_rank_one]
      simp
    have hprimeX_zero : Chromosome.prime^[1] X.1.1 = 0 := by
      rw [Function.iterate_one, hXeq, prime_single, hg_rank_one]
      simp
    have hprimeY_ne : Chromosome.prime^[1] Y.1.1 ≠ 0 := by
      intro hYzero
      rw [hprimeX_zero, hYzero] at hseed1
      simp at hseed1
    have hYprime_rank_ge_two :
        (2 : ℚ) ≤ ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
      have hsig_ge :
          ((1 : ℚ), (1 : ℚ)) ≤ signature (Chromosome.prime^[1] Y.1.1) := by
        simpa [Function.iterate_one, hprimeX_zero] using hgap1
      have hsum :=
        signature_sum_eq_rank (X := Chromosome.prime^[1] Y.1.1)
      rw [← hsum]
      nlinarith [hsig_ge.1, hsig_ge.2]
    have hYprime_rank_lt_Xg :
        (Chromosome.prime^[1] Y.1.1).rank < X.1.1 g := by
      have hYprime_lt_rank :
          (Chromosome.prime^[1] Y.1.1).rank < Y.1.1.rank :=
        prime_iterate_rank_lt_of_ne_zero (by omega) hprimeY_ne
      have hYrank_eq_Xg : Y.1.1.rank = X.1.1 g := by
        have hYrank_m : Y.1.1.rank = m + 2 := Y.2
        have hXrank_m : X.1.1.rank = m + 2 := X.2
        omega
      omega
    exact
      ⟨hXeq, hXrank, hprimeX_zero, hprimeY_ne, hYprime_rank_ge_two,
        hYprime_rank_lt_Xg⟩
  have htail_later_setup :
      ∀ gtail : Gene, 0 < tailAfterG gtail →
        0 < X.1.1 gtail ∧
        gtail ≠ g ∧
        gtail.type ≠ GeneType.NonPolarized ∧
        Odd gtail.rank ∧
        ∃ q : ℕ, gtail.rank = 2 * q + 3 := by
    intro gtail hgtail
    have hXgtail : 0 < X.1.1 gtail := (htailAfterG_pos_X_ne gtail hgtail).1
    have hne_gtail_g : gtail ≠ g := (htailAfterG_pos_X_ne gtail hgtail).2
    have hgtail_pol : gtail.type ≠ GeneType.NonPolarized :=
      IsPolarized_def'.mp hXpol gtail
        (Finsupp.mem_support_iff.mpr (ne_of_gt hXgtail))
    have hgtail_odd : Odd gtail.rank :=
      Mix2LambdaSection17.odd_rank_of_polarized_gene_mem_Mix_2Lambda_Pi
        X.1.2 hXgtail hgtail_pol
    have hgtail_rank_ge_three : 3 ≤ gtail.rank :=
      htailAfterG_rank_ge_three gtail hgtail
    have hgtail_odd_copy : Odd gtail.rank := hgtail_odd
    obtain ⟨r, hr⟩ := hgtail_odd
    have hr_pos : 0 < r := by omega
    refine ⟨hXgtail, hne_gtail_g, hgtail_pol, hgtail_odd_copy, ⟨r - 1, ?_⟩⟩
    omega
  constructor
  · intro htail_zero
    exfalso
    obtain ⟨hXeq, hXrank, hprimeX_zero, hprimeY_ne, _hYprime_ge_two,
      _hYprime_lt_Xg⟩ := htail_empty_setup htail_zero
    have hsig_single : ∀ (g : Gene) (n : ℕ),
        signature (Finsupp.single g n) = (n : ℚ) • g.signature := by
      intro g n
      rw [signature_def]
      exact Finsupp.sum_single_index (by simp)
    have hle0 := le_iff_dominates.mp hXY.le 0
    simp only [Function.iterate_zero, id_eq] at hle0
    have hsum : (signature X.1.1).1 + (signature X.1.1).2 =
        (signature Y.1.1).1 + (signature Y.1.1).2 := by
      rw [signature_sum_eq_rank, signature_sum_eq_rank, X.2, Y.2]
    have hsigeq : signature X.1.1 = signature Y.1.1 :=
      Prod.ext (le_antisymm hle0.1 (by linarith [hle0.2]))
        (le_antisymm hle0.2 (by linarith [hle0.1]))
    have hYprime_zero : Chromosome.prime^[1] Y.1.1 = 0 := by
      have hYrank_le_one : ∀ y ∈ Y.1.1.support, y.rank ≤ 1 := by
        cases htype : g.type with
        | NonPolarized => exact False.elim (hg_pol htype)
        | Positive =>
            have hgsig : g.signature = (1, 0) := by
              rw [Gene.signature_of_positive htype,
                if_neg (by rw [hg_rank_one]; decide), hg_rank_one]
              norm_num
            have hsigX : signature X.1.1 = ((X.1.1 g : ℚ), 0) := by
              rw [hXeq, hsig_single, hgsig]
              simp
            have hsigY_snd_zero : (signature Y.1.1).2 = 0 := by
              rw [← hsigeq, hsigX]
            rw [signature_snd, Finsupp.sum] at hsigY_snd_zero
            simp only [smul_eq_mul] at hsigY_snd_zero
            have hterm_zero :
                ∀ y ∈ Y.1.1.support,
                  (Y.1.1 y : ℚ) * y.signature.2 = 0 := by
              intro y hy
              have hle :
                  (Y.1.1 y : ℚ) * y.signature.2 ≤
                    ∑ x ∈ Y.1.1.support, (Y.1.1 x : ℚ) * x.signature.2 :=
                Finset.single_le_sum
                  (fun x _hx =>
                    mul_nonneg (Nat.cast_nonneg _) (gene_signature_snd_nonneg x))
                  hy
              have hge : 0 ≤ (Y.1.1 y : ℚ) * y.signature.2 :=
                mul_nonneg (Nat.cast_nonneg _) (gene_signature_snd_nonneg y)
              linarith
            intro y hy
            have hy_pos : 0 < Y.1.1 y :=
              Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hy)
            have hy_sig_snd_zero : y.signature.2 = 0 := by
              have hz := hterm_zero y hy
              have hcoeff : (Y.1.1 y : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hy_pos
              exact mul_eq_zero.mp hz |>.resolve_left hcoeff
            exact (gene_signature_snd_eq_zero_iff_rank_one_positive y hy_sig_snd_zero).1.le
        | Negative =>
            have hgsig : g.signature = (0, 1) := by
              rw [Gene.signature_of_negative htype,
                if_neg (by rw [hg_rank_one]; decide), hg_rank_one]
              norm_num
            have hsigX : signature X.1.1 = (0, (X.1.1 g : ℚ)) := by
              rw [hXeq, hsig_single, hgsig]
              simp
            have hsigY_fst_zero : (signature Y.1.1).1 = 0 := by
              rw [← hsigeq, hsigX]
            rw [signature_fst, Finsupp.sum] at hsigY_fst_zero
            simp only [smul_eq_mul] at hsigY_fst_zero
            have hterm_zero :
                ∀ y ∈ Y.1.1.support,
                  (Y.1.1 y : ℚ) * y.signature.1 = 0 := by
              intro y hy
              have hle :
                  (Y.1.1 y : ℚ) * y.signature.1 ≤
                    ∑ x ∈ Y.1.1.support, (Y.1.1 x : ℚ) * x.signature.1 :=
                Finset.single_le_sum
                  (fun x _hx =>
                    mul_nonneg (Nat.cast_nonneg _) (gene_signature_fst_nonneg x))
                  hy
              have hge : 0 ≤ (Y.1.1 y : ℚ) * y.signature.1 :=
                mul_nonneg (Nat.cast_nonneg _) (gene_signature_fst_nonneg y)
              linarith
            intro y hy
            have hy_pos : 0 < Y.1.1 y :=
              Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hy)
            have hy_sig_fst_zero : y.signature.1 = 0 := by
              have hz := hterm_zero y hy
              have hcoeff : (Y.1.1 y : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hy_pos
              exact mul_eq_zero.mp hz |>.resolve_left hcoeff
            exact (gene_signature_fst_eq_zero_iff_rank_one_negative y hy_sig_fst_zero).1.le
      exact prime_iterate_eq_zero_rank_le.1 hYrank_le_one
    exact hprimeY_ne hYprime_zero
  · intro gtail hgtail hgtail_min hgtail_rank
    obtain ⟨hXgtail, hne_gtail_g, hgtail_pol, hgtail_odd,
      qtail, hgtail_rank_q⟩ := htail_later_setup gtail hgtail
    have htail_pos_of_X_ne_g :
        ∀ h : Gene, 0 < X.1.1 h → h ≠ g → 0 < tailAfterG h := by
      intro h hh hne_hg
      rw [htailAfterG_def, Finsupp.tsub_apply, Finsupp.single_apply,
        if_neg (fun hg_eq => hne_hg hg_eq.symm)]
      exact hh
    have hgtail_min_X_ne_g :
        ∀ h : Gene, 0 < X.1.1 h → h ≠ g → gtail.rank ≤ h.rank := by
      intro h hh hne_hg
      exact hgtail_min h (htail_pos_of_X_ne_g h hh hne_hg)
    have htailAfterG_support_ge :
        ∀ h ∈ tailAfterG.support, 2 * qtail + 3 ≤ h.rank := by
      intro h hh
      have hpos : 0 < tailAfterG h :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      have hle := hgtail_min h hpos
      rwa [hgtail_rank_q] at hle
    have hprimeX_eq_tailAfterG :
        ∀ i, 1 ≤ i → Chromosome.prime^[i] X.1.1 =
          Chromosome.prime^[i] tailAfterG := by
      intro i hi
      ext z
      have hcoeffX := prime_iterate_coeff i X.1.1 z
      have hcoeffTail := prime_iterate_coeff i tailAfterG z
      change (Chromosome.prime^[i] X.1.1) z =
        X.1.1 ⟨z.rank + i, z.type, Nat.le_add_right_of_le z.rank_pos⟩ at hcoeffX
      change (Chromosome.prime^[i] tailAfterG) z =
        tailAfterG ⟨z.rank + i, z.type, Nat.le_add_right_of_le z.rank_pos⟩ at hcoeffTail
      rw [hcoeffX, hcoeffTail, htailAfterG_def, Finsupp.tsub_apply,
        Finsupp.single_apply]
      have hne :
          g ≠ (⟨z.rank + i, z.type, Nat.le_add_right_of_le z.rank_pos⟩ : Gene) := by
        intro h
        have hrank := congrArg Gene.rank h
        dsimp at hrank
        rw [hg_rank_one] at hrank
        have hzpos : 0 < z.rank := z.rank_pos
        omega
      rw [if_neg hne]
      omega
    have htail_sigma_eq :
        ∀ i, 1 ≤ i → Sigma.sigma X.1.1 i = Sigma.sigma tailAfterG i := by
      intro i hi
      simp [Sigma.sigma, hprimeX_eq_tailAfterG i hi]
    have hne_gtail_neg_g : gtail ≠ -g := by
      intro h
      have hrank : gtail.rank = g.rank := by rw [h, Gene.neg_rank]
      rw [hg_rank_one] at hrank
      omega
    have hrestAfterTriple_gtail :
        restAfterTriple gtail = X.1.1 gtail := by
      rw [hrestAfterTriple_eq]
      simp [Finsupp.tsub_apply, hne_gtail_g.symm]
    have hrestAfterTriple_gtail_pos : 0 < restAfterTriple gtail := by
      rw [hrestAfterTriple_gtail]
      exact hXgtail
    have hopposite_type16_setup :
        gtail.type = -g.type →
          ∃ restAfterType16 : Chromosome,
            restAfterType16 =
                X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
                  Finsupp.single gtail 1 ∧
            (X16 (Nat.zero_le (qtail + 1)) hg_pol).1 + restAfterType16 =
                X.1.1 ∧
            ((Y16 (Nat.zero_le (qtail + 1)) hg_pol).1 + restAfterType16 ≤
                Y.1.1 →
              ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1) := by
      intro hopp
      let restAfterType16 : Chromosome :=
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
          Finsupp.single gtail 1
      have hrestAfterType16_eq :
          restAfterType16 =
              X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
                Finsupp.single gtail 1 := rfl
      have hcandidate :=
        htype16_boundary (q := qtail + 1) gtail hopp
          (by rw [hgtail_rank_q]; omega) (by omega : 1 ≤ X.1.1 gtail)
      have hg_eq :
          Gene.ofRank 1 g.type = (Finsupp.single g 1 : Chromosome) := by
        have h := Gene.ofRank_eq_gene (g := g)
        rwa [hg_rank_one] at h
      have hgtail_eq :
          Gene.ofRank (2 * (qtail + 1) + 1) (-g.type) =
            (Finsupp.single gtail 1 : Chromosome) := by
        have h := Gene.ofRank_eq_gene (g := gtail)
        rw [hopp, hgtail_rank_q] at h
        convert h using 2
        omega
      have hX16val :
          (X16 (Nat.zero_le (qtail + 1)) hg_pol).1 =
            Finsupp.single g 1 + Finsupp.single g 1 +
              Finsupp.single gtail 1 := by
        rw [X16_eq, hg_eq, hgtail_eq]
      have hXeq_type16 :
          (X16 (Nat.zero_le (qtail + 1)) hg_pol).1 + restAfterType16 =
            X.1.1 := by
        rw [hX16val]
        dsimp [restAfterType16]
        exact Mix2LambdaSection17.double_single_pair_add_rest
          hg_two (by omega : 1 ≤ X.1.1 gtail) hne_gtail_g.symm
      exact ⟨restAfterType16, hrestAfterType16_eq, hXeq_type16, fun hZle =>
        hcandidate (by simpa [hrestAfterType16_eq] using hZle)⟩
    have hsame_sign_setup :
        ¬ gtail.type = -g.type →
          gtail.type = g.type ∧ X.1.1 (-gtail) = 0 ∧ -gtail ≠ g ∧
            tailAfterG (-gtail) = 0 := by
      intro hnot_opp
      have hsame_type : gtail.type = g.type :=
        polarized_same_type_of_not_neg hg_pol hgtail_pol hnot_opp
      have hXneg_gtail_zero : X.1.1 (-gtail) = 0 :=
        no_pair_neg_gene_zero hno_pair hgtail_pol hXgtail
      have hneg_gtail_ne_g : -gtail ≠ g := by
        intro h
        have hrank : gtail.rank = g.rank := by
          rw [← Gene.neg_rank gtail, h]
        rw [hg_rank_one] at hrank
        omega
      have htail_neg_gtail_zero : tailAfterG (-gtail) = 0 := by
        rw [htailAfterG_def, Finsupp.tsub_apply, Finsupp.single_apply,
          if_neg (fun h => hneg_gtail_ne_g h.symm), hXneg_gtail_zero]
        rfl
      exact ⟨hsame_type, hXneg_gtail_zero, hneg_gtail_ne_g, htail_neg_gtail_zero⟩
    have hopposite_multiplicity_split :
        gtail.type = -g.type →
          (X.1.1 gtail = 1 ∧
            ∃ restAfterType16 : Chromosome,
              restAfterType16 =
                  X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
                    Finsupp.single gtail 1 ∧
              (X16 (Nat.zero_le (qtail + 1)) hg_pol).1 + restAfterType16 =
                  X.1.1 ∧
              ((Y16 (Nat.zero_le (qtail + 1)) hg_pol).1 + restAfterType16 ≤
                  Y.1.1 →
                ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)) ∨
          (2 ≤ X.1.1 gtail ∧
            ∃ restAfterType14 : Chromosome,
              restAfterType14 =
                  X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
                    Finsupp.single gtail 1 - Finsupp.single gtail 1 ∧
              (X14 (Nat.zero_le (qtail + 1)) hg_pol).1 + restAfterType14 =
                  X.1.1 ∧
              ((Y14 (Nat.zero_le (qtail + 1)) hg_pol).1 + restAfterType14 ≤
                  Y.1.1 →
                ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)) := by
      intro hopp
      by_cases htwo : 2 ≤ X.1.1 gtail
      · right
        let restAfterType14 : Chromosome :=
          X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
            Finsupp.single gtail 1 - Finsupp.single gtail 1
        have hrestAfterType14_eq :
            restAfterType14 =
                X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
                  Finsupp.single gtail 1 - Finsupp.single gtail 1 := rfl
        have hcandidate :=
          htype14_boundary (q := qtail + 1) gtail hopp
            (by rw [hgtail_rank_q]; omega) htwo
        have hg_eq :
            Gene.ofRank 1 g.type = (Finsupp.single g 1 : Chromosome) := by
          have h := Gene.ofRank_eq_gene (g := g)
          rwa [hg_rank_one] at h
        have hgtail_eq :
            Gene.ofRank (2 * (qtail + 1) + 1) (-g.type) =
              (Finsupp.single gtail 1 : Chromosome) := by
          have h := Gene.ofRank_eq_gene (g := gtail)
          rw [hopp, hgtail_rank_q] at h
          convert h using 2
          omega
        have hX14val :
            (X14 (Nat.zero_le (qtail + 1)) hg_pol).1 =
              Finsupp.single g 1 + Finsupp.single g 1 +
                Finsupp.single gtail 1 + Finsupp.single gtail 1 := by
          rw [X14_eq, hg_eq, hgtail_eq]
        have hXeq_type14 :
            (X14 (Nat.zero_le (qtail + 1)) hg_pol).1 + restAfterType14 =
              X.1.1 := by
          rw [hX14val]
          dsimp [restAfterType14]
          exact Mix2LambdaSection17.double_pair_add_rest
            hg_two htwo hne_gtail_g.symm
        exact ⟨htwo, restAfterType14, hrestAfterType14_eq, hXeq_type14,
          fun hZle => hcandidate (by simpa [hrestAfterType14_eq] using hZle)⟩
      · left
        have hone : X.1.1 gtail = 1 := by omega
        obtain ⟨restAfterType16, hrestAfterType16_eq, hXeq_type16,
          hcandidate⟩ := hopposite_type16_setup hopp
        exact ⟨hone, restAfterType16, hrestAfterType16_eq, hXeq_type16,
          hcandidate⟩
    have hgap_odd_non_top :
        ∀ j, 1 ≤ j → j < 2 * qtail + 3 → ¬ Even j → j ≠ 1 →
          ((1 : ℚ), (1 : ℚ)) +
              signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1) := by
      intro j hjlo hjlt hjodd _hj1
      exact type10_mid_gap_odd_of_Y_ne X Y h17_1 hjodd (by omega)
        (same_gene_prime_iterate_Y_ne_of_X_gene_above X Y hXY gtail hXgtail (by
          rw [hgtail_rank_q]
          omega))
    have hgap_odd_top :
        ((1 : ℚ), (1 : ℚ)) +
            signature (Chromosome.prime^[2 * qtail + 3] X.1.1) ≤
          signature (Chromosome.prime^[2 * qtail + 3] Y.1.1) := by
      refine type10_mid_gap_odd_of_Y_ne X Y h17_1
        (Nat.not_even_iff_odd.mpr ⟨qtail + 1, by ring⟩) (by omega) ?_
      intro hYzero
      have hYrank : ∀ h : Gene, 0 < Y.1.1 h → h.rank ≤ 2 * qtail + 3 := by
        intro h hh
        have hall :=
          (Chromosome.prime_iterate_eq_zero_rank_le
            (X := Y.1.1) (k := 2 * qtail + 3)).2 hYzero
        exact hall h (Finsupp.mem_support_iff.mpr (ne_of_gt hh))
      have hYpol_top : ∀ h : Gene, 0 < Y.1.1 h → h.rank = 2 * qtail + 3 →
          h.type ≠ GeneType.NonPolarized := by
        intro h hh hhrank
        have hhodd : Odd h.rank := by
          rw [hhrank]
          exact ⟨qtail + 1, by ring⟩
        have hodd_part : 0 < Y.1.1.oddPart h := by
          rw [oddPart_eq, Finsupp.filter_apply, if_pos hhodd]
          exact hh
        exact IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2.2) h
          (Finsupp.mem_support_iff.mpr hodd_part.ne')
      cases htype : gtail.type with
      | NonPolarized => exact hgtail_pol htype
      | Positive =>
          have hno_pos :
              Y.1.1 ⟨2 * qtail + 3, GeneType.Positive, by omega⟩ = 0 := by
            have htop_eq_g :
                (⟨2 * qtail + 3, GeneType.Positive, by omega⟩ : Gene) = gtail :=
              Gene.ext (by dsimp; rw [hgtail_rank_q]) htype.symm
            have hle := hcommon gtail hXgtail
            rw [htop_eq_g]
            omega
          have hYfst0 :=
            signature_prime_iterate_even_fst_eq_zero_of_rank_le_no_positive_top
              (W := Y.1.1) (p := qtail + 1) hYpol_top hYrank hno_pos
          have hYfst0' :
              (signature (Chromosome.prime^[2 * qtail + 2] Y.1.1)).1 = 0 := by
            simpa [show 2 * (qtail + 1) = 2 * qtail + 2 by omega] using hYfst0
          have hXfst1 :=
            one_le_signature_prime_pred_fst_of_positive (X := X.1.1)
              (gpos := gtail) htype hXgtail
          have hXfst1' :
              1 ≤ (signature (Chromosome.prime^[2 * qtail + 2] X.1.1)).1 := by
            simpa [hgtail_rank_q, show 2 * qtail + 3 - 1 = 2 * qtail + 2 by omega]
              using hXfst1
          have hdom := (le_iff_dominates.mp hXY.le (2 * qtail + 2)).1
          linarith
      | Negative =>
          have hno_neg :
              Y.1.1 ⟨2 * qtail + 3, GeneType.Negative, by omega⟩ = 0 := by
            have htop_eq_g :
                (⟨2 * qtail + 3, GeneType.Negative, by omega⟩ : Gene) = gtail :=
              Gene.ext (by dsimp; rw [hgtail_rank_q]) htype.symm
            have hle := hcommon gtail hXgtail
            rw [htop_eq_g]
            omega
          have hYsnd0 :=
            signature_prime_iterate_even_snd_eq_zero_of_rank_le_no_negative_top
              (W := Y.1.1) (p := qtail + 1) hYpol_top hYrank hno_neg
          have hYsnd0' :
              (signature (Chromosome.prime^[2 * qtail + 2] Y.1.1)).2 = 0 := by
            simpa [show 2 * (qtail + 1) = 2 * qtail + 2 by omega] using hYsnd0
          have hXsnd1 :=
            one_le_signature_prime_pred_snd_of_negative (X := X.1.1)
              (gneg := gtail) htype hXgtail
          have hXsnd1' :
              1 ≤ (signature (Chromosome.prime^[2 * qtail + 2] X.1.1)).2 := by
            simpa [hgtail_rank_q, show 2 * qtail + 3 - 1 = 2 * qtail + 2 by omega]
              using hXsnd1
          have hdom := (le_iff_dominates.mp hXY.le (2 * qtail + 2)).2
          linarith
    have hgap_odd_tail :
        ∀ j, 1 ≤ j → j ≤ 2 * qtail + 3 → ¬ Even j →
          ((1 : ℚ), (1 : ℚ)) +
              signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1) := by
      intro j hjlo hjhi hjodd
      by_cases hj1 : j = 1
      · subst j
        simpa using hgap1
      · by_cases hjtop : j = 2 * qtail + 3
        · subst j
          exact hgap_odd_top
        · exact hgap_odd_non_top j hjlo (by omega) hjodd hj1
    -- Even-layer `+2` gap on the `g`-component, anchored on `tailAfterG`
    -- (`X ⊇ (X g) · g(1)` with `X g ≥ 3`, the paper's Case 3).  This is the
    -- documented §17 frontier: the two-step window shrinks the gap by
    -- `X g - 1 ≥ 2` per step (X even two-step drop `= D - X g`, but the Y drop
    -- is only bounded by `D - 1`), so it must be proved via the paper's
    -- single-step monotone-growth chain (`c_i - a_i` strictly increasing),
    -- for which no `onestep`-style helper yet exists in the tree.  Both the
    -- Type16 and Type14 opposite-sign candidates consume this same gap.
    have hgap_even_tail :
        ∀ j, 1 ≤ j → j ≤ 2 * qtail + 3 → Even j →
          (signature (Gene.ofRank 1 g.type) +
                signature (Gene.ofRank 1 g.type)) +
              signature (Chromosome.prime^[j] X.1.1) ≤
            signature (Chromosome.prime^[j] Y.1.1) := by
      intro j hjlo hjhi hjeven
      have hj2 : 2 ≤ j := by rcases hjeven with ⟨t, rfl⟩; omega
      have hXPi : X.1.1 ∈ Variety.Pi := Variety.mem_Pi_iff.mpr hXpol
      -- level-0 signature agreement (equal ranks `m + 2`)
      have hb0d0 : (Sigma.sigma X.1.1 0).2 = (Sigma.sigma Y.1.1 0).2 := by
        have hx : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = ((m : ℚ) + 2) := by
          simpa [Sigma.sigma, X.2] using
            @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
        have hy : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = ((m : ℚ) + 2) := by
          simpa [Sigma.sigma, Y.2] using
            @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
        have h0 := le_iff_dominates.mp hXY.le 0
        have h01 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 := by
          simpa [Sigma.sigma] using h0.1
        have h02 : (Sigma.sigma X.1.1 0).2 ≤ (Sigma.sigma Y.1.1 0).2 := by
          simpa [Sigma.sigma] using h0.2
        linarith
      have ha0c0 : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 := by
        have hx : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = ((m : ℚ) + 2) := by
          simpa [Sigma.sigma, X.2] using
            @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
        have hy : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = ((m : ℚ) + 2) := by
          simpa [Sigma.sigma, Y.2] using
            @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
        have h0 := le_iff_dominates.mp hXY.le 0
        have h01 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 := by
          simpa [Sigma.sigma] using h0.1
        have h02 : (Sigma.sigma X.1.1 0).2 ≤ (Sigma.sigma Y.1.1 0).2 := by
          simpa [Sigma.sigma] using h0.2
        linarith
      -- odd-neighbour gap at level `j - 1`
      have hodd_gap := hgap_odd_tail (j - 1) (by omega) (by omega)
        (by
          rw [Nat.not_even_iff_odd]
          rcases hjeven with ⟨t, rfl⟩
          exact ⟨t - 1, by omega⟩)
      -- below rank `j`, `g` (rank one) is the only surviving gene of `X`
      have hlowrank : ∀ h : Gene, 0 < X.1.1 h → h ≠ g → j - 1 < h.rank := by
        intro h hh hne
        have hle := hgtail_min_X_ne_g h hh hne
        rw [hgtail_rank_q] at hle
        omega
      cases hgt : g.type with
      | NonPolarized => exact absurd hgt hg_pol
      | Positive =>
          -- X-side single-step telescoping: `b₀ - b_{j-1} = a₁ - a_j`
          have hX1 : (Sigma.sigma X.1.1 0).2 - (Sigma.sigma X.1.1 (j - 1)).2 =
              (Sigma.sigma X.1.1 1).1 - (Sigma.sigma X.1.1 j).1 := by
            have h := Sigma.b0_bi_eq_a1_ai1 X.1.1 hXPi (j - 1) (by
              intro h hh hrank
              by_cases hhg : h = g
              · rw [hhg]; exact hgt
              · exact absurd hrank (by
                  have := hlowrank h
                    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)) hhg
                  omega))
            rw [show j - 1 + 1 = j from by omega] at h
            simpa [Sigma.sigma] using h
          have hY1 := mix_a1_ai_le_b0_bi_1 Y.1.2 (i := j) (by omega)
          have hodd_snd := snd_add_one_le_of_one_one_add_le hodd_gap
          have hc1a1 := fst_add_one_le_of_one_one_add_le hgap1
          simp only [Sigma.sigma] at hX1 hY1 hodd_snd hc1a1
          have hgoal : (signature (Chromosome.prime^[j] X.1.1)).1 + 2 ≤
              (signature (Chromosome.prime^[j] Y.1.1)).1 := by
            simp only [Sigma.sigma] at hb0d0 ha0c0
            linarith
          have hdom := (le_iff_dominates.mp hXY.le j).2
          refine ⟨?_, ?_⟩
          · simp only [signature_ofRank_one_positive, Prod.fst_add, Prod.mk_add_mk]
            linarith
          · simp only [signature_ofRank_one_positive, Prod.snd_add, Prod.mk_add_mk,
              add_zero]
            simpa [Sigma.sigma] using hdom
      | Negative =>
          have hX1 : (Sigma.sigma X.1.1 0).1 - (Sigma.sigma X.1.1 (j - 1)).1 =
              (Sigma.sigma X.1.1 1).2 - (Sigma.sigma X.1.1 j).2 := by
            have h := sg_a0_ai_eq_b1_bi1 hXPi (j - 1) (by
              intro h hh hrank
              by_cases hhg : h = g
              · rw [hhg]; exact hgt
              · exact absurd hrank (by
                  have := hlowrank h
                    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)) hhg
                  omega))
            rw [show j - 1 + 1 = j from by omega] at h
            simpa [Sigma.sigma] using h
          have hY1 := mix_b1_bi_le_a0_ai_1 Y.1.2 (i := j) (by omega)
          have hodd_fst := fst_add_one_le_of_one_one_add_le hodd_gap
          have hc1a1 := snd_add_one_le_of_one_one_add_le hgap1
          simp only [Sigma.sigma] at hX1 hY1 hodd_fst hc1a1
          have hgoal : (signature (Chromosome.prime^[j] X.1.1)).2 + 2 ≤
              (signature (Chromosome.prime^[j] Y.1.1)).2 := by
            simp only [Sigma.sigma] at hb0d0 ha0c0
            linarith
          have hdom := (le_iff_dominates.mp hXY.le j).1
          refine ⟨?_, ?_⟩
          · simp only [signature_ofRank_one_negative, Prod.fst_add, Prod.mk_add_mk,
              add_zero]
            simpa [Sigma.sigma] using hdom
          · simp only [signature_ofRank_one_negative, Prod.snd_add, Prod.mk_add_mk]
            linarith
    -- Below the successor level `2 * qtail + 4` the only surviving `X` genes are
    -- the rank-one `g` (all `X g ≥ 3` copies) and the minimal tail gene `gtail`
    -- (rank `2 * qtail + 3`).  The naive two-step edge-drop leaves cushion
    -- `3 - X g ≤ 0`, so this uses the paper's single-step telescoping (as in
    -- `hgap_even_tail`) with an off-by-one correction for the single opposite-sign
    -- `gtail`.  It is only needed for the Type16 candidate (`X gtail = 1`); the
    -- Type14 candidate consumes only the pred-level even gap.
    have hXPi : X.1.1 ∈ Variety.Pi := Variety.mem_Pi_iff.mpr hXpol
    -- level-0 signature agreement (equal ranks `m + 2`)
    have hb0d0 : (Sigma.sigma X.1.1 0).2 = (Sigma.sigma Y.1.1 0).2 := by
      have hx : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = ((m : ℚ) + 2) := by
        simpa [Sigma.sigma, X.2] using
          @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      have hy : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = ((m : ℚ) + 2) := by
        simpa [Sigma.sigma, Y.2] using
          @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      have h0 := le_iff_dominates.mp hXY.le 0
      have h01 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 := by
        simpa [Sigma.sigma] using h0.1
      have h02 : (Sigma.sigma X.1.1 0).2 ≤ (Sigma.sigma Y.1.1 0).2 := by
        simpa [Sigma.sigma] using h0.2
      linarith
    have ha0c0 : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 := by
      have hx : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = ((m : ℚ) + 2) := by
        simpa [Sigma.sigma, X.2] using
          @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
      have hy : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = ((m : ℚ) + 2) := by
        simpa [Sigma.sigma, Y.2] using
          @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
      have h0 := le_iff_dominates.mp hXY.le 0
      have h01 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 := by
        simpa [Sigma.sigma] using h0.1
      have h02 : (Sigma.sigma X.1.1 0).2 ≤ (Sigma.sigma Y.1.1 0).2 := by
        simpa [Sigma.sigma] using h0.2
      linarith
    -- odd-neighbour gap at `2 * qtail + 3` (available from the odd family)
    have hodd_gap := hgap_odd_tail (2 * qtail + 3) (by omega) (by omega)
      (Nat.not_even_iff_odd.mpr ⟨qtail + 1, by ring⟩)
    -- successor gap, assuming the opposite-sign `gtail` has multiplicity one
    have hgap_succ_of_one : X.1.1 gtail = 1 → gtail.type = -g.type →
        signature (Gene.ofRank 1 g.type) +
            signature (Chromosome.prime^[2 * qtail + 4] X.1.1) ≤
          signature (Chromosome.prime^[2 * qtail + 4] Y.1.1) := by
      intro hone hopp
      have hsucc_rank : 2 * qtail + 4 = (2 * qtail + 3) + 1 := by omega
      cases hgt : g.type with
      | NonPolarized => exact absurd hgt hg_pol
      | Positive =>
          have hgtail_neg : gtail.type = GeneType.Negative := by
            rw [hopp, hgt]; rfl
          -- below rank `2*qtail+4`, only `g` (positive) and `gtail` (negative) survive
          have hlow_pos : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * qtail + 3 →
              h ≠ gtail → h.type = GeneType.Positive := by
            intro h hh hrank hne
            have hhpos : 0 < X.1.1 h := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
            by_cases hhg : h = g
            · rw [hhg]; exact hgt
            · have hle := hgtail_min_X_ne_g h hhpos hhg
              rw [hgtail_rank_q] at hle
              have hheq : h.rank = 2 * qtail + 3 := by omega
              cases hht : h.type with
              | NonPolarized =>
                  exact absurd hht (IsPolarized_def'.mp hXpol h hh)
              | Positive => rfl
              | Negative =>
                  exact absurd (Gene.ext (by rw [hheq, hgtail_rank_q])
                    (by rw [hht, hgtail_neg])) hne
          -- off-by-one telescoping: `b_X 0 - b_X(2qtail+3) = a_X 1 - a_X(2qtail+4) + 1`
          have hX1 := sg_b0_bi_off_by_one hXPi (i := 2 * qtail + 3) hone hgtail_neg
            (by rw [hgtail_rank_q]) hlow_pos
          have hY1 := mix_a1_ai_le_b0_bi_1 Y.1.2 (i := 2 * qtail + 4) (by omega)
          have hodd_snd := snd_add_one_le_of_one_one_add_le hodd_gap
          have hc1a1 := fst_add_one_le_of_one_one_add_le hgap1
          rw [← hsucc_rank] at hX1
          simp only [Sigma.sigma, show 2 * qtail + 4 - 1 = 2 * qtail + 3 by omega]
            at hX1 hY1 hodd_snd hc1a1
          have hstrict : (signature (Chromosome.prime^[2 * qtail + 4] X.1.1)).1 <
              (signature (Chromosome.prime^[2 * qtail + 4] Y.1.1)).1 := by
            simp only [Sigma.sigma] at hb0d0 ha0c0 ⊢
            linarith
          simpa [hgt, show 2 * (qtail + 1) + 2 = 2 * qtail + 4 by omega] using
            type16_succ_gap_positive X Y hXY (p := qtail + 1)
              (by simpa [show 2 * (qtail + 1) + 2 = 2 * qtail + 4 by omega] using hstrict)
      | Negative =>
          have hgtail_pos : gtail.type = GeneType.Positive := by
            rw [hopp, hgt]; rfl
          have hlow_neg : ∀ h ∈ X.1.1.support, h.rank ≤ 2 * qtail + 3 →
              h ≠ gtail → h.type = GeneType.Negative := by
            intro h hh hrank hne
            have hhpos : 0 < X.1.1 h := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
            by_cases hhg : h = g
            · rw [hhg]; exact hgt
            · have hle := hgtail_min_X_ne_g h hhpos hhg
              rw [hgtail_rank_q] at hle
              have hheq : h.rank = 2 * qtail + 3 := by omega
              cases hht : h.type with
              | NonPolarized =>
                  exact absurd hht (IsPolarized_def'.mp hXpol h hh)
              | Negative => rfl
              | Positive =>
                  exact absurd (Gene.ext (by rw [hheq, hgtail_rank_q])
                    (by rw [hht, hgtail_pos])) hne
          have hX1 := sg_a0_ai_off_by_one hXPi (i := 2 * qtail + 3) hone hgtail_pos
            (by rw [hgtail_rank_q]) hlow_neg
          have hY1 := mix_b1_bi_le_a0_ai_1 Y.1.2 (i := 2 * qtail + 4) (by omega)
          have hodd_fst := fst_add_one_le_of_one_one_add_le hodd_gap
          have hc1a1 := snd_add_one_le_of_one_one_add_le hgap1
          rw [← hsucc_rank] at hX1
          simp only [Sigma.sigma, show 2 * qtail + 4 - 1 = 2 * qtail + 3 by omega]
            at hX1 hY1 hodd_fst hc1a1
          have hstrict : (signature (Chromosome.prime^[2 * qtail + 4] X.1.1)).2 <
              (signature (Chromosome.prime^[2 * qtail + 4] Y.1.1)).2 := by
            simp only [Sigma.sigma] at hb0d0 ha0c0 ⊢
            linarith
          simpa [hgt, show 2 * (qtail + 1) + 2 = 2 * qtail + 4 by omega] using
            type16_succ_gap_negative X Y hXY (p := qtail + 1)
              (by simpa [show 2 * (qtail + 1) + 2 = 2 * qtail + 4 by omega] using hstrict)
    by_cases hopp : gtail.type = -g.type
    · -- Opposite-sign tail gene: dispatch on its multiplicity into the
      -- Type16 (`2g(1)+gtail`) or Type14 (`2g(1)+2gtail`) boundary candidate.
      rcases hopposite_multiplicity_split hopp with
        ⟨hone, restAfterType16, _hrest16_eq, hX16eq, hcont16⟩ |
        ⟨_htwo, restAfterType14, _hrest14_eq, hX14eq, hcont14⟩
      · refine hcont16 ?_
        exact type16_rank_one_target_add_rest_le_of_gaps hg_pol X Y hXY
          restAfterType16 hX16eq hgap_odd_tail hgap_even_tail
          (hgap_succ_of_one hone hopp)
      · refine hcont14 ?_
        exact type14_rank_one_target_add_rest_le_of_gaps hg_pol X Y hXY
          restAfterType14 hX14eq hgap_odd_tail hgap_even_tail
    · -- Same-sign tail gene (`gtail.type = g.type`).  Split on opposite-sign mass:
      -- if `X` carries no negative charge it is all-positive and the configuration
      -- is vacuous (mirror of the SameSign all-positive branch); otherwise `X`
      -- has a negative gene and needs the §17 Case 3 negative-partner move.
      by_cases hb0a1 : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma X.1.1 0).2
      · -- Opposite-sign mass present: dispatch on the minimal opposite-sign gene
        -- (Type16/Type14 boundary anchored at its rank), via the shared engine.
        exact exists_step_neg_partner_dispatch hg_pol X Y hXY hcommon h17_1 hXpol
          hno_pair g hg_rank_one rfl hg_two hgmin hseed1
      · -- No opposite-sign mass ⟹ `X` all-positive ⟹ vacuous:
        -- `b₁ = a₁ ≥ b₀ = d₀ ≥ d₁ > b₁`  (last strict step is `hseed1.2`).
        exfalso
        have hB0A1 : (signature X.1.1).2 ≤
            (signature (Chromosome.prime^[1] X.1.1)).1 := not_lt.mp hb0a1
        have hB0D0 : (signature X.1.1).2 = (signature Y.1.1).2 := hb0d0
        have hD1D0 : (signature (Chromosome.prime^[1] Y.1.1)).2 ≤
            (signature Y.1.1).2 := ((signature_prime_le Y.1.1).trans inf_le_left).2
        linarith [hseed1.2, hXsig1_eq, hB0A1, hB0D0, hD1D0]

lemma rank_one_double_same_gene_tail_frontier
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_two : 2 ≤ X.1.1 g)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hXsig1_eq :
      (signature (Chromosome.prime^[1] X.1.1)).1 =
        (signature (Chromosome.prime^[1] X.1.1)).2)
    (hYsig1_eq :
      (signature (Chromosome.prime^[1] Y.1.1)).1 =
        (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hgap1 :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[1] X.1.1) ≤
        signature (Chromosome.prime^[1] Y.1.1))
    (restAfterDouble restAfterTriple tailAfterG : Chromosome)
    (hrestAfterDouble_eq :
      restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (hrestAfterDouble_ne : restAfterDouble ≠ 0)
    (hrestAfterDouble_mem : restAfterDouble ∈ Mix (2 • Lambda, Pi))
    (hprimeX_eq_restAfterDouble :
      Chromosome.prime^[1] X.1.1 =
        Chromosome.prime^[1] restAfterDouble)
    (hrestAfterDouble_total :
      restAfterDouble.sum (fun _ n => n) + 2 = X.1.1.sum (fun _ n => n))
    (hg₂_rest : 0 < restAfterDouble g₂)
    (hg₂min : ∀ g' : Gene, 0 < restAfterDouble g' → g₂.rank ≤ g'.rank)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_odd : Odd g₂.rank)
    (hX_rank_ge_three_of_ne_g :
      ∀ h : Gene, 0 < X.1.1 h → h ≠ g → 3 ≤ h.rank)
    (hg₂min_X_ne_g :
      ∀ h : Gene, 0 < X.1.1 h → h ≠ g → g₂.rank ≤ h.rank)
    (hg₂_same_extra : g₂ = g → 3 ≤ X.1.1 g)
    (hg₂_rank_ge_three_of_ne_g : g₂ ≠ g → 3 ≤ g₂.rank)
    (htype16_boundary :
      ∀ {q : ℕ} (gsingle : Gene),
        gsingle.type = -g.type →
        gsingle.rank = 2 * q + 1 →
        1 ≤ X.1.1 gsingle →
        (Y16 (Nat.zero_le q) hg_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
              Finsupp.single gsingle 1) ≤ Y.1.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (htype14_boundary :
      ∀ {q : ℕ} (gopp : Gene),
        gopp.type = -g.type →
        gopp.rank = 2 * q + 1 →
        2 ≤ X.1.1 gopp →
        (Y14 (Nat.zero_le q) hg_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
              Finsupp.single gopp 1 - Finsupp.single gopp 1) ≤ Y.1.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (hsame : g₂ = g)
    (hg_extra : 3 ≤ X.1.1 g)
    (hrestAfterTriple_eq :
      restAfterTriple =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
          Finsupp.single g 1)
    (hprimeX_eq_restAfterTriple :
      Chromosome.prime^[1] X.1.1 =
        Chromosome.prime^[1] restAfterTriple)
    (hrestAfterTriple_total :
      restAfterTriple.sum (fun _ n => n) + 3 = X.1.1.sum (fun _ n => n))
    (htailAfterG_def : tailAfterG = X.1.1 - Finsupp.single g (X.1.1 g))
    (htailAfterG_g_zero : tailAfterG g = 0)
    (htailAfterG_pos_X_ne :
      ∀ h : Gene, 0 < tailAfterG h → 0 < X.1.1 h ∧ h ≠ g)
    (htailAfterG_rank_ge_three :
      ∀ h : Gene, 0 < tailAfterG h → 3 ≤ h.rank)
    (htailAfterG_zero_or_min :
      tailAfterG = 0 ∨
        ∃ gtail : Gene, 0 < tailAfterG gtail ∧
          (∀ h : Gene, 0 < tailAfterG h → gtail.rank ≤ h.rank) ∧
          3 ≤ gtail.rank) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hcases :=
    rank_one_double_same_gene_tail_cases X Y hXY hcommon h17_1 hXpol hno_pair
      g g₂ hgX hgmin hg_pol hp hp0 hg_rank_one hXneg_zero hg_two hseed1
      hXsig1_eq hYsig1_eq hgap1 restAfterDouble restAfterTriple tailAfterG
      hrestAfterDouble_eq hrestAfterDouble_ne hrestAfterDouble_mem
      hprimeX_eq_restAfterDouble hrestAfterDouble_total hg₂_rest hg₂min hXg₂
      hg₂_pol hg₂_odd hX_rank_ge_three_of_ne_g hg₂min_X_ne_g
      hg₂_same_extra hg₂_rank_ge_three_of_ne_g htype16_boundary
      htype14_boundary hsame hg_extra hrestAfterTriple_eq
      hprimeX_eq_restAfterTriple hrestAfterTriple_total htailAfterG_def
      htailAfterG_g_zero htailAfterG_pos_X_ne htailAfterG_rank_ge_three
  rcases htailAfterG_zero_or_min with htail_zero | htail_min
  · exact hcases.1 htail_zero
  · rcases htail_min with ⟨gtail, hgtail, hgtail_min, hgtail_rank⟩
    exact hcases.2 gtail hgtail hgtail_min hgtail_rank

/-- The same-gene extra-multiplicity frontier in the rank-one-double no-pair
branch.

Here the residue-minimal gene after removing two copies of the rank-one source
is again the rank-one gene itself, so `X` has at least three copies of that
minimal gene.  The large dispatcher reduces to this focused frontier before
continuing with the Type14/Type16 alternatives. -/
lemma rank_one_double_same_gene_extra
    {m p : ℕ} (X Y : nMix2LambdaPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∀ g : Gene, 0 < X.1.1 g → Y.1.1 g ≤ 0)
    (h17_1 : ∀ k, 0 < k → Chromosome.prime^[k] Y.1.1 ≠ 0 →
      (Chromosome.prime^[k] X.1.1).rank <
        (Chromosome.prime^[k] Y.1.1).rank)
    (hXpol : X.1.1.IsPolarized)
    (hno_pair : ¬ ∃ (gpos gneg : Gene),
      gpos.rank = gneg.rank ∧
      gpos.type = .Positive ∧ gneg.type = .Negative ∧
      0 < X.1.1 gpos ∧ 0 < X.1.1 gneg)
    (g g₂ : Gene)
    (hgX : 0 < X.1.1 g)
    (hgmin : ∀ g' : Gene, 0 < X.1.1 g' → g.rank ≤ g'.rank)
    (hg_pol : g.type ≠ .NonPolarized)
    (hp : g.rank = 2 * p + 1) (hp0 : p = 0)
    (hg_rank_one : g.rank = 1)
    (hXneg_zero : X.1.1 (-g) = 0)
    (hg_two : 2 ≤ X.1.1 g)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hXsig1_eq :
      (signature (Chromosome.prime^[1] X.1.1)).1 =
        (signature (Chromosome.prime^[1] X.1.1)).2)
    (hYsig1_eq :
      (signature (Chromosome.prime^[1] Y.1.1)).1 =
        (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hgap1 :
      ((1 : ℚ), (1 : ℚ)) + signature (Chromosome.prime^[1] X.1.1) ≤
        signature (Chromosome.prime^[1] Y.1.1))
    (restAfterDouble : Chromosome)
    (hrestAfterDouble_eq :
      restAfterDouble =
        X.1.1 - Finsupp.single g 1 - Finsupp.single g 1)
    (hrestAfterDouble_ne : restAfterDouble ≠ 0)
    (hrestAfterDouble_mem : restAfterDouble ∈ Mix (2 • Lambda, Pi))
    (hprimeX_eq_restAfterDouble :
      Chromosome.prime^[1] X.1.1 =
        Chromosome.prime^[1] restAfterDouble)
    (hrestAfterDouble_total :
      restAfterDouble.sum (fun _ n => n) + 2 = X.1.1.sum (fun _ n => n))
    (hg₂_rest : 0 < restAfterDouble g₂)
    (hg₂min : ∀ g' : Gene, 0 < restAfterDouble g' → g₂.rank ≤ g'.rank)
    (hXg₂ : 0 < X.1.1 g₂)
    (hg₂_pol : g₂.type ≠ GeneType.NonPolarized)
    (hg₂_odd : Odd g₂.rank)
    (hX_rank_ge_three_of_ne_g :
      ∀ h : Gene, 0 < X.1.1 h → h ≠ g → 3 ≤ h.rank)
    (hg₂min_X_ne_g :
      ∀ h : Gene, 0 < X.1.1 h → h ≠ g → g₂.rank ≤ h.rank)
    (hg₂_same_extra : g₂ = g → 3 ≤ X.1.1 g)
    (hg₂_rank_ge_three_of_ne_g : g₂ ≠ g → 3 ≤ g₂.rank)
    (htype16_boundary :
      ∀ {q : ℕ} (gsingle : Gene),
        gsingle.type = -g.type →
        gsingle.rank = 2 * q + 1 →
        1 ≤ X.1.1 gsingle →
        (Y16 (Nat.zero_le q) hg_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
              Finsupp.single gsingle 1) ≤ Y.1.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (htype14_boundary :
      ∀ {q : ℕ} (gopp : Gene),
        gopp.type = -g.type →
        gopp.rank = 2 * q + 1 →
        2 ≤ X.1.1 gopp →
        (Y14 (Nat.zero_le q) hg_pol).1 +
            (X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
              Finsupp.single gopp 1 - Finsupp.single gopp 1) ≤ Y.1.1 →
        ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1)
    (hsame : g₂ = g) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  have hg_extra : 3 ≤ X.1.1 g := hg₂_same_extra hsame
  have hrestAfterDouble_g : restAfterDouble g = X.1.1 g - 2 := by
    rw [hrestAfterDouble_eq]
    simp [Finsupp.tsub_apply]
    omega
  have hrestAfterDouble_g_pos : 0 < restAfterDouble g := by
    rw [hrestAfterDouble_g]
    omega
  let restAfterTriple : Chromosome := restAfterDouble - Finsupp.single g 1
  have hrestAfterTriple_eq :
      restAfterTriple =
          X.1.1 - Finsupp.single g 1 - Finsupp.single g 1 -
            Finsupp.single g 1 := by
    dsimp [restAfterTriple]
    rw [hrestAfterDouble_eq]
  have hprimeX_eq_restAfterTriple :
      Chromosome.prime^[1] X.1.1 =
        Chromosome.prime^[1] restAfterTriple := by
    rw [hprimeX_eq_restAfterDouble]
    dsimp [restAfterTriple]
    exact prime_iterate_eq_sub_single_of_rank_le_of_pos
      (X := restAfterDouble) (gm := g) hrestAfterDouble_g_pos
      (by rw [hg_rank_one])
  have hrestAfterTriple_total :
      restAfterTriple.sum (fun _ n => n) + 3 =
        X.1.1.sum (fun _ n => n) := by
    have hdrop_last :
        restAfterTriple.sum (fun _ n => n) + 1 =
          restAfterDouble.sum (fun _ n => n) := by
      dsimp [restAfterTriple]
      exact totalMult_sub_single_one_of_pos hrestAfterDouble_g_pos
    omega
  let tailAfterG : Chromosome := X.1.1 - Finsupp.single g (X.1.1 g)
  have htailAfterG_def :
      tailAfterG = X.1.1 - Finsupp.single g (X.1.1 g) := rfl
  have htailAfterG_g_zero : tailAfterG g = 0 := by
    dsimp [tailAfterG]
    simp
  have htailAfterG_pos_X_ne :
      ∀ h : Gene, 0 < tailAfterG h → 0 < X.1.1 h ∧ h ≠ g := by
    intro h hh
    constructor
    · dsimp [tailAfterG] at hh
      exact lt_of_lt_of_le hh (Nat.sub_le _ _)
    · intro h_eq
      subst h_eq
      omega
  have htailAfterG_rank_ge_three :
      ∀ h : Gene, 0 < tailAfterG h → 3 ≤ h.rank := by
    intro h hh
    exact hX_rank_ge_three_of_ne_g h
      (htailAfterG_pos_X_ne h hh).1 (htailAfterG_pos_X_ne h hh).2
  have htailAfterG_zero_or_min :
      tailAfterG = 0 ∨
        ∃ gtail : Gene, 0 < tailAfterG gtail ∧
          (∀ h : Gene, 0 < tailAfterG h → gtail.rank ≤ h.rank) ∧
          3 ≤ gtail.rank := by
    by_cases htail_zero : tailAfterG = 0
    · exact Or.inl htail_zero
    · obtain ⟨gtail, hgtail, hgtail_min⟩ :=
        Mix2LambdaSection17.exists_min_rank_gene htail_zero
      exact Or.inr
        ⟨gtail, hgtail, hgtail_min, htailAfterG_rank_ge_three gtail hgtail⟩
  exact rank_one_double_same_gene_tail_frontier X Y hXY hcommon h17_1 hXpol
    hno_pair g g₂ hgX hgmin hg_pol hp hp0 hg_rank_one hXneg_zero hg_two
    hseed1 hXsig1_eq hYsig1_eq hgap1 restAfterDouble restAfterTriple
    tailAfterG hrestAfterDouble_eq hrestAfterDouble_ne hrestAfterDouble_mem
    hprimeX_eq_restAfterDouble hrestAfterDouble_total
    hg₂_rest hg₂min hXg₂ hg₂_pol hg₂_odd hX_rank_ge_three_of_ne_g
    hg₂min_X_ne_g hg₂_same_extra hg₂_rank_ge_three_of_ne_g
    htype16_boundary htype14_boundary hsame hg_extra hrestAfterTriple_eq
    hprimeX_eq_restAfterTriple hrestAfterTriple_total htailAfterG_def
    htailAfterG_g_zero htailAfterG_pos_X_ne htailAfterG_rank_ge_three
    htailAfterG_zero_or_min

end Mix2LambdaPi
