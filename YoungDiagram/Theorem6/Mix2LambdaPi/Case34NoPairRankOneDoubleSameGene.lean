import YoungDiagram.Theorem6.Mix2LambdaPi.Case34Gaps
import YoungDiagram.Theorem6.Mix2LambdaPi.Type14
import YoungDiagram.Theorem6.Mix2LambdaPi.Type16

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

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
  sorry

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
