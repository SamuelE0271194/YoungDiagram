import YoungDiagram.Theorem6.MixPiLambda.Prelim
import YoungDiagram.Theorem6.MixPiLambda.Drops

/-!
# §16 propagation core for `Mix (Pi, Lambda)` Branch A Case 1.

Parity-mirror of `MixLambdaPi/Propagation.lean`.  For `Mix (Pi, Lambda)` the
nonpolarized genes sit at ODD rank, so the §16 window is anchored at the odd rank
`2m'+1` and the relevant levels are ODD.  Integrality at odd levels holds because
`prime^[odd]` maps `Mix (Pi, Lambda)` into `Mix (Lambda, Pi)` (whose `oddPart ∈ Pi`
is integral and whose `evenPart ∈ Lambda` has even ranks).

`KEY_Y` uses the odd branch of `cond_15_6_Mix_Pi_Lambda` (where LP used the even
branch of `cond_15_7`); the resulting inequality has the same shape.  The
X-structure lemmas (`cells`, `twostep`, `shift`) are parity-agnostic and copied
verbatim.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixPiLambda

/-- Single-step rank-drop antitonicity for `Mix (Pi, Lambda)`. -/
private lemma rank_drop_step {Z : Chromosome} (hZ : Z ∈ Mix (Pi, Lambda)) (i : ℕ) :
    (Sigma.sigma Z (i + 1)).1 + (Sigma.sigma Z (i + 1)).2 -
        ((Sigma.sigma Z (i + 2)).1 + (Sigma.sigma Z (i + 2)).2) ≤
      (Sigma.sigma Z i).1 + (Sigma.sigma Z i).2 -
        ((Sigma.sigma Z (i + 1)).1 + (Sigma.sigma Z (i + 1)).2) := by
  have h6 := cond_15_6_Mix_Pi_Lambda hZ i
  have h7 := cond_15_7_Mix_Pi_Lambda hZ i
  by_cases hi : Even i
  · rw [if_pos hi] at h6 h7; linarith
  · rw [if_neg hi] at h6 h7; linarith

/-- Telescoped: the rank-drop at level `i` is at most the rank-drop at level `0`. -/
lemma rank_drop_le {Z : Chromosome} (hZ : Z ∈ Mix (Pi, Lambda)) (i : ℕ) :
    (Sigma.sigma Z i).1 + (Sigma.sigma Z i).2 -
        ((Sigma.sigma Z (i + 1)).1 + (Sigma.sigma Z (i + 1)).2) ≤
      (Sigma.sigma Z 0).1 + (Sigma.sigma Z 0).2 -
        ((Sigma.sigma Z 1).1 + (Sigma.sigma Z 1).2) := by
  induction i with
  | zero => exact le_refl _
  | succ k ih => exact le_trans (rank_drop_step hZ k) ih

/-- KEY_Y: the §16 bound on `Y`'s `a`-component 2-step drop by `r_0 - r_1 - 1`.
At ODD levels, via the odd branch of `cond_15_6_Mix_Pi_Lambda`.  Takes the *total*
rank gap `r_1 < s_1` directly (self-dual under negation), so the same lemma serves
the `a`-propagation (Case 1) and the sign-dual `b`-propagation (Case 2). -/
lemma KEY_Y {N : ℕ} (X Y : nMixPiLambda N)
    (hgap_nat : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    {i : ℕ} (hi : Odd i) :
    (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma Y.1.1 (i + 2)).1 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
  have hcond6 := cond_15_6_Mix_Pi_Lambda Y.1.2 i
  rw [if_neg (Nat.not_even_iff_odd.2 hi)] at hcond6
  have hdrop := rank_drop_le Y.1.2 i
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
    simpa [Sigma.sigma, X.2] using this
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
    simpa [Sigma.sigma, Y.2] using this
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgap : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 1 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by exact_mod_cast Nat.succ_le_of_lt hgap_nat
  linarith

/-- The total rank gap `r_1 < s_1`, derived from the level-1 `a`-strict `ha` plus
dominance.  This is the hypothesis `KEY_Y` actually needs. -/
lemma rank_gap_one {N : ℕ} (X Y : nMixPiLambda N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) :
    (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank := by
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hb1 : (Sigma.sigma X.1.1 1).2 ≤ (Sigma.sigma Y.1.1 1).2 :=
    (le_iff_dominates.mp hXY.le 1).2
  have : ((Chromosome.prime^[1] X.1.1).rank : ℚ) < ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    rw [← hrX1, ← hrY1]; linarith
  exact_mod_cast this

private lemma X_sub_add {N : ℕ} (X : nMixPiLambda N) (gm : Gene) (hgm1 : X.1.1 gm = 1) :
    X.1.1 = (X.1.1 - Finsupp.single gm 1) + Finsupp.single gm 1 := by
  ext g
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hg : gm = g
  · subst hg; rw [if_pos rfl]; omega
  · rw [if_neg hg]; omega

lemma cells {Z : Chromosome} :
    (Z.rank : ℚ) - (Z.prime.rank : ℚ) = Z.sum (fun _ m => (m : ℚ)) := by
  rw [rank_def, rank_of_prime, Finsupp.sum, Finsupp.sum, Finsupp.sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  have h1 : (1 : ℕ) ≤ g.rank := g.rank_pos
  push_cast [smul_eq_mul, Nat.cast_sub h1]
  ring

lemma twostep {W : Chromosome} {i : ℕ} (hW : ∀ g ∈ W.support, i + 2 ≤ g.rank) :
    (Sigma.sigma W i).1 - (Sigma.sigma W (i + 2)).1 = (W.sum fun _ m => (m : ℚ)) := by
  induction W using Finsupp.induction with
  | zero => simp [Sigma.sigma]
  | single_add g n f hg hn ih =>
    have hgr : i + 2 ≤ g.rank := hW g (by simp [hn])
    have hf : ∀ g' ∈ f.support, i + 2 ≤ g'.rank := by
      intro g' hg'
      apply hW
      simp only [Finsupp.mem_support_iff, Finsupp.add_apply]
      have hz : (Finsupp.single g n) g' = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl; exact hg hg'
      rw [hz, zero_add]; exact Finsupp.mem_support_iff.mp hg'
    have he : (Finsupp.single g n : Chromosome) = n • Gene.ofRank g.rank g.type := by
      rw [Gene.ofRank_eq_gene]; simp
    have e1 : Chromosome.prime^[i] (Finsupp.single g n) =
        n • Gene.ofRank (g.rank - i) g.type := by rw [he, iterate_map_nsmul, prime_iterate_ofRank]
    have e2 : Chromosome.prime^[i + 2] (Finsupp.single g n) =
        n • Gene.ofRank (g.rank - (i + 2)) g.type := by
      rw [he, iterate_map_nsmul, prime_iterate_ofRank]
    have hsingle : (Sigma.sigma (Finsupp.single g n) i).1 -
        (Sigma.sigma (Finsupp.single g n) (i + 2)).1 = (n : ℚ) := by
      simp only [Sigma.sigma, e1, e2, map_nsmul]
      rw [show g.rank - i = (g.rank - (i + 2)) + 2 by omega, signature_ofRank_eq₂']
      simp only [Prod.smul_fst, Prod.fst_add]
      ring
    rw [Finsupp.sum_add_index (by simp) (by intros; simp), Finsupp.sum_single_index (by simp)]
    rw [Sigma.sigma_linearity, Sigma.sigma_linearity, Prod.fst_add, Prod.fst_add]
    rw [show (Sigma.sigma (Finsupp.single g n) i).1 + (Sigma.sigma f i).1 -
        ((Sigma.sigma (Finsupp.single g n) (i + 2)).1 + (Sigma.sigma f (i + 2)).1) =
        ((Sigma.sigma (Finsupp.single g n) i).1 - (Sigma.sigma (Finsupp.single g n) (i + 2)).1) +
        ((Sigma.sigma f i).1 - (Sigma.sigma f (i + 2)).1) by ring]
    rw [hsingle, ih hf]

lemma twostep_snd {W : Chromosome} {i : ℕ} (hW : ∀ g ∈ W.support, i + 2 ≤ g.rank) :
    (Sigma.sigma W i).2 - (Sigma.sigma W (i + 2)).2 = (W.sum fun _ m => (m : ℚ)) := by
  induction W using Finsupp.induction with
  | zero => simp [Sigma.sigma]
  | single_add g n f hg hn ih =>
    have hgr : i + 2 ≤ g.rank := hW g (by simp [hn])
    have hf : ∀ g' ∈ f.support, i + 2 ≤ g'.rank := by
      intro g' hg'
      apply hW
      simp only [Finsupp.mem_support_iff, Finsupp.add_apply]
      have hz : (Finsupp.single g n) g' = 0 := by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl; exact hg hg'
      rw [hz, zero_add]; exact Finsupp.mem_support_iff.mp hg'
    have he : (Finsupp.single g n : Chromosome) = n • Gene.ofRank g.rank g.type := by
      rw [Gene.ofRank_eq_gene]; simp
    have e1 : Chromosome.prime^[i] (Finsupp.single g n) =
        n • Gene.ofRank (g.rank - i) g.type := by rw [he, iterate_map_nsmul, prime_iterate_ofRank]
    have e2 : Chromosome.prime^[i + 2] (Finsupp.single g n) =
        n • Gene.ofRank (g.rank - (i + 2)) g.type := by
      rw [he, iterate_map_nsmul, prime_iterate_ofRank]
    have hsingle : (Sigma.sigma (Finsupp.single g n) i).2 -
        (Sigma.sigma (Finsupp.single g n) (i + 2)).2 = (n : ℚ) := by
      simp only [Sigma.sigma, e1, e2, map_nsmul]
      rw [show g.rank - i = (g.rank - (i + 2)) + 2 by omega, signature_ofRank_eq₂']
      simp only [Prod.smul_snd, Prod.snd_add]
      ring
    rw [Finsupp.sum_add_index (by simp) (by intros; simp), Finsupp.sum_single_index (by simp)]
    rw [Sigma.sigma_linearity, Sigma.sigma_linearity, Prod.snd_add, Prod.snd_add]
    rw [show (Sigma.sigma (Finsupp.single g n) i).2 + (Sigma.sigma f i).2 -
        ((Sigma.sigma (Finsupp.single g n) (i + 2)).2 + (Sigma.sigma f (i + 2)).2) =
        ((Sigma.sigma (Finsupp.single g n) i).2 - (Sigma.sigma (Finsupp.single g n) (i + 2)).2) +
        ((Sigma.sigma f i).2 - (Sigma.sigma f (i + 2)).2) by ring]
    rw [hsingle, ih hf]

private lemma shift {N : ℕ} (X : nMixPiLambda N) (gm : Gene) {m' : ℕ}
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm1 : X.1.1 gm = 1) {i : ℕ} (hi : 2 * m' + 1 ≤ i) :
    Sigma.sigma X.1.1 i = Sigma.sigma (X.1.1 - Finsupp.single gm 1) i := by
  have h3 : Chromosome.prime^[i] (Finsupp.single gm 1) = 0 := by
    rw [← prime_iterate_eq_zero_rank_le]
    intro g hg
    rw [Finsupp.support_single _ (by norm_num), Finset.mem_singleton] at hg
    subst hg; omega
  conv_lhs => rw [X_sub_add X gm hgm1]
  rw [Sigma.sigma_linearity]
  simp only [Sigma.sigma, h3, map_zero, add_zero]

private lemma cells_of_X {N : ℕ} (X : nMixPiLambda N) (gm : Gene)
    (hgm1 : X.1.1 gm = 1) :
    (X.1.1.sum fun _ m => (m : ℚ)) =
      (X.1.1 - Finsupp.single gm 1).sum (fun _ m => (m : ℚ)) + 1 := by
  conv_lhs => rw [X_sub_add X gm hgm1]
  rw [Finsupp.sum_add_index (by simp) (by intros; simp), Finsupp.sum_single_index (by simp)]
  norm_num

/-- KEY_X: the §16 X-structure count, anchored at the odd minimal NP gene rank
`2m'+1`.  Parity-agnostic in the underlying `twostep`. -/
private lemma KEY_X {N : ℕ} (X : nMixPiLambda N) {m' n' : ℕ}
    {gm : Gene} (hgm_rank : gm.rank = 2 * m' + 1) (_ : gm.type = .NonPolarized)
    (hgm1 : X.1.1 gm = 1)
    (_ : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 1 ≤ g.rank)
    {i : ℕ} (hi1 : 2 * m' + 1 ≤ i) (hi2 : i + 2 ≤ 2 * n' + 1) :
    (Sigma.sigma X.1.1 i).1 - (Sigma.sigma X.1.1 (i + 2)).1 =
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 1 := by
  have hW := shift X gm hgm_rank hgm1 hi1
  have hW' := shift X gm hgm_rank hgm1 (by omega : 2 * m' + 1 ≤ i + 2)
  rw [hW, hW']
  have h2 : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, i + 2 ≤ g.rank := by
    intro g hg; have := h2nd g hg; omega
  rw [twostep h2]
  have h4 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (X.1.1.rank : ℚ) :=
    @signature_sum_eq_rank _
  have h5 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 = (X.1.1.prime.rank : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[1] X.1.1)
    simpa [Sigma.sigma, Function.iterate_one] using this
  rw [h4, h5, cells, cells_of_X X gm hgm1]
  ring

private lemma even_rank_of_even_support {Z : Chromosome}
    (hev : ∀ g ∈ Z.support, Even g.rank) : Even Z.rank := by
  rw [rank_def, Finsupp.sum]
  apply Finset.even_sum
  intro g hg
  rw [smul_eq_mul]
  exact (hev g hg).mul_left _

private lemma sig_fst_eq_comp_of_even {Z : Chromosome}
    (hev : ∀ g ∈ Z.support, Even g.rank) : (signature Z).1 = (signature Z).2 := by
  rw [signature_fst, signature_snd]
  apply Finset.sum_congr rfl
  intro g hg
  have hg_ev := hev g hg
  have hg_sig : g.signature.1 = g.signature.2 := by
    have h1 : g.signature = ((g.rank : ℚ) / 2, (g.rank : ℚ) / 2) := by
      cases ht : g.type with
      | NonPolarized => exact Gene.signature_of_nonPolarized ht
      | Positive => rw [Gene.signature_of_positive ht, if_pos hg_ev]
      | Negative => rw [Gene.signature_of_negative ht, if_pos hg_ev]
    rw [h1]
  simp [hg_sig]

/-- Odd-level integrality: at odd level, the first signature component of a
`Mix (Pi, Lambda)` element is an integer.  (`prime^[odd]` lands in `Mix (Lambda, Pi)`,
whose `oddPart ∈ Pi` is integral and `evenPart ∈ Lambda` has even ranks.) -/
lemma sig_fst_isInt_odd {Z : Chromosome} (hZ : Z ∈ Mix (Pi, Lambda))
    {i : ℕ} (hi : Odd i) : ∃ z : ℤ, (Sigma.sigma Z i).1 = (z : ℚ) := by
  have hW : Chromosome.prime^[i] Z ∈ Mix (Lambda, Pi) := by
    have := prime_mem_Mix_Pi_Lambda_iterate hZ i
    rwa [if_neg (Nat.not_even_iff_odd.2 hi)] at this
  set W := Chromosome.prime^[i] Z with hWdef
  obtain ⟨n, hn⟩ := signature_pi_isNat (mem_Mix_iff.mp hW).2
  have hev : ∀ g ∈ W.evenPart.support, Even g.rank := by
    intro g hg
    rw [Finsupp.mem_support_iff, evenPart_eq, Finsupp.filter_apply] at hg
    by_contra h
    rw [if_neg h] at hg
    exact hg rfl
  have hsym := sig_fst_eq_comp_of_even hev
  have hsum : (signature W.evenPart).1 + (signature W.evenPart).2 =
      (W.evenPart.rank : ℚ) := signature_sum_eq_rank
  obtain ⟨k, hk⟩ := even_rank_of_even_support hev
  have heven_int : (signature W.evenPart).1 = (k : ℚ) := by
    rw [hsym] at hsum
    have h2 : (2 : ℚ) * (signature W.evenPart).2 = (W.evenPart.rank : ℚ) := by linarith
    rw [hk] at h2
    push_cast at h2
    rw [hsym]; linarith
  have hdecomp : W = W.oddPart + W.evenPart := parity_decomposition W
  have hsig : (signature W).1 = (signature W.oddPart).1 + (signature W.evenPart).1 := by
    conv_lhs => rw [hdecomp]
    rw [map_add]; rfl
  refine ⟨(n.1 : ℤ) + (k : ℤ), ?_⟩
  change (signature W).1 = _
  rw [hsig, hn, heven_int]
  push_cast; ring

/-- **Generalized §16 drop-chain telescoping** (gk-free) for `Mix (Pi, Lambda)`.
Window anchored at the odd minimal NP gene rank `2m'+1`; levels are ODD. -/
lemma branchA_hprop_odd_gen {N : ℕ}
    (X Y : nMixPiLambda N)
    (hgap_nat : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (m' n' : ℕ) (_ : m' ≤ n')
    (gm : Gene)
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgm1 : X.1.1 gm = 1)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 1 ≤ g.rank)
    (ha_m : (Sigma.sigma X.1.1 (2 * m' + 1)).1 < (Sigma.sigma Y.1.1 (2 * m' + 1)).1) :
    ∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * n' + 1 → Odd j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
  have hstep : ∀ i, 2 * m' + 1 ≤ i → i + 2 ≤ 2 * n' + 1 → Odd i →
      (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma X.1.1 i).1 ≤
        (Sigma.sigma Y.1.1 (i + 2)).1 - (Sigma.sigma X.1.1 (i + 2)).1 := by
    intro i hi1 hi2 hoi
    have hY := KEY_Y X Y hgap_nat hoi
    have hX := KEY_X X hgm_rank hgm_np hgm1 hmin h2nd hi1 hi2
    linarith
  have hmono : ∀ t, 2 * m' + 1 + 2 * t ≤ 2 * n' + 1 →
      (Sigma.sigma Y.1.1 (2 * m' + 1)).1 - (Sigma.sigma X.1.1 (2 * m' + 1)).1 ≤
        (Sigma.sigma Y.1.1 (2 * m' + 1 + 2 * t)).1 -
          (Sigma.sigma X.1.1 (2 * m' + 1 + 2 * t)).1 := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ k ih =>
      intro hrange
      have hk : 2 * m' + 1 + 2 * k ≤ 2 * n' + 1 := by omega
      have hodd : Odd (2 * m' + 1 + 2 * k) := ⟨m' + k, by ring⟩
      have hstep' := hstep (2 * m' + 1 + 2 * k) (by omega) (by omega) hodd
      have : 2 * m' + 1 + 2 * k + 2 = 2 * m' + 1 + 2 * (k + 1) := by ring
      rw [this] at hstep'
      exact le_trans (ih hk) hstep'
  intro j hj1 hj2 hoj
  obtain ⟨t, ht⟩ : ∃ t, j = 2 * m' + 1 + 2 * t := by
    obtain ⟨r, hr⟩ := hoj
    exact ⟨r - m', by omega⟩
  subst ht
  have hf_pos : 0 < (Sigma.sigma Y.1.1 (2 * m' + 1 + 2 * t)).1 -
      (Sigma.sigma X.1.1 (2 * m' + 1 + 2 * t)).1 := by
    have hb := hmono t hj2
    linarith
  obtain ⟨zX, hzX⟩ := sig_fst_isInt_odd X.1.2 hoj
  obtain ⟨zY, hzY⟩ := sig_fst_isInt_odd Y.1.2 hoj
  rw [hzX, hzY] at hf_pos ⊢
  have hlt : (zX : ℚ) < (zY : ℚ) := by linarith
  have hlt' : zX < zY := by exact_mod_cast hlt
  have : (zX : ℚ) + 1 ≤ (zY : ℚ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt'
  linarith

/-- §16 drop-chain telescoping for Branch A Case 1 (`gk` nonpolarized of rank `2n'+1`).
Takes the self-dual total-rank gap `hgap_nat`, so the same lemma drives the direct
`a`-propagation and (via sign-duality) the `b`-version. -/
lemma branchA_case1_hprop_odd {N : ℕ}
    (X Y : nMixPiLambda N)
    (hgap_nat : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (m' n' : ℕ) (hmn : m' ≤ n')
    (gm gk : Gene)
    (hgm_rank : gm.rank = 2 * m' + 1) (hgm_np : gm.type = .NonPolarized)
    (hgk_rank : gk.rank = 2 * n' + 1) (hgk_np : gk.type = .NonPolarized)
    (hXgm : 0 < X.1.1 gm)
    (_ : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gk)
    (hne : gm ≠ gk)
    (hmin : ∀ g ∈ X.1.1.support, 2 * m' + 1 ≤ g.rank)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, 2 * n' + 1 ≤ g.rank)
    (ha_m : (Sigma.sigma X.1.1 (2 * m' + 1)).1 < (Sigma.sigma Y.1.1 (2 * m' + 1)).1) :
    ∀ j, 2 * m' + 1 ≤ j → j ≤ 2 * n' + 1 → Odd j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
  have hgm1 : X.1.1 gm = 1 := by
    by_contra h
    have h2 : 2 ≤ X.1.1 gm := by omega
    have hgmW : 0 < (X.1.1 - Finsupp.single gm 1 : Chromosome) gm := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
    have hgm_supp : gm ∈ (X.1.1 - Finsupp.single gm 1).support :=
      Finsupp.mem_support_iff.mpr (by exact Nat.pos_iff_ne_zero.mp hgmW)
    have hge := h2nd gm hgm_supp
    rw [hgm_rank] at hge
    have hnm : n' = m' := by omega
    exact hne (Gene.ext (by rw [hgm_rank, hgk_rank, hnm]) (by rw [hgm_np, hgk_np]))
  exact branchA_hprop_odd_gen X Y hgap_nat m' n' hmn gm hgm_rank hgm_np hgm1
    hmin h2nd ha_m

end MixPiLambda
