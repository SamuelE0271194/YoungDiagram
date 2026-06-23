import YoungDiagram.Theorem6.MixLambdaPi.Prelim
import YoungDiagram.Theorem6.MixLambdaPi.Drops
import YoungDiagram.Theorem6.MixLambdaPi.Propagation
import YoungDiagram.Theorem6.MixLambdaPi.Case3

/-!
# General Case 5 a-propagation for `Mix (Lambda, Pi)` Branch B.

The §16 Case 5 propagation must work *below* the minimal nonpolarized/negative gene,
where `X` may still contain positive genes (odd rank).  The key exact identity is, for
**even** `i ≤ k` (all neg/NP genes of `X` have rank `≥ k`):

  `a_X(i-1) - a_X(i) = b_X(0) - b_X(1)`   (the `a`-drop at even steps is constant).

This holds per-gene: a positive gene (odd rank) contributes `0` to both sides, a
nonpolarized gene (even rank) contributes `1/2`, a negative gene (odd rank) `1`.
-/

open Variety hiding prime prime_def
open Chromosome

namespace MixLambdaPi

/-- Per-gene exact identity behind the §16 Case 5 `a`-drop constancy.  For even `i ≥ 1`
and a gene of rank `r`, type `t` with the `Mix (Lambda, Pi)` parity
(`Pos/Neg ↦ odd r`, `NP ↦ even r`) and `r ≥ i` unless positive, the `a`-drop at the
`(i-1, i)` step equals the bottom `b`-drop. -/
lemma pergene_adrop {i : ℕ} (hi : Even i) (hi1 : 1 ≤ i) (r : ℕ) (t : GeneType)
    (hposodd : t = .Positive → Odd r) (hnegodd : t = .Negative → Odd r)
    (hsurv : t ≠ .Positive → i ≤ r) :
    (Gene.ofRank (r - (i - 1)) t).signature.1 - (Gene.ofRank (r - i) t).signature.1 =
    (Gene.ofRank r t).signature.2 - (Gene.ofRank (r - 1) t).signature.2 := by
  match t with
  | .NonPolarized =>
    have hri : i ≤ r := hsurv (by decide)
    rw [signature_ofRank_nonPolarized, signature_ofRank_nonPolarized,
      signature_ofRank_nonPolarized, signature_ofRank_nonPolarized]
    have e1 : r - (i - 1) = (r - i) + 1 := by omega
    have e2 : r = (r - 1) + 1 := by omega
    rw [e1]
    conv_rhs => rw [e2]
    push_cast [Nat.cast_sub (show i ≤ r by omega), Nat.cast_sub (show 1 ≤ r by omega)]
    ring
  | .Positive =>
    have hr : Odd r := hposodd rfl
    have hrpos : 1 ≤ r := by have := Nat.odd_iff.mp hr; omega
    by_cases hri : i ≤ r
    · -- surviving: a-drop at even step, r odd
      have hge1 : 1 ≤ r - (i - 1) := by omega
      have hstep := signature_ofRank_eq' (k := r - (i - 1)) (ε := GeneType.Positive) hge1 (by decide)
      have he : r - (i - 1) - 1 = r - i := by omega
      rw [he] at hstep
      have heven : Even (r - (i - 1)) := by
        rcases hr with ⟨s, hs⟩; rcases hi with ⟨u, hu⟩; rw [Nat.even_iff]; omega
      rw [hstep, if_pos heven]
      have hbstep := signature_ofRank_eq' (k := r) (ε := GeneType.Positive) (by omega) (by decide)
      rw [hbstep, if_neg (by rw [Nat.not_even_iff_odd]; exact hr)]
      simp [GeneType.neg_positive]
    · -- vanished: r < i, r odd; both a-residues are 0
      have h0a : r - (i - 1) = 0 := by omega
      have h0b : r - i = 0 := by omega
      rw [h0a, h0b]
      have hbstep := signature_ofRank_eq' (k := r) (ε := GeneType.Positive) (by omega) (by decide)
      rw [hbstep, if_neg (by rw [Nat.not_even_iff_odd]; exact hr)]
      simp
  | .Negative =>
    have hr : Odd r := hnegodd rfl
    have hri : i ≤ r := hsurv (by decide)
    have hge1 : 1 ≤ r - (i - 1) := by omega
    have hstep := signature_ofRank_eq' (k := r - (i - 1)) (ε := GeneType.Negative) hge1 (by decide)
    have he : r - (i - 1) - 1 = r - i := by omega
    rw [he] at hstep
    have heven : Even (r - (i - 1)) := by
      rcases hr with ⟨s, hs⟩; rcases hi with ⟨u, hu⟩; rw [Nat.even_iff]; omega
    rw [hstep, if_pos heven]
    have hbstep := signature_ofRank_eq' (k := r) (ε := GeneType.Negative) (by omega) (by decide)
    rw [hbstep, if_neg (by rw [Nat.not_even_iff_odd]; exact hr)]
    simp [GeneType.neg_negative]

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

/-- `(signature (prime^[m] X)).1` as a sum over genes. -/
private lemma sig_iterate_fst_sum (X : Chromosome) (m : ℕ) :
    (signature (Chromosome.prime^[m] X)).1 =
    X.sum (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature.1) := by
  rw [sig_iterate_eq_sum X m]
  exact map_finsuppSum (AddMonoidHom.fst ℚ ℚ) X
    (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature)

/-- `(signature (prime^[m] X)).2` as a sum over genes. -/
private lemma sig_iterate_snd_sum (X : Chromosome) (m : ℕ) :
    (signature (Chromosome.prime^[m] X)).2 =
    X.sum (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature.2) := by
  rw [sig_iterate_eq_sum X m]
  exact map_finsuppSum (AddMonoidHom.snd ℚ ℚ) X
    (fun g k => (k : ℚ) • (Gene.ofRank (g.rank - m) g.type).signature)

/-- **§16 Case 5 exact `a`-drop.**  For even `i ≥ 2`, with `Mix (Lambda, Pi)` parity and all
neg/NP genes of rank `≥ i`, the `a`-drop at the `(i-1, i)` step equals the bottom `b`-drop. -/
lemma xdrop_eq {X : Chromosome} {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i)
    (hpar : ∀ g ∈ X.support, (g.type = .Positive → Odd g.rank) ∧ (g.type = .Negative → Odd g.rank))
    (hsurv : ∀ g ∈ X.support, g.type ≠ .Positive → i ≤ g.rank) :
    (signature (Chromosome.prime^[i - 1] X)).1 - (signature (Chromosome.prime^[i] X)).1 =
    (signature X).2 - (signature (Chromosome.prime^[1] X)).2 := by
  have h0 : signature X = signature (Chromosome.prime^[0] X) := rfl
  rw [sig_iterate_fst_sum X (i - 1), sig_iterate_fst_sum X i, h0,
    sig_iterate_snd_sum X 0, sig_iterate_snd_sum X 1]
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← smul_sub, ← smul_sub]
  congr 1
  have hg' := hsurv g hg
  have hp := hpar g hg
  have := pergene_adrop hi (by omega) g.rank g.type hp.1 hp.2 hg'
  simpa [Nat.sub_zero] using this

/-- `b`-drop at even index is bounded by the bottom `b`-drop. -/
private lemma bdrop_even_le {Y : Chromosome} (hY : Y ∈ Mix (Lambda, Pi)) (t : ℕ) :
    (Sigma.sigma Y (2 * t)).2 - (Sigma.sigma Y (2 * t + 1)).2 ≤
      (Sigma.sigma Y 0).2 - (Sigma.sigma Y 1).2 := by
  induction t with
  | zero => simp
  | succ k ih =>
    have hodd := cond_15_7_Mix_Lambda_Pi hY (2 * k + 1)
    rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨k, by ring⟩),
      show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show 2 * k + 1 + 2 = 2 * k + 3 from by ring] at hodd
    have heven := cond_15_7_Mix_Lambda_Pi hY (2 * k)
    rw [if_pos ⟨k, by ring⟩] at heven
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
      show 2 * k + 2 + 1 = 2 * k + 3 from by ring]
    linarith

/-- **General §16 Case 5 a-propagation.**  `a_X(j) + 1 ≤ a_Y(j)` for even `j ∈ [2, k]`,
where all neg/NP genes of `X` have rank `≥ k` (positive genes below `k` are allowed). -/
lemma branchB_case5_aprop_gen {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1)
    (k : ℕ) (hk : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → k ≤ g.rank) :
    ∀ j, 2 ≤ j → j ≤ k → Even j →
        (Sigma.sigma X.1.1 j).1 + 1 ≤ (Sigma.sigma Y.1.1 j).1 := by
  -- parity of X's genes
  have hpar : ∀ g ∈ X.1.1.support,
      (g.type = .Positive → Odd g.rank) ∧ (g.type = .Negative → Odd g.rank) := by
    intro g hg
    refine ⟨fun h => rank_odd_of_polarized X.1.2 (by rw [h]; decide)
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)),
      fun h => rank_odd_of_polarized X.1.2 (by rw [h]; decide)
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg))⟩
  -- (C): X bottom b-drop strictly exceeds Y bottom b-drop
  have hXodd : (Sigma.sigma X.1.1 1).1 = (Sigma.sigma X.1.1 1).2 :=
    signature_prime_iterate_odd_eq_components X.1.2 (by decide)
  have hYodd : (Sigma.sigma Y.1.1 1).1 = (Sigma.sigma Y.1.1 1).2 :=
    signature_prime_iterate_odd_eq_components Y.1.2 (by decide)
  have hX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1); simpa [Sigma.sigma, X.2] using this
  have hY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
    have := @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1); simpa [Sigma.sigma, Y.2] using this
  have ha0 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 := (le_iff_dominates.mp hXY.le 0).1
  have hC : (Sigma.sigma Y.1.1 0).2 - (Sigma.sigma Y.1.1 1).2 <
      (Sigma.sigma X.1.1 0).2 - (Sigma.sigma X.1.1 1).2 := by
    rw [← hXodd, ← hYodd]; linarith
  intro j hj2 hjk hje
  -- (A) X exact a-drop
  have hxd : (Sigma.sigma X.1.1 (j - 1)).1 - (Sigma.sigma X.1.1 j).1 =
      (Sigma.sigma X.1.1 0).2 - (Sigma.sigma X.1.1 1).2 :=
    xdrop_eq hje hj2 hpar (fun g hg hgnp => le_trans hjk (hk g hg hgnp))
  -- (B) Y a-drop bound
  obtain ⟨t, ht⟩ : ∃ t, j = 2 * t := by rcases hje with ⟨r, hr⟩; exact ⟨r, by omega⟩
  have hcond := cond_15_7_Mix_Lambda_Pi Y.1.2 (j - 2)
  rw [if_pos (by rcases hje with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩)] at hcond
  have he1 : j - 2 + 1 = j - 1 := by omega
  have he2 : j - 2 + 2 = j := by omega
  rw [he1, he2] at hcond
  have hbev : (Sigma.sigma Y.1.1 (j - 2)).2 - (Sigma.sigma Y.1.1 (j - 1)).2 ≤
      (Sigma.sigma Y.1.1 0).2 - (Sigma.sigma Y.1.1 1).2 := by
    have hbe := bdrop_even_le Y.1.2 (t - 1)
    have e1 : 2 * (t - 1) = j - 2 := by omega
    rw [e1, he1] at hbe; exact hbe
  have hB : (Sigma.sigma Y.1.1 (j - 1)).1 - (Sigma.sigma Y.1.1 j).1 ≤
      (Sigma.sigma Y.1.1 0).2 - (Sigma.sigma Y.1.1 1).2 := by linarith
  -- (D) dominance
  have hD : (Sigma.sigma X.1.1 (j - 1)).1 ≤ (Sigma.sigma Y.1.1 (j - 1)).1 :=
    (le_iff_dominates.mp hXY.le (j - 1)).1
  -- strict, then integrality
  have hlt : (Sigma.sigma X.1.1 j).1 < (Sigma.sigma Y.1.1 j).1 := by linarith
  obtain ⟨zX, hzX⟩ := sig_fst_isInt_even X.1.2 hje
  obtain ⟨zY, hzY⟩ := sig_fst_isInt_even Y.1.2 hje
  rw [hzX, hzY] at hlt ⊢
  have hz : zX < zY := by exact_mod_cast hlt
  have : (zX : ℚ) + 1 ≤ (zY : ℚ) := by exact_mod_cast hz
  linarith

/-- §16 Case 5 existence: `X` (with `g₁ = g⁺(1)` minimal and `a_1 < c_1`) contains a
negative or nonpolarized gene.  If not, `branchB_case5_aprop_gen` (vacuous hypothesis)
would force `a_X(2N) + 1 ≤ a_Y(2N) = 0`. -/
lemma branchB_case5_exists_negNP {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (ha : (Sigma.sigma X.1.1 1).1 < (Sigma.sigma Y.1.1 1).1) :
    ∃ g ∈ X.1.1.support, g.type ≠ .Positive := by
  by_contra hcon
  push_neg at hcon
  have hk : ∀ g ∈ X.1.1.support, g.type ≠ .Positive → 2 * N + 2 ≤ g.rank :=
    fun g hg hgnp => absurd (hcon g hg) hgnp
  have hprop := branchB_case5_aprop_gen X Y hXY ha (2 * N + 2) hk (2 * N + 2)
    (by omega) (le_refl _) ⟨N + 1, by ring⟩
  have hzero : ∀ Z : nMixLambdaPi N, Chromosome.prime^[2 * N + 2] Z.1.1 = 0 := by
    intro Z
    apply prime_iterate_zero_of_maxRank_le
    have h2 := maxRank_le_rank Z.1.1
    rw [Z.2] at h2
    exact le_trans h2 (by omega)
  rw [show Sigma.sigma X.1.1 (2 * N + 2) = signature (Chromosome.prime^[2 * N + 2] X.1.1) from rfl,
    show Sigma.sigma Y.1.1 (2 * N + 2) = signature (Chromosome.prime^[2 * N + 2] Y.1.1) from rfl,
    hzero X, hzero Y, map_zero] at hprop
  simp only [Prod.fst_zero, zero_add] at hprop
  exact absurd hprop (by norm_num)

/-- `prime^[j] Y ≠ 0` for `j` below the rank of any gene of `X` (via dominance). -/
lemma Ywin_below {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1) (gk : Gene)
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

/-- Top-boundary nonvanishing for §16 Branch B Case 5/Case 3 type7 (`gk = g⁻(2n'+1)`):
`prime^[2n'+1] Y ≠ 0`.  b-mirror of `branchA_case2_Ynonzero_top`. -/
lemma branchB_case5_Ynonzero_top {N : ℕ} (X Y : nMixLambdaPi N) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.1 g ∧ 0 < Y.1.1 g)
    (n' : ℕ) (gk : Gene) (hgk_rank : gk.rank = 2 * n' + 1)
    (hgk_neg : gk.type = .Negative) (hXgk : 0 < X.1.1 gk) :
    Chromosome.prime^[2 * n' + 1] Y.1.1 ≠ 0 := by
  push_neg at hcommon
  intro hYzero
  have hbX : 1 ≤ (signature (Chromosome.prime^[2 * n'] X.1.1)).2 := by
    have hgk_single : Gene.ofRank gk.rank gk.type = (Finsupp.single gk 1 : Chromosome) :=
      Gene.ofRank_eq_gene
    have hprime : Chromosome.prime^[2 * n'] (Finsupp.single gk 1 : Chromosome) =
        Gene.ofRank 1 .Negative := by
      rw [← hgk_single, prime_iterate_ofRank, hgk_rank, hgk_neg,
        show 2 * n' + 1 - 2 * n' = 1 from by omega]
    have hXeq : X.1.1 = Finsupp.single gk 1 + (X.1.1 - Finsupp.single gk 1) := by
      rw [add_comm, sub_single_add_single_eq hXgk]
    calc (1 : ℚ) = (signature (Gene.ofRank 1 .Negative : Chromosome)).2 := by
          rw [signature_ofRank_one_negative]
      _ = (signature (Chromosome.prime^[2 * n'] (Finsupp.single gk 1 : Chromosome))).2 := by
          rw [hprime]
      _ ≤ (signature (Chromosome.prime^[2 * n'] X.1.1)).2 := by
          conv_rhs => rw [hXeq]
          rw [iterate_map_add, map_add]
          exact le_add_of_nonneg_right (signature_nonneg _).2
  have hbY : 1 ≤ (signature (Chromosome.prime^[2 * n'] Y.1.1)).2 :=
    le_trans hbX (le_iff_dominates.mp hXY.le (2 * n')).2
  set W := Chromosome.prime^[2 * n'] Y.1.1 with hWdef
  have hWprime : Chromosome.prime W = 0 := by
    rw [hWdef, ← Function.iterate_succ_apply' Chromosome.prime (2 * n') Y.1.1]
    exact hYzero
  have hWmem : W ∈ Mix (Lambda, Pi) := by
    have heven : Even (2 * n') := ⟨n', by ring⟩
    have h := prime_mem_Mix_Lambda_Pi_iterate Y.1.2 (2 * n')
    rwa [if_pos heven] at h
  have hWgenes : ∀ h ∈ W.support, h.signature.2 = 0 := by
    intro h hh
    have hr1 : h.rank = 1 := rank_one_of_prime_eq_zero hWprime hh
    have hpol : h.type ≠ .NonPolarized := by
      have hod : 0 < W.oddPart h := by
        rw [oddPart_eq, Finsupp.filter_apply, if_pos (by rw [hr1]; exact ⟨0, rfl⟩)]
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hh)
      exact IsPolarized_def'.mp (mem_Pi_iff.mp hWmem.2) h
        (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hod))
    have hnneg : h.type ≠ .Negative := by
      intro hneg
      have hWh : W h = Y.1.1 ⟨h.rank + 2 * n', h.type,
          Nat.le_add_right_of_le h.rank_pos⟩ := prime_iterate_coeff (2 * n') Y.1.1 h
      have hge : (⟨h.rank + 2 * n', h.type, Nat.le_add_right_of_le h.rank_pos⟩ : Gene) = gk :=
        Gene.ext (by show h.rank + 2 * n' = gk.rank; rw [hgk_rank]; omega)
          (by show h.type = gk.type; rw [hneg, hgk_neg])
      rw [hge] at hWh
      have hYgk : Y.1.1 gk = 0 := Nat.le_zero.mp (hcommon gk hXgk)
      rw [hYgk] at hWh
      exact (Finsupp.mem_support_iff.mp hh) hWh
    have hpos : h.type = .Positive := by
      cases ht : h.type with
      | NonPolarized => exact absurd ht hpol
      | Negative => exact absurd ht hnneg
      | Positive => rfl
    rw [Gene.signature_of_positive hpos, if_neg (by rw [hr1]; decide)]
    simp [hr1]
  have hW0 : (signature W).2 = 0 := by
    rw [signature_snd, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro h hh
    rw [hWgenes h hh, smul_zero]
  rw [hW0] at hbY
  linarith

end MixLambdaPi



