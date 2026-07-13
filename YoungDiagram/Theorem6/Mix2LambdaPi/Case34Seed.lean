import YoungDiagram.Theorem6.Mix2LambdaPi.Window

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

/-- §17 Case 4 level-1 gap: for Label 3, `prime X` and `prime Y` lie in
`Mix (Pi, 2 • Lambda)`, so their signature components are integers.  A strict
gap in *both* components at level 1 therefore gives a rank gap of at least `2`. -/
lemma case4_gap2 {N : ℕ} (X Y : nMix2LambdaPi N)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2) :
    (Chromosome.prime^[1] X.1.1).rank + 2 ≤ (Chromosome.prime^[1] Y.1.1).rank := by
  have hmemX : Chromosome.prime^[1] X.1.1 ∈ Mix (Pi, 2 • Lambda) := by
    have h := Variety.prime_mem_Mix_2Lambda_Pi_iterate X.1.2 1
    rwa [if_neg (by decide)] at h
  have hmemY : Chromosome.prime^[1] Y.1.1 ∈ Mix (Pi, 2 • Lambda) := by
    have h := Variety.prime_mem_Mix_2Lambda_Pi_iterate Y.1.2 1
    rwa [if_neg (by decide)] at h
  obtain ⟨nx, hnx⟩ := Mix2LambdaSection17.signature_Mix_Pi_2Lambda_isNat hmemX
  obtain ⟨ny, hny⟩ := Mix2LambdaSection17.signature_Mix_Pi_2Lambda_isNat hmemY
  have hnx1 : (signature (Chromosome.prime^[1] X.1.1)).1 = (nx.1 : ℚ) := by rw [hnx]
  have hnx2 : (signature (Chromosome.prime^[1] X.1.1)).2 = (nx.2 : ℚ) := by rw [hnx]
  have hny1 : (signature (Chromosome.prime^[1] Y.1.1)).1 = (ny.1 : ℚ) := by rw [hny]
  have hny2 : (signature (Chromosome.prime^[1] Y.1.1)).2 = (ny.2 : ℚ) := by rw [hny]
  rw [hnx1, hnx2, hny1, hny2] at hseed1
  have hg1 : nx.1 < ny.1 := by exact_mod_cast hseed1.1
  have hg2 : nx.2 < ny.2 := by exact_mod_cast hseed1.2
  have hrx : (Chromosome.prime^[1] X.1.1).rank = nx.1 + nx.2 := by
    have h := signature_sum_eq_rank (X := Chromosome.prime^[1] X.1.1)
    rw [hnx1, hnx2] at h; exact_mod_cast h.symm
  have hry : (Chromosome.prime^[1] Y.1.1).rank = ny.1 + ny.2 := by
    have h := signature_sum_eq_rank (X := Chromosome.prime^[1] Y.1.1)
    rw [hny1, hny2] at h; exact_mod_cast h.symm
  omega

lemma case4_Ydrop_fst_strong_even
    {N i : ℕ} (X Y : nMix2LambdaPi N)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hi : Even i) :
    (Sigma.sigma Y.1.1 i).1 - (Sigma.sigma Y.1.1 (i + 2)).1 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
  have hcond7 := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi Y.1.2 i
  rw [if_pos hi] at hcond7
  have hdrop := rank_drop_le Y.1.2 i
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
      (N : ℚ) := by
    simpa [Sigma.sigma, X.2] using (@signature_sum_eq_rank (Chromosome.prime^[0] X.1.1))
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
      (N : ℚ) := by
    simpa [Sigma.sigma, Y.2] using (@signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1))
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    exact_mod_cast case4_gap2 X Y hseed1
  linarith

lemma case4_Ydrop_snd_strong_even
    {N i : ℕ} (X Y : nMix2LambdaPi N)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    (hi : Even i) :
    (Sigma.sigma Y.1.1 i).2 - (Sigma.sigma Y.1.1 (i + 2)).2 ≤
      (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 -
        ((Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2) - 2 := by
  have hcond6 := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi Y.1.2 i
  rw [if_pos hi] at hcond6
  have hdrop := rank_drop_le Y.1.2 i
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
      (N : ℚ) := by
    simpa [Sigma.sigma, X.2] using (@signature_sum_eq_rank (Chromosome.prime^[0] X.1.1))
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 =
      (N : ℚ) := by
    simpa [Sigma.sigma, Y.2] using (@signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1))
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by
    exact_mod_cast case4_gap2 X Y hseed1
  linarith

/-- Level-0 signature agreement: `X < Y` of equal rank agree at level 0. -/
lemma sigma_zero_eq {N : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1) :
    Sigma.sigma X.1.1 0 = Sigma.sigma Y.1.1 0 := by
  have hle := le_iff_dominates.mp hXY.le 0
  have hsum : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 =
      (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 := by
    have hx : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
      simpa [Sigma.sigma, X.2] using @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
    have hy : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
      simpa [Sigma.sigma, Y.2] using @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
    rw [hx, hy]
  have h1 : (Sigma.sigma X.1.1 0).1 ≤ (Sigma.sigma Y.1.1 0).1 := by
    simpa [Sigma.sigma] using hle.1
  have h2 : (Sigma.sigma X.1.1 0).2 ≤ (Sigma.sigma Y.1.1 0).2 := by
    simpa [Sigma.sigma] using hle.2
  exact Prod.ext (le_antisymm h1 (by linarith)) (le_antisymm h2 (by linarith))

/-- §17 Case 4 level-2 seed (first component).  With a rank-one minimal gene `gm`
of multiplicity one, every other gene of rank `≥ k`, and a both-component strict
level-1 gap, the first component is strict at level 2. -/
lemma case4_seed_fst {N k : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    (Sigma.sigma X.1.1 2).1 < (Sigma.sigma Y.1.1 2).1 := by
  have hgap2 := case4_gap2 X Y hseed1
  have hcond7 := Mix2LambdaSection17.cond_15_7_Mix_2Lambda_Pi Y.1.2 0
  rw [if_pos (by decide : Even 0)] at hcond7
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, X.2] using @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, Y.2] using @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by exact_mod_cast hgap2
  have hXdrop := KEY_X_fst_ge X hgm1 h2nd (i := 0) (by omega)
  have h0fst : (Sigma.sigma X.1.1 0).1 = (Sigma.sigma Y.1.1 0).1 :=
    congrArg Prod.fst (sigma_zero_eq X Y hXY)
  simp only [Sigma.sigma, Nat.zero_add] at hcond7 hrX0 hrY0 hrX1 hrY1 hXdrop h0fst ⊢
  linarith

/-- §17 Case 4 level-2 seed (second component). -/
lemma case4_seed_snd {N k : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    (Sigma.sigma X.1.1 2).2 < (Sigma.sigma Y.1.1 2).2 := by
  have hgap2 := case4_gap2 X Y hseed1
  have hcond6 := Mix2LambdaSection17.cond_15_6_Mix_2Lambda_Pi Y.1.2 0
  rw [if_pos (by decide : Even 0)] at hcond6
  have hrX0 : (Sigma.sigma X.1.1 0).1 + (Sigma.sigma X.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, X.2] using @signature_sum_eq_rank (Chromosome.prime^[0] X.1.1)
  have hrY0 : (Sigma.sigma Y.1.1 0).1 + (Sigma.sigma Y.1.1 0).2 = (N : ℚ) := by
    simpa [Sigma.sigma, Y.2] using @signature_sum_eq_rank (Chromosome.prime^[0] Y.1.1)
  have hrX1 : (Sigma.sigma X.1.1 1).1 + (Sigma.sigma X.1.1 1).2 =
      ((Chromosome.prime^[1] X.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hrY1 : (Sigma.sigma Y.1.1 1).1 + (Sigma.sigma Y.1.1 1).2 =
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := @signature_sum_eq_rank _
  have hgapQ : ((Chromosome.prime^[1] X.1.1).rank : ℚ) + 2 ≤
      ((Chromosome.prime^[1] Y.1.1).rank : ℚ) := by exact_mod_cast hgap2
  have hXdrop := KEY_X_snd_ge X hgm1 h2nd (i := 0) (by omega)
  have h0snd : (Sigma.sigma X.1.1 0).2 = (Sigma.sigma Y.1.1 0).2 :=
    congrArg Prod.snd (sigma_zero_eq X Y hXY)
  simp only [Sigma.sigma, Nat.zero_add] at hcond6 hrX0 hrY0 hrX1 hrY1 hXdrop h0snd ⊢
  linarith

/-- §17 Case 4 even-window first-component propagation: strict on every even
level from `2` up to the second-gene rank `k`. -/
lemma case4_window_fst {N k : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    ∀ t : ℕ, 2 + 2 * t ≤ k →
      (Sigma.sigma X.1.1 (2 + 2 * t)).1 < (Sigma.sigma Y.1.1 (2 + 2 * t)).1 := by
  intro t ht
  have hseed := case4_seed_fst X Y hXY hr1 hseed1 hgm1 h2nd hk
  exact window_even_fst_lt X Y hr1 hgm1 h2nd 2 t (by decide) ht hseed t (le_refl t)

/-- §17 Case 4 even-window second-component propagation. -/
lemma case4_window_snd {N k : ℕ} (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (hr1 : (Chromosome.prime^[1] X.1.1).rank < (Chromosome.prime^[1] Y.1.1).rank)
    (hseed1 :
      (signature (Chromosome.prime^[1] X.1.1)).1 <
          (signature (Chromosome.prime^[1] Y.1.1)).1 ∧
        (signature (Chromosome.prime^[1] X.1.1)).2 <
          (signature (Chromosome.prime^[1] Y.1.1)).2)
    {gm : Gene} (hgm1 : X.1.1 gm = 1)
    (h2nd : ∀ g ∈ (X.1.1 - Finsupp.single gm 1).support, k ≤ g.rank)
    (hk : 2 ≤ k) :
    ∀ t : ℕ, 2 + 2 * t ≤ k →
      (Sigma.sigma X.1.1 (2 + 2 * t)).2 < (Sigma.sigma Y.1.1 (2 + 2 * t)).2 := by
  intro t ht
  have hseed := case4_seed_snd X Y hXY hr1 hseed1 hgm1 h2nd hk
  exact window_even_snd_lt X Y hr1 hgm1 h2nd 2 t (by decide) ht hseed t (le_refl t)

end Mix2LambdaPi
