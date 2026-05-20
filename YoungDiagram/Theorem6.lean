import YoungDiagram.Sigma
import YoungDiagram.Lifting.Pi

set_option maxHeartbeats 400000

open Variety hiding prime prime_def
open Chromosome

abbrev nPi (n : ℕ) := {X : Pi // X.1.rank = n}

/-! ## Case 1: X and Y share a gene -/

/-- Remove a shared gene from both X and Y, apply IH, then reattach. -/
private lemma exists_mutation_le_shared_gene (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  obtain ⟨g, hgX, hgY⟩ := hcommon
  have hg_pol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g
      (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgX))
  have hg1_Pi : Finsupp.single g 1 ∈ Pi :=
    mem_Pi_iff.mpr <| (IsPolarized_single Nat.one_ne_zero).2 hg_pol
  let X'v : Chromosome := X.1.val - Finsupp.single g 1
  let Y'v : Chromosome := Y.1.val - Finsupp.single g 1
  have hX'Pi : X'v ∈ Pi := sub_mem_Pi _ X.1.2
  have hY'Pi : Y'v ∈ Pi := sub_mem_Pi _ Y.1.2
  have hlt' : (⟨X'v, hX'Pi⟩ : Pi) < ⟨Y'v, hY'Pi⟩ :=
    sub_single_lt_sub_single hgX hgY hXY
  have hX'rank : X'v.rank = m + 2 - g.rank := by
    rw [rank_sub_single hgX, X.2]
  have hY'rank : Y'v.rank = m + 2 - g.rank := by
    rw [rank_sub_single hgY, Y.2]
  obtain ⟨Z', hmut', hle'⟩ :=
    ih (m + 2 - g.rank) (Nat.sub_lt (by omega) g.rank_pos)
      ⟨⟨X'v, hX'Pi⟩, hX'rank⟩ ⟨⟨Y'v, hY'Pi⟩, hY'rank⟩ hlt'
  refine ⟨⟨Z'.val + Finsupp.single g 1,
      mem_Pi_iff.mpr (IsPolarized_iff_add.mpr
        ⟨mem_Pi_iff.mp Z'.2, mem_Pi_iff.mp hg1_Pi⟩)⟩, ?_, ?_⟩
  · convert Pi.Step.add_right_pi ⟨Finsupp.single g 1, hg1_Pi⟩ hmut' using 1
    exact Subtype.ext (sub_single_add_single_eq hgX).symm
  · change Z'.val + Finsupp.single g 1 ≤ Y.1.val
    rw [← sub_single_add_single_eq hgY, le_iff_dominates]
    intro k
    have h := (le_iff_dominates.mp hle') k
    simp only [iterate_map_add, map_add, add_le_add_iff_right]
    exact h

/-! ## Sub-case 2a: disjoint supports, some sigma column agrees -/

/-- Drop to prime^[k] level where sigma agrees, apply IH, then lift back. -/
private lemma exists_mutation_le_disjoint_sigma_eq (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X : Pi) (Y : nPi (m + 2))
    (hXY : X < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.val g ∧ 0 < Y.1.val g)
    (hsigeq : ∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X k = Sigma.sigma Y.1 k) :
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y.1 := by
  push Not at hcommon
  obtain ⟨k, hkpos, hYkne, hk⟩ := hsigeq
  have hle_k : prime^[k] X.val ≤ prime^[k] Y.1.val := by
    intro j; simp_rw [← Function.iterate_add_apply]; exact le_iff_dominates.mp hXY.le (j + k)
  have hdisj_k : ∀ (g' : Gene), 0 < (prime^[k] X.val) g' →
      (prime^[k] Y.1.val) g' = 0 := by
    intro g' hg'
    rw [prime_iterate_coeff k X.val g'] at hg'
    rw [prime_iterate_coeff k Y.1.val g']
    exact Nat.eq_zero_of_le_zero (hcommon ⟨g'.rank + k, g'.type, by linarith [g'.rank_pos]⟩ hg')
  let Xk : Pi := ⟨prime^[k] X.val, prime_mem_Pi_iterate X.2⟩
  let Yk : Pi := ⟨prime^[k] Y.1.val, prime_mem_Pi_iterate Y.1.2⟩
  have hXk_Yk_rank : Xk.val.rank = Yk.val.rank := by
    have h := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) hk
    simp only [Sigma.sigma, signature_sum_eq_rank] at h
    exact_mod_cast h
  have hXk_rank_lt : Xk.val.rank < m + 2 := by
    rw [hXk_Yk_rank, show m + 2 = Y.1.val.rank from Y.2.symm]
    exact prime_iterate_rank_lt_of_ne_zero hkpos hYkne
  have hlt_k : Xk < Yk := by
    change Yk.val.Dominates Xk.val ∧ ¬Xk.val.Dominates Yk.val
    refine ⟨le_iff_dominates.mp hle_k, fun hcontra => ?_⟩
    have hXkYk_eq : Xk.val = Yk.val :=
      pi_chromosome_antisymm Xk.2 Yk.2 hle_k (le_iff_dominates.mpr hcontra)
    obtain ⟨g', hg'⟩ : ∃ g', 0 < Yk.val g' := by
      obtain ⟨g', hg'mem⟩ := Finsupp.support_nonempty_iff.mpr hYkne
      exact ⟨g', Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'mem)⟩
    have hXkg' : 0 < Xk.val g' := by rwa [hXkYk_eq]
    have hYkg'zero := hdisj_k g' hXkg'; simp only [Yk] at hg'; omega
  obtain ⟨U, hU_step, hU_le⟩ : ∃ U : Pi, Pi.Step Xk U ∧ U ≤ Yk :=
    ih Xk.val.rank hXk_rank_lt ⟨Xk, rfl⟩ ⟨Yk, hXk_Yk_rank.symm⟩ hlt_k
  obtain ⟨Z, hZ, hZ_step, hZ_prime, hZ_sig⟩ :=
    Pi.mutation_lifting X.2 U.2 hU_step
  refine ⟨⟨Z, hZ⟩, hZ_step, ?_⟩
  change Z ≤ Y.1.val; rw [le_iff_dominates]
  intro j
  by_cases hjk : j ≤ k
  · rw [← hZ_sig j hjk]; exact le_iff_dominates.mp hXY.le j
  · push Not at hjk
    conv_lhs => rw [show j = (j - k) + k from (Nat.sub_add_cancel hjk.le).symm,
        Function.iterate_add_apply, hZ_prime]
    calc signature (prime^[j - k] U.val)
        ≤ signature (prime^[j - k] Yk.val) := le_iff_dominates.mp hU_le (j - k)
      _ = signature (prime^[j] Y.1.val) := by
          simp only [Yk, ← Function.iterate_add_apply, Nat.sub_add_cancel hjk.le]

/-! ## Sub-case 2b: disjoint supports, X contains g⁺(k) + g⁻(k) -/

lemma prime_iterate_no_gene_of_rank {Y : Chromosome} {r : ℕ}
    (hY_no_gene : ∀ g : Gene, g.rank = r → Y g = 0)
    (j : ℕ) (hj : j ≤ r - 1) (h : Gene) (hh : h.rank = r - j) :
    (prime^[j] Y) h = 0 := by
  induction j generalizing h with
  | zero => exact hY_no_gene h (by omega)
  | succ j ihj =>
    simp only [Function.iterate_succ', Function.comp,
      prime_def, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    simp only [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro g hg
    have hg_ne : (prime^[j] Y) g ≠ 0 := Finsupp.mem_support_iff.mp hg
    by_cases hrk : g.rank - 1 = h.rank
    · exfalso
      have _ := g.rank_pos
      exact hg_ne (ihj (by omega) g (by omega))
    · simp only [Nat.mul_eq_zero]
      right
      simp only [primeGene, Gene.ofRank_def]
      split_ifs with h0
      · rfl
      · rw [Finsupp.single_apply, if_neg]
        intro heq
        exact hrk (congrArg Gene.rank heq)

lemma prime_ne_zero_of_Y_no_gene {Y : Chromosome} {r : ℕ} (hr : 1 ≤ r)
    (hY_no_gene : ∀ g : Gene, g.rank = r → Y g = 0)
    (hYr_minus_one : prime^[r - 1] Y ≠ 0) : prime^[r] Y ≠ 0 := by
  rw [show r = 1 + (r - 1) from by omega,
      Function.iterate_add_apply, Function.iterate_one]
  apply prime_ne_zero_of_rank_ge_two hYr_minus_one
  intro h hmem
  rw [Finsupp.mem_support_iff] at hmem
  by_contra! hlt
  have hh1 : h.rank = 1 := le_antisymm (by omega) h.rank_pos
  exact hmem (prime_iterate_no_gene_of_rank hY_no_gene (r - 1) (by omega) h (by omega))

lemma Y_no_gene_of_rank {X Y : Chromosome} (hYPi : Y ∈ Pi)
    (hcommon : ∀ g, 0 < X g → Y g ≤ 0)
    (gpos gneg : Gene) (hrank : gpos.rank = gneg.rank)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hXgpos : 0 < X gpos) (hXgneg : 0 < X gneg)
    (g : Gene) (hgr : g.rank = gpos.rank) : Y g = 0 := by
  by_contra hne
  have hg_pol : g.type ≠ .NonPolarized :=
    IsPolarized_def'.mp (mem_Pi_iff.mp hYPi) g (Finsupp.mem_support_iff.mpr hne)
  cases ht : g.type with
  | NonPolarized => exact hg_pol ht
  | Positive =>
    have hgeq : g = gpos := Gene.ext hgr (ht.trans hgpos.symm)
    subst hgeq; have h := hcommon g hXgpos; omega
  | Negative =>
    have hgeq : g = gneg := Gene.ext (hgr.trans hrank) (ht.trans hgneg.symm)
    subst hgeq; have h := hcommon g hXgneg; omega

lemma one_le_signature_fst_of_contains_positive {X : Chromosome} {gpos : Gene}
    (hgpos : gpos.type = .Positive) (hXgpos : 0 < X gpos) :
    1 ≤ (signature (prime^[gpos.rank - 1] X)).1 := by
  let r := gpos.rank
  have hr : 1 ≤ r := gpos.rank_pos
  have hgpos_single : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rw [hgpos] at h; exact h
  have hprime_gpos : prime^[r - 1] (Finsupp.single gpos 1 : Chromosome) =
      Gene.ofRank 1 .Positive := by
    rw [← hgpos_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
  have hXeq : X = Finsupp.single gpos 1 + (X - Finsupp.single gpos 1) := by
    rw [add_comm, sub_single_add_single_eq hXgpos]
  calc (1 : ℚ)
      = (signature (Gene.ofRank 1 .Positive : Chromosome)).1 := by
        simp [signature_ofRank_one_positive]
    _ = (signature (prime^[r - 1] (Finsupp.single gpos 1 : Chromosome))).1 := by
        rw [hprime_gpos]
    _ ≤ (signature (prime^[r - 1] X)).1 := by
        conv_rhs => rw [hXeq]
        rw [iterate_map_add, map_add]
        exact le_add_of_nonneg_right (signature_nonneg _).1

lemma X_eq_X1_add_rest {X : Chromosome} {gpos gneg : Gene}
    (hXgpos : 0 < X gpos) (hXgneg : 0 < X gneg) (hne : gpos ≠ gneg) :
    Finsupp.single gpos 1 + Finsupp.single gneg 1 +
      (X - Finsupp.single gpos 1 - Finsupp.single gneg 1) = X := by
  ext g'
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases h1 : gpos = g'
  · subst h1; have h2 : gneg ≠ gpos := hne.symm; simp [if_neg h2]; omega
  · by_cases h2 : gneg = g'
    · subst h2; simp [if_neg hne]; omega
    · simp [if_neg h1, if_neg h2]

/-- Construct a type-1 mutation directly from a positive-negative gene pair. -/
private lemma exists_mutation_le_disjoint_pair
    (X Y : Pi)
    (hXY : X < Y)
    (hcommon : ¬∃ g : Gene, 0 < X.val g ∧ 0 < Y.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.val ≠ 0 ∧
      Sigma.sigma X k = Sigma.sigma Y k)
    (hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.val g ∧ 0 < X.val h) :
    ∃ Z : Pi, Pi.Step X Z ∧ Z ≤ Y := by
  push Not at hcommon hsigeq
  obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXgpos, hXgneg⟩ := hXpn
  let r := gpos.rank
  have hr : 1 ≤ r := gpos.rank_pos
  have hY_no_gene : ∀ (g : Gene), g.rank = r → Y.val g = 0 :=
    Y_no_gene_of_rank Y.2 hcommon gpos gneg hrank hgpos hgneg hXgpos hXgneg
  have h1a : 1 ≤ (signature (prime^[r - 1] X.val)).1 :=
    one_le_signature_fst_of_contains_positive hgpos hXgpos
  have h1c : prime^[r - 1] Y.val ≠ 0 := by
    intro heq
    have h1b : 1 ≤ (signature (prime^[r - 1] Y.val)).1 :=
      le_trans h1a ((le_iff_dominates.mp hXY.le (r - 1)).1)
    have : (signature (prime^[r - 1] Y.val)).1 = 0 := by simp [heq]
    linarith
  have hYr : prime^[r] Y.val ≠ 0 := prime_ne_zero_of_Y_no_gene hr hY_no_gene h1c
  have hsig_ne : Sigma.sigma X r ≠ Sigma.sigma Y r :=
    hsigeq r gpos.rank_pos hYr
  have hle_r : Sigma.sigma X r ≤ Sigma.sigma Y r := le_iff_dominates.mp hXY.le r
  have hsig_lt : (Sigma.sigma X r).1 < (Sigma.sigma Y r).1 ∨
                 (Sigma.sigma X r).2 < (Sigma.sigma Y r).2 := by
    rcases lt_or_eq_of_le hle_r.1 with h1 | h1
    · exact Or.inl h1
    · rcases lt_or_eq_of_le hle_r.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd (Prod.ext h1 h2) hsig_ne
  let restval := X.val - Finsupp.single gpos 1 - Finsupp.single gneg 1
  have hne : gpos ≠ gneg := fun h =>
    absurd (congrArg Gene.type h) (by rw [hgpos, hgneg]; decide)
  have hgpos_eq : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) := by
    rw [← hgpos]; exact Gene.ofRank_eq_gene
  have hgneg_eq : Gene.ofRank r .Negative = (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rw [hgneg] at h; rwa [← hrank] at h
  have rest_mem : restval ∈ Pi := by
    rw [mem_Pi_iff, IsPolarized_def']
    intro g hg
    apply IsPolarized_def'.mp (mem_Pi_iff.mp X.2) g
    rw [Finsupp.mem_support_iff] at hg ⊢
    intro hX0; apply hg
    simp only [restval, Finsupp.tsub_apply, Finsupp.single_apply, hX0]; omega
  rcases hsig_lt with h_pos | h_neg
  · let ε : GeneType := .Positive
    have hε : ε ≠ .NonPolarized := by decide
    let X1 : Pi := Pi.X1 hε (le_refl r) hr
    let Y1 : Pi := Pi.Y1 hε (le_refl r) hr
    let rest_pi : Pi := ⟨restval, rest_mem⟩
    have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
      rw [Pi.X1_eq, GeneType.neg_positive, hgpos_eq, hgneg_eq]
    have hX_eq : X1.val + restval = X.val := by
      rw [hX1_val]; exact X_eq_X1_add_rest hXgpos hXgneg hne
    let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
    have hprim : Pi.Primitive X1 Y1 := Pi.Primitive.type1 ε hε (le_refl r) hr
    have hstep_raw : Pi.Step (X1 + rest_pi) (Y1 + rest_pi) := Pi.Step.mk X1 Y1 rest_pi hprim
    have hX_sub : X1 + rest_pi = X := Subtype.ext hX_eq
    refine ⟨Z, hX_sub ▸ hstep_raw, ?_⟩
    change Y1.val + restval ≤ Y.val
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp : signature (prime^[j] X.val) =
        signature (prime^[j] X1.val) + signature (prime^[j] restval) := by
      rw [← hX_eq, iterate_map_add, map_add]
    have hXYj : signature (prime^[j] X.val) ≤ signature (prime^[j] Y.val) :=
      le_iff_dominates.mp hXY.le j
    rcases lt_trichotomy j r with hjr | rfl | hjr
    · have hY1X1 : signature (prime^[j] Y1.val) = signature (prime^[j] X1.val) := by
        rw [Pi.Y1_eq, Pi.X1_eq]
        have key := mutation_type1_iterate_signature_eq hε le_rfl le_rfl j (r - 1) (by omega)
        simp only [show 1 + (r - 1) = r from by omega] at key
        exact key.symm
      rw [hY1X1, ← hdecomp]; exact hXYj
    · have hX1r : signature (prime^[r] X1.val) = 0 := by
        rw [Pi.X1_eq]
        simp only [iterate_map_add, prime_iterate_ofRank,
                   Nat.sub_self, Gene.ofRank_zero, map_zero, add_zero]
      have hY1r : signature (prime^[r] Y1.val) = (1, 0) := by
        rw [Pi.Y1_eq]
        simp only [iterate_map_add, prime_iterate_ofRank,
                   show r - 1 - r = 0 from by omega,
                   show r + 1 - r = 1 from by omega,
                   Gene.ofRank_zero, zero_add]
        exact signature_ofRank_one_positive
      have hrest_eq : signature (prime^[r] restval) = signature (prime^[r] X.val) := by
        rw [hdecomp, hX1r, zero_add]
      rw [hY1r, hrest_eq]
      simp only [Sigma.sigma] at h_pos hle_r
      obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.2 (k := r))
      obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.2 (k := r))
      constructor
      · simp only [Prod.fst_add]
        rw [hnX, hnY] at h_pos ⊢
        have hnXY : nX.1 < nY.1 := Nat.cast_lt.mp h_pos
        have hfst : (nX.1 : ℚ) + 1 ≤ nY.1 := by exact_mod_cast Nat.add_one_le_iff.mpr hnXY
        linarith
      · simp only [Prod.snd_add, zero_add]; exact hle_r.2
    · have hX1j : signature (prime^[j] X1.val) = 0 := by
        rw [Pi.X1_eq]
        simp only [iterate_map_add, prime_iterate_ofRank,
                   show r - j = 0 from by omega,
                   Gene.ofRank_zero, map_zero, add_zero]
      have hY1j : signature (prime^[j] Y1.val) = 0 := by
        rw [Pi.Y1_eq]
        simp only [iterate_map_add, prime_iterate_ofRank,
                   show r - 1 - j = 0 from by omega,
                   show r + 1 - j = 0 from by omega,
                   Gene.ofRank_zero, map_zero, add_zero]
      have hrestj : signature (prime^[j] restval) = signature (prime^[j] X.val) := by
        rw [hdecomp, hX1j, zero_add]
      rw [hY1j, zero_add, hrestj]; exact hXYj
  · let ε : GeneType := .Negative
    have hε : ε ≠ .NonPolarized := by decide
    let X1 : Pi := Pi.X1 hε (le_refl r) hr
    let Y1 : Pi := Pi.Y1 hε (le_refl r) hr
    let rest_pi : Pi := ⟨restval, rest_mem⟩
    have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
      rw [Pi.X1_eq, GeneType.neg_negative, hgneg_eq, hgpos_eq, add_comm]
    have hX_eq : X1.val + restval = X.val := by
      rw [hX1_val]; exact X_eq_X1_add_rest hXgpos hXgneg hne
    let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
    have hprim : Pi.Primitive X1 Y1 := Pi.Primitive.type1 ε hε (le_refl r) hr
    have hstep_raw : Pi.Step (X1 + rest_pi) (Y1 + rest_pi) := Pi.Step.mk X1 Y1 rest_pi hprim
    have hX_sub : X1 + rest_pi = X := Subtype.ext hX_eq
    refine ⟨Z, hX_sub ▸ hstep_raw, ?_⟩
    change Y1.val + restval ≤ Y.val
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp : signature (prime^[j] X.val) =
        signature (prime^[j] X1.val) + signature (prime^[j] restval) := by
      rw [← hX_eq, iterate_map_add, map_add]
    have hXYj : signature (prime^[j] X.val) ≤ signature (prime^[j] Y.val) :=
      le_iff_dominates.mp hXY.le j
    rcases lt_trichotomy j r with hjr | rfl | hjr
    · have hY1X1 : signature (prime^[j] Y1.val) = signature (prime^[j] X1.val) := by
        rw [Pi.Y1_eq, Pi.X1_eq]
        have key := mutation_type1_iterate_signature_eq hε le_rfl le_rfl j (r - 1) (by omega)
        simp only [show 1 + (r - 1) = r from by omega] at key
        exact key.symm
      rw [hY1X1, ← hdecomp]; exact hXYj
    · have hX1r : signature (prime^[r] X1.val) = 0 := by
        rw [Pi.X1_eq]
        simp only [iterate_map_add, prime_iterate_ofRank,
                   Nat.sub_self, Gene.ofRank_zero, map_zero, zero_add]
      have hY1r : signature (prime^[r] Y1.val) = (0, 1) := by
        rw [Pi.Y1_eq]
        simp only [iterate_map_add, prime_iterate_ofRank,
                   show r - 1 - r = 0 from by omega,
                   show r + 1 - r = 1 from by omega,
                   Gene.ofRank_zero, zero_add]
        exact signature_ofRank_one_negative
      have hrest_eq : signature (prime^[r] restval) = signature (prime^[r] X.val) := by
        rw [hdecomp, hX1r, zero_add]
      rw [hY1r, hrest_eq]
      simp only [Sigma.sigma] at h_neg hle_r
      obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.2 (k := r))
      obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.2 (k := r))
      constructor
      · simp only [Prod.fst_add, zero_add]; exact hle_r.1
      · simp only [Prod.snd_add]
        rw [hnX, hnY] at h_neg ⊢
        have hnXY : nX.2 < nY.2 := Nat.cast_lt.mp h_neg
        have hsnd : (nX.2 : ℚ) + 1 ≤ nY.2 := by exact_mod_cast Nat.add_one_le_iff.mpr hnXY
        linarith
    · have hX1j : signature (prime^[j] X1.val) = 0 := by
        rw [Pi.X1_eq]
        simp only [iterate_map_add, prime_iterate_ofRank,
                   show r - j = 0 from by omega,
                   Gene.ofRank_zero, map_zero, add_zero]
      have hY1j : signature (prime^[j] Y1.val) = 0 := by
        rw [Pi.Y1_eq]
        simp only [iterate_map_add, prime_iterate_ofRank,
                   show r - 1 - j = 0 from by omega,
                   show r + 1 - j = 0 from by omega,
                   Gene.ofRank_zero, map_zero, add_zero]
      have hrestj : signature (prime^[j] restval) = signature (prime^[j] X.val) := by
        rw [hdecomp, hX1j, zero_add]
      rw [hY1j, zero_add, hrestj]; exact hXYj

/-- If `X` and `Y` have the same rank and `X.1 ≤ Y.1` in `Pi`, then their sigma sequences
agree in the first component at level 0 (i.e. `a₀ = c₀`).

The key is that `signature_sum_eq_rank` gives `a₀ + b₀ = rank = c₀ + d₀`, and since
`a₀ ≤ c₀` and `b₀ ≤ d₀` from sigma-dominance, equality is forced by linarith. -/
private lemma sigma_zero_fst_eq {n : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1) :
    (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 := by
  simp only [Sigma.sigma, Function.iterate_zero, id]
  have hsig_le := (le_iff_dominates.mp hXY) 0
  simp only [Function.iterate_zero, id] at hsig_le
  obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
  have hXsum := @signature_sum_eq_rank X.1.val
  have hYsum := @signature_sum_eq_rank Y.1.val
  have hXrank : (X.1.val.rank : ℚ) = n := by exact_mod_cast X.2
  have hYrank : (Y.1.val.rank : ℚ) = n := by exact_mod_cast Y.2
  linarith

private lemma sigma_zero_snd_eq {n : ℕ} (X Y : nPi n) (hXY : X.1 ≤ Y.1) :
    (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 := by
  simp only [Sigma.sigma, Function.iterate_zero, id]
  have hsig_le := (le_iff_dominates.mp hXY) 0
  simp only [Function.iterate_zero, id] at hsig_le
  obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
  have hXsum := @signature_sum_eq_rank X.1.val
  have hYsum := @signature_sum_eq_rank Y.1.val
  have hXrank : (X.1.val.rank : ℚ) = n := by exact_mod_cast X.2
  have hYrank : (Y.1.val.rank : ℚ) = n := by exact_mod_cast Y.2
  linarith

/-- **X-side equalities** (Step 5, Case 1 of §15, Djoković 1982).

For `j < g₂.rank = k`, the alternating sigma-differences of `X` are all equal to `a₀ − a₁`:
the `.1`-difference at even `j` and `.2`-difference at odd `j` equal
`(Sigma.sigma X 0).1 − (Sigma.sigma X 1).1`.

The proof uses the column-count formula: `aᵢ₋₁ − aᵢ` counts g₊-genes of rank ≥ i when i is odd,
and g₋-genes of rank ≥ i when i is even. Minimality of k (among g₊-ranks) forces the g₊-count
to equal P on the whole range [1, k], giving the constant chain. -/
private lemma x_side_equalities
    {X : Pi}
    (_ : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.val g ∧ 0 < X.val h)
    {g₂ : Gene}
    (_ : Gene.ofRankAlt g₂.rank GeneType.Positive = Finsupp.single g₂ 1)
    (_ : 0 < X.val g₂)
    (hg₂min : ∀ g' : Gene,
      Gene.ofRankAlt g'.rank GeneType.Positive = Finsupp.single g' 1 →
      0 < X.val g' → g₂.rank ≤ g'.rank)
    {j : ℕ} (hj : j < g₂.rank) :
    (if Even j then
      (Sigma.sigma X j).1 - (Sigma.sigma X (j + 1)).1
    else
      (Sigma.sigma X j).2 - (Sigma.sigma X (j + 1)).2) =
    (Sigma.sigma X 0).1 - (Sigma.sigma X 1).1 := by
  -- Column-count formula: the alternating sigma-diff at i equals the total multiplicity of
  -- g₊-subscript genes in X with rank > i.
  -- (For even i the `.1` diff counts g₊-genes contributing to column i+1; for odd i the `.2` diff.)
  have hcol : ∀ i : ℕ, (if Even i then
      (Sigma.sigma X i).1 - (Sigma.sigma X (i + 1)).1
    else
      (Sigma.sigma X i).2 - (Sigma.sigma X (i + 1)).2) =
    ∑ g ∈ X.val.support.filter (fun g =>
        i < g.rank ∧ g.type = Int.negOnePow (g.rank - 1) • GeneType.Positive),
      (X.val g : ℚ) := by
    intro i
    split_ifs
    · rw [Sigma.sigma_fst_diff X.val i X.2]
      exact Sigma.prime_iterate_sum_pos_eq X.val i ‹Even i›
    · rw [Sigma.sigma_snd_diff X.val i X.2]
      exact Sigma.prime_iterate_sum_neg_eq X.val i ‹¬Even i›
  rw [hcol j]
  -- At i = 0 (even), rank > 0 holds for all genes (rank_pos), so the formula gives the
  -- total g₊-count P = Σ_{g₊-genes in X} X.val g.
  have hRHS : (Sigma.sigma X 0).1 - (Sigma.sigma X 1).1 =
      ∑ g ∈ X.val.support.filter (fun g =>
        g.type = Int.negOnePow (g.rank - 1) • GeneType.Positive), (X.val g : ℚ) := by
    have h0 := hcol 0
    -- Reduce the `if Even 0 then A(0+1) else B(0+1)` form in h0 to `A(1)` by proving heq
    -- against an explicitly-written if-expression (avoiding the pattern-matching failure that
    -- occurs when if_pos is applied directly to h0 whose `Even 0` may be stored unfolded).
    have heq : (if Even (0 : ℕ) then (Sigma.sigma X 0).1 - (Sigma.sigma X (0 + 1)).1
                else (Sigma.sigma X 0).2 - (Sigma.sigma X (0 + 1)).2) =
               (Sigma.sigma X 0).1 - (Sigma.sigma X 1).1 := by
      rw [if_pos (by norm_num : Even (0 : ℕ))]
    rw [← heq, h0]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext g; simp only [Finset.mem_filter]
    exact ⟨fun ⟨hs, _, ht⟩ => ⟨hs, ht⟩, fun ⟨hs, ht⟩ => ⟨hs, g.rank_pos, ht⟩⟩
  rw [hRHS]
  -- Constancy: for j < g₂.rank every g₊-gene has rank ≥ g₂.rank > j,
  -- so the condition `j < g.rank` is redundant and the two filter-sums agree.
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext g; simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hsupp, _, htype⟩; exact ⟨hsupp, htype⟩
  · rintro ⟨hsupp, htype⟩
    refine ⟨hsupp, ?_, htype⟩
    have hg2le : g₂.rank ≤ g.rank :=
      hg₂min g
        (by rw [Gene.ofRankAlt_eq_gene g.rank_pos]; congr 1; exact Gene.ext rfl htype.symm)
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hsupp))
    omega

private lemma prime_iterate_actual_type_sum_eq (X : Chromosome) (k : ℕ) (ε : GeneType) :
    (prime^[k] X).sum (fun g m ↦ if g.type = ε then (m : ℚ) else 0) =
    ∑ g ∈ X.support.filter (fun g => k < g.rank ∧ g.type = ε), (X g : ℚ) := by
  simp only [Finsupp.sum]
  conv_lhs => arg 2; ext g; rw [prime_iterate_coeff k X g]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
      (fun g _ => (⟨g.rank + k, g.type, Nat.le_add_right_of_le g.rank_pos⟩ : Gene))
      (fun g' hg' => (⟨g'.rank - k, g'.type, by
        have hlt := (Finset.mem_filter.mp hg').2.1
        omega⟩ : Gene))
      ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg ⊢
    obtain ⟨hgsupp, hgtype⟩ := hg
    refine ⟨by rwa [← prime_iterate_coeff], ?_, ?_⟩
    · have := g.rank_pos; omega
    · exact hgtype
  · intro g' hg'
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hg' ⊢
    obtain ⟨hgsupp', hlt, hgtype'⟩ := hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt hlt
    refine ⟨?_, ?_⟩
    · rw [prime_iterate_coeff]
      simp only [Nat.sub_add_cancel hle]
      exact hgsupp'
    · exact hgtype'
  · intro g _
    exact Gene.ext (Nat.add_sub_cancel g.rank k) rfl
  · intro g' hg'
    have hle : k ≤ g'.rank := Nat.le_of_lt (Finset.mem_filter.mp hg').2.1
    exact Gene.ext (Nat.sub_add_cancel hle) rfl
  · intros
    rfl

private lemma x_actual_negative_prefix_equalities
    {X : Pi} {g₂ : Gene}
    (hg₂_min : ∀ g' : Gene, g'.type = .Negative → 0 < X.val g' → g₂.rank ≤ g'.rank)
    {i : ℕ} (hi : 1 ≤ i) (hi₂ : i ≤ g₂.rank) :
    (Sigma.sigma X.val 0).2 - (Sigma.sigma X.val (i - 1)).2 =
      (Sigma.sigma X.val 1).1 - (Sigma.sigma X.val i).1 := by
  have hcount0 := Sigma.b0_sub_a1_eq_neg_count X.val X.2
  have hcounti := Sigma.b0_sub_a1_eq_neg_count (prime^[i - 1] X.val)
    (Variety.prime_mem_Pi_iterate X.2 (k := i - 1))
  simp only [Sigma.sigma, Function.iterate_zero, id, Function.iterate_one] at hcount0 hcounti
  have hcount :
      (prime^[i - 1] X.val).sum
          (fun g m => if g.type = GeneType.Negative then (m : ℚ) else 0) =
        X.val.sum (fun g m => if g.type = GeneType.Negative then (m : ℚ) else 0) := by
    rw [prime_iterate_actual_type_sum_eq X.val (i - 1) GeneType.Negative]
    rw [Finsupp.sum, ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext g
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hsupp, _, hneg⟩
        exact ⟨hsupp, hneg⟩
      · rintro ⟨hsupp, hneg⟩
        refine ⟨hsupp, ?_ , hneg⟩
        have hpos : 0 < X.val g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hsupp)
        have hg₂_le := hg₂_min g hneg hpos
        omega
    · intro g _
      rfl
  have hprime_i : prime (prime^[i - 1] X.val) = prime^[i] X.val := by
    rw [show i = i - 1 + 1 from by omega]
    exact (Function.iterate_succ_apply' prime (i - 1) X.val).symm
  simp only [Sigma.sigma, Function.iterate_zero, id, Function.iterate_one]
  rw [← hprime_i]
  linarith

private lemma caseA2_strict_fst
    {n : ℕ} (X Y : nPi n) (hXY : X.1 < Y.1)
    {g₂ : Gene}
    (hg₂_min : ∀ g' : Gene, g'.type = .Negative → 0 < X.1.val g' → g₂.rank ≤ g'.rank)
    (hb₀_eq_d₀ : (Sigma.sigma X.1.val 0).2 = (Sigma.sigma Y.1.val 0).2)
    (ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1)
    {i : ℕ} (hi : 1 ≤ i) (hi₂ : i ≤ g₂.rank) :
    (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.1.val i).1 := by
  have hY_chain : (Sigma.sigma Y.1.val 0).2 - (Sigma.sigma Y.1.val (i - 1)).2 ≥
      (Sigma.sigma Y.1.val 1).1 - (Sigma.sigma Y.1.val i).1 :=
    Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 hi
  have hX_eq : (Sigma.sigma X.1.val 0).2 - (Sigma.sigma X.1.val (i - 1)).2 =
      (Sigma.sigma X.1.val 1).1 - (Sigma.sigma X.1.val i).1 := by
    exact x_actual_negative_prefix_equalities hg₂_min hi hi₂
  have hXY_pred : (Sigma.sigma X.1.val (i - 1)).2 ≤
      (Sigma.sigma Y.1.val (i - 1)).2 :=
    (le_iff_dominates.mp hXY.le (i - 1)).2
  linarith

/-! ## (15.10): X has no positive-negative gene pair of equal rank -/
/-- Cases 1–4 of §15.10 (all s orry). -/
private lemma exists_mutation_le_fifteen_ten (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2))
    (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  -- From hsigeq: for k ≥ 1 with Y^(k) ≠ 0, sigma X k ≠ sigma Y k.
  -- Combined with X < Y: (a_k, b_k) ≤ (c_k, d_k), so a_k < c_k or b_k < d_k.
  -- Split: either some k has a_k < c_k, or for all such k a_k = c_k (so b_k < d_k).
  -- From hsigeq: for k ≥ 1 with Y^(k) ≠ 0, sigma X k ≠ sigma Y k.
  -- Split on Case A (a₁ < c₁) vs Case B (a₁ = c₁, so b₁ < d₁).
  by_cases ha : (Sigma.sigma X.1 1).1 < (Sigma.sigma Y.1 1).1
  · -- Case A: a₁ < c₁ (paper §15.10, Cases 1–4).
    -- Let g₁ = g_{ε₁}(m) be the gene of minimal rank m in X (paper §15, p.30).
    have hXne : X.1.val ≠ 0 := by
      intro h; have := X.2; rw [h, rank_def, Finsupp.sum_zero_index] at this; omega
    obtain ⟨g₁, hXg₁, hg₁min⟩ := Finset.exists_min_image X.1.val.support Gene.rank
      (Finsupp.support_nonempty_iff.mpr hXne)
    rw [Finsupp.mem_support_iff] at hXg₁
    have hXg₁pos : 0 < X.1.val g₁ := Nat.pos_of_ne_zero hXg₁

    by_cases hε₁ : g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Negative
    · -- Case 1: ε₁ = − (i.e. g₁ = Gene.ofRankAlt g₁.rank .Negative as a Gene term).
      sorry /-
      have hg₂_exists : ∃ g₂ : Gene, (g₂.type = Int.negOnePow (g₂.rank - 1) • GeneType.Positive) ∧
       0 < X.1.val g₂ := by
        by_contra hno_g₂
        push Not at hno_g₂
        -- hno_g₂ : ∀ g : Gene, g.rank = 1 → g.type = .Positive → X.1.val g = 0
        -- Since no rank-1 Positive gene exists in X, priming once does not decrease a.
        have ha₁_eq_a₀ : (Sigma.sigma X.1 1).1 = (Sigma.sigma X.1 0).1 := by
          simp only [Sigma.sigma, Function.iterate_one, Function.iterate_zero, id]
          rw [signature_prime_fst, signature_fst]
          apply Finsupp.sum_congr
          intro g hg
          congr 1
          -- Goal: (Chromosome.signature (primeGene g)).1 = (Gene.signature g).1
          have hg_in_X : 0 < X.1.val g :=
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
          have hg_pol : g.type ≠ .NonPolarized :=
            IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g hg
          -- Every gene in X has type Int.negOnePow(g.rank-1)•.Negative.
          have hg_neg : g.type = Int.negOnePow (g.rank - 1) • GeneType.Negative := by
            have h_not_pos : g.type ≠ Int.negOnePow (g.rank - 1) • GeneType.Positive :=
              fun heq => by have := hno_g₂ g heq; omega
            simp only [GeneType.negOnePow_smul, GeneType.neg_positive,
              GeneType.neg_negative] at h_not_pos ⊢
            -- After simp: even case gives h_not_pos : g.type ≠ .Positive, goal : g.type = .Negative
            --              odd case gives h_not_pos : g.type ≠ .Negative, goal : g.type = .Positive
            split_ifs with heven
            · simp only [if_pos heven] at h_not_pos
              -- h_not_pos : g.type ≠ GeneType.Positive
              cases ht : g.type with
              | Positive => exact absurd ht h_not_pos
              | Negative => rfl
              | NonPolarized => exact absurd ht hg_pol
            · simp only [if_neg heven] at h_not_pos
              -- h_not_pos : g.type ≠ GeneType.Negative
              cases ht : g.type with
              | Positive => rfl
              | Negative => exact absurd ht h_not_pos
              | NonPolarized => exact absurd ht hg_pol
          -- Gene.ofRankAlt g.rank .Negative = single g 1 (since g has the matching type).
          have hofRankAlt : Gene.ofRankAlt g.rank GeneType.Negative = Finsupp.single g 1 := by
            rw [Gene.ofRankAlt_eq_gene g.rank_pos]
            congr 1
            exact Gene.ext rfl hg_neg.symm
          -- signature_prime_ofRankAlt_negative: priming g_-(k) leaves the first component fixed.
          have hkey := signature_prime_ofRankAlt_negative g.rank_pos
          rw [hofRankAlt, prime_single, one_smul, ← primeGene_def] at hkey
          -- hkey : signature (single g 1) - signature (primeGene g) = (0, 1)
          have hfst : (signature (Finsupp.single g 1)).1 = (signature (primeGene g)).1 := by
            have h : (signature (Finsupp.single g 1)).1 - (signature (primeGene g)).1 = 0 :=
              calc (signature (Finsupp.single g 1)).1 - (signature (primeGene g)).1
                  = (signature (Finsupp.single g 1) - signature (primeGene g)).1 := rfl
                _ = (0, 1).1 := congr_arg Prod.fst hkey
                _ = 0 := rfl
            linarith
          -- signature (single g 1) has first component = g.signature.1.
          have hsingle : (signature (Finsupp.single g 1)).1 = g.signature.1 := by
            rw [signature_fst, Finsupp.sum_single_index (by simp), Nat.cast_one, one_smul]
          linarith
        -- a₀ = c₀ follows from equal ranks and componentwise dominance (X ≤ Y).
        have ha₀_eq_c₀ : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 := by
          simp only [Sigma.sigma, Function.iterate_zero, id]
          have hsig_le := (le_iff_dominates.mp hXY.le) 0
          simp only [Function.iterate_zero, id] at hsig_le
          have hXsum := @signature_sum_eq_rank X.1.val
          have hYsum := @signature_sum_eq_rank Y.1.val
          have hXrank : (X.1.val.rank : ℚ) = m + 2 := by exact_mod_cast X.2
          have hYrank : (Y.1.val.rank : ℚ) = m + 2 := by exact_mod_cast Y.2
          obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
          linarith
        -- c₁ ≤ c₀: sigma of Y is antitone.
        have hc₁_le_c₀ : (Sigma.sigma Y.1 1).1 ≤ (Sigma.sigma Y.1 0).1 :=
          (Prod.le_def.mp (Sigma.antitone Y.1 (Nat.zero_le 1))).1
        -- a₁ = a₀ = c₀ ≥ c₁ > a₁: contradiction.
        linarith
      -- Choose g₂ of minimal rank among all g₊-genes in X (Step 2: "choose k minimal").
      have hg₂ : ∃ g₂ : Gene,
          Gene.ofRankAlt g₂.rank GeneType.Positive = Finsupp.single g₂ 1 ∧
          0 < X.1.val g₂ ∧
          ∀ g' : Gene, Gene.ofRankAlt g'.rank GeneType.Positive = Finsupp.single g' 1 →
            0 < X.1.val g' → g₂.rank ≤ g'.rank := by
        have hSne : (X.1.val.support.filter
            (fun g => g.type = Int.negOnePow (g.rank - 1) • GeneType.Positive)).Nonempty := by
          obtain ⟨g, hgtype, hgpos⟩ := hg₂_exists
          exact ⟨g, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hgpos.ne', hgtype⟩⟩
        obtain ⟨g₂, hg₂S, hg₂min⟩ := Finset.exists_min_image _ Gene.rank hSne
        rw [Finset.mem_filter] at hg₂S
        refine ⟨g₂,
          by rw [Gene.ofRankAlt_eq_gene g₂.rank_pos]; congr 1; exact Gene.ext rfl hg₂S.2.symm,
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂S.1),
          fun g' hg'_eq hg'pos => hg₂min g' (Finset.mem_filter.mpr
            ⟨Finsupp.mem_support_iff.mpr hg'pos.ne', by
              have h := (Gene.ofRankAlt_eq_gene g'.rank_pos).symm.trans hg'_eq
              exact (congr_arg Gene.type
                ((Finsupp.single_left_inj one_ne_zero).mp h)).symm⟩)⟩
      obtain ⟨g₂, hg₂type, hg₂pos, hg₂min⟩ := hg₂

      -- Step 3: the mutation g₋(g₁.rank) + g₊(g₂.rank) → g₊(g₁.rank−1) + g₋(g₂.rank+1).
      -- Hypotheses for Pi.Primitive.type3 (ε = Negative, m = g₁.rank, n = g₂.rank).
      have hε_neg : GeneType.Negative ≠ .NonPolarized := by decide
      have hle_ranks : g₁.rank ≤ g₂.rank :=
        hg₁min g₂ (Finsupp.mem_support_iff.mpr hg₂pos.ne')
      -- g₁ is the gene inside Gene.ofRankAlt g₁.rank Negative.
      have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Negative = Finsupp.single g₁ 1 := by
        rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]; congr 1; exact Gene.ext rfl hε₁.symm
      -- Recover the type of g₂ from the ofRankAlt identity.
      have hg₂_type_eq : g₂.type = Int.negOnePow (g₂.rank - 1) • GeneType.Positive :=
        (congr_arg Gene.type ((Finsupp.single_left_inj one_ne_zero).mp
          ((Gene.ofRankAlt_eq_gene g₂.rank_pos).symm.trans hg₂type))).symm
      -- g₁ ≠ g₂: their types are incompatible (Negative-family vs Positive-family).
      have hg₁g₂_ne : g₁ ≠ g₂ := fun heq => by
        rw [← heq] at hg₂_type_eq; rw [hε₁] at hg₂_type_eq
        simp only [GeneType.negOnePow_smul, GeneType.neg_negative, GeneType.neg_positive]
          at hg₂_type_eq
        split_ifs at hg₂_type_eq;

      -- The primitive source chromosome equals single g₁ 1 + single g₂ 1.
      have hsrc_val : (Pi.X3 hε_neg hle_ranks g₁.rank_pos : Chromosome) =
          Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
        simp only [Pi.X3_eq, GeneType.neg_negative]; rw [hg₁_ofRankAlt, hg₂type]
      -- src ≤ X.1.val pointwise (using hXg₁pos, hg₂pos, and g₁ ≠ g₂).
      have hsrc_le : ∀ g : Gene,
          (Pi.X3 hε_neg hle_ranks g₁.rank_pos : Chromosome) g ≤ X.1.val g := by
        intro g
        rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
        rcases eq_or_ne g g₁ with rfl | hne₁
        · simp only [↓reduceIte, if_neg (Ne.symm hg₁g₂_ne)]; exact hXg₁pos
        · rcases eq_or_ne g g₂ with rfl | hne₂
          · simp only [if_neg (Ne.symm hne₁), ↓reduceIte, zero_add]; exact hg₂pos
          · simp only [if_neg (Ne.symm hne₁), if_neg (Ne.symm hne₂), add_zero, Nat.zero_le]
      -- rest = X.1 − src, still in Pi.
      let rest : Pi :=
        ⟨X.1.val - (Pi.X3 hε_neg hle_ranks g₁.rank_pos : Chromosome),
          Variety.sub_mem_Pi _ X.1.2⟩
      -- X.1 decomposes as src + rest.
      have hdecomp : X.1 = Pi.X3 hε_neg hle_ranks g₁.rank_pos + rest :=
        Subtype.val_injective
          (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
      -- Z is the result of the mutation.
      let Z : Pi := Pi.Y3 hε_neg hle_ranks g₁.rank_pos + rest
      -- Construct the Pi-step.
      have hstep : Pi.Step X.1 Z :=
        hdecomp.symm ▸ Pi.Step.mk
          (Pi.X3 hε_neg hle_ranks g₁.rank_pos)
          (Pi.Y3 hε_neg hle_ranks g₁.rank_pos)
          rest
          (Pi.Primitive.type3 GeneType.Negative hε_neg hle_ranks g₁.rank_pos)
      -- Step 4: σ(Z) = σ(X) + alternating increment on [g₁.rank, g₂.rank], zero elsewhere.
      -- The type-3 mutation with ε = Negative adds (1,0) at odd columns and (0,1) at even
      -- columns within [g₁.rank, g₂.rank], and is the identity outside this range.
      have hstep4 : ∀ i : ℕ,
          Sigma.sigma Z.val i =
          Sigma.sigma X.1.val i +
          if g₁.rank ≤ i ∧ i ≤ g₂.rank then
            if Even i then (0, 1) else (1, 0)
          else (0, 0) := by
        intro i
        -- sigma is additive on Chromosomes
        have sigma_add : ∀ (A B : Chromosome),
            Sigma.sigma (A + B) i = Sigma.sigma A i + Sigma.sigma B i :=
          fun A B => by simp only [Sigma.sigma, iterate_map_add, map_add]
        -- Z.val = Y3.val + rest.val (from the let definition and AddSubmonoid.coe_add)
        have hZ_split : Sigma.sigma Z.val i =
            Sigma.sigma (Pi.Y3 hε_neg hle_ranks g₁.rank_pos).val i +
            Sigma.sigma rest.val i := by
          change Sigma.sigma (Pi.Y3 hε_neg hle_ranks g₁.rank_pos + rest : Variety.Pi).val i = _
          simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
        -- X.1.val = X3.val + rest.val (from hdecomp and AddSubmonoid.coe_add)
        have hX_split : Sigma.sigma X.1.val i =
            Sigma.sigma (Pi.X3 hε_neg hle_ranks g₁.rank_pos).val i +
            Sigma.sigma rest.val i := by
          have hval : X.1.val = (Pi.X3 hε_neg hle_ranks g₁.rank_pos).val + rest.val := by
            have h := congrArg Subtype.val hdecomp
            simp only [AddSubmonoid.coe_add] at h
            exact h
          rw [hval, sigma_add]
        rw [hZ_split, hX_split, Sigma.mutation_type3_sigma_eq hε_neg hle_ranks g₁.rank_pos i]
        simp only [GeneType.neg_negative, signature_ofRank_one_negative,
          signature_ofRank_one_positive]
        abel
        -- It remains to show Z ≤ Y.1.
        --First show strict inequality (X,Y) on the appt indexes, then since Z is + 1 or 0,
        -- have weak inequality (Z,Y)
      refine ⟨Z, hstep, ?_⟩
      -- Case split on the parity of k = g₂.rank.
      rcases Nat.even_or_odd g₂.rank with ⟨j, hk_even⟩ | ⟨j, hk_odd⟩
      · -- k even: g₂.rank = 2 * j
        have hXchain : ∀ i : ℕ, i < g₂.rank →
            (if Even i then (Sigma.sigma X.1 i).1 - (Sigma.sigma X.1 (i + 1)).1
             else (Sigma.sigma X.1 i).2 - (Sigma.sigma X.1 (i + 1)).2) =
            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 :=
          fun i hi => x_side_equalities hXpn hg₂type hg₂pos hg₂min hi
        have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
          have ha₀ := sigma_zero_fst_eq X Y hXY.le
          linarith
        change Z.val ≤ Y.1.val
        rw [le_iff_dominates]
        intro i
        change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
        have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
          le_iff_dominates.mp hXY.le i
        rw [hstep4 i]
        split_ifs with hin heven
        · -- In range, even i: σ(Z)(i) = σ(X)(i) + (0, 1), increment at .2 component.
          suffices h : (Sigma.sigma X.1.val i).2 < (Sigma.sigma Y.1.val i).2 by
            constructor
            · calc (Sigma.sigma X.1.val i + ((0, 1) : ℚ × ℚ)).1
                  = (Sigma.sigma X.1.val i).1 + 0 := rfl
                _ ≤ (Sigma.sigma Y.1.val i).1 := by linarith [hXY_i.1]
            · obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.1.2 (k := i))
              obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.1.2 (k := i))
              simp only [Sigma.sigma] at h ⊢
              simp only [Prod.snd_add]
              rw [hnX, hnY] at h ⊢
              simp only at h ⊢
              have hnXY : nX.2 < nY.2 := Nat.cast_lt.mp h
              exact_mod_cast Nat.add_one_le_iff.mpr hnXY
          -- No hi_lt needed: i ≤ g₂.rank and 1 ≤ i give i-1 < g₂.rank directly.
          have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
          have hpred_odd : ¬Even (i - 1) := by
            simp only [Nat.even_iff] at *; omega
          have hX_eq : (Sigma.sigma X.1 (i - 1)).2 - (Sigma.sigma X.1 i).2 =
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            have h := hXchain (i - 1) (by omega)
            simp only [if_neg hpred_odd] at h
            rwa [Nat.sub_add_cancel hi_pos] at h
          have hY_le : (Sigma.sigma Y.1.val (i - 1)).2 - (Sigma.sigma Y.1.val i).2 ≤
              (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
            simp only [if_neg hpred_odd] at h
            rwa [Nat.sub_add_cancel hi_pos] at h
          have hXY_pred : (Sigma.sigma X.1.val (i - 1)).2 ≤ (Sigma.sigma Y.1.val (i - 1)).2 :=
            (le_iff_dominates.mp hXY.le (i - 1)).2
          linarith [hX_eq, hY_le, hstrict, hXY_pred]
        · -- In range, odd i: σ(Z)(i) = σ(X)(i) + (1, 0), increment at .1 component.
          suffices h : (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.1.val i).1 by
            constructor
            · obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.1.2 (k := i))
              obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.1.2 (k := i))
              simp only [Sigma.sigma] at h ⊢
              simp only [Prod.fst_add]
              rw [hnX, hnY] at h ⊢
              simp only at h ⊢
              have hnXY : nX.1 < nY.1 := Nat.cast_lt.mp h
              exact_mod_cast Nat.add_one_le_iff.mpr hnXY
            · calc (Sigma.sigma X.1.val i + ((1, 0) : ℚ × ℚ)).2
                  = (Sigma.sigma X.1.val i).2 + 0 := rfl
                _ ≤ (Sigma.sigma Y.1.val i).2 := by linarith [hXY_i.2]
          have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
          have hpred_even : Even (i - 1) := by
            simp only [Nat.even_iff] at *; omega
          have hX_eq : (Sigma.sigma X.1 (i - 1)).1 - (Sigma.sigma X.1 i).1 =
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            have h := hXchain (i - 1) (by omega)
            simp only [if_pos hpred_even] at h
            rwa [Nat.sub_add_cancel hi_pos] at h
          have hY_le : (Sigma.sigma Y.1.val (i - 1)).1 - (Sigma.sigma Y.1.val i).1 ≤
              (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
            simp only [if_pos hpred_even] at h
            rwa [Nat.sub_add_cancel hi_pos] at h
          have hXY_pred : (Sigma.sigma X.1.val (i - 1)).1 ≤ (Sigma.sigma Y.1.val (i - 1)).1 :=
            (le_iff_dominates.mp hXY.le (i - 1)).1
          linarith [hX_eq, hY_le, hstrict, hXY_pred]
        · -- Outside mutation range: σ(Z)(i) = σ(X)(i) + (0,0) = σ(X)(i) ≤ σ(Y)(i).
          have h00 : ((0, 0) : ℚ × ℚ) = 0 := rfl
          rw [h00, add_zero]
          exact hXY_i
      · -- k odd: g₂.rank = 2 * j + 1
        -- Step 5: chain of inequalities.
        -- 5a (X-side equalities, proved): for all i < g₂.rank, the alternating sigma-difference
        -- of X equals P = (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1.
        have hXchain : ∀ i : ℕ, i < g₂.rank →
            (if Even i then (Sigma.sigma X.1 i).1 - (Sigma.sigma X.1 (i + 1)).1
             else (Sigma.sigma X.1 i).2 - (Sigma.sigma X.1 (i + 1)).2) =
            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 :=
          fun i hi => x_side_equalities hXpn hg₂type hg₂pos hg₂min hi
        -- 5b (Y-side weak chain): alternating sigma-differences of Y are non-increasing
        -- This is sigma.cond_15_6_compare_k_to_0
        -- 5c (strict inequality): a₀ = c₀ and a₁ < c₁ give c₀ - c₁ < P.
        have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
          have ha₀ := sigma_zero_fst_eq X Y hXY.le
          linarith
        -- Step 6: telescoping to conclude Z ≤ Y.1.
        -- The mutation adds alternating (1,0)/(0,1) increments to σ(X) on [g₁.rank, g₂.rank].
        -- At each such column the strict inequality from step 5 (combined with X ≤ Y elsewhere)
        -- absorbs the increment.
        change Z.val ≤ Y.1.val
        rw [le_iff_dominates]
        intro i
        -- Unfold sigma so that hstep4 can rewrite the goal.
        change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
        -- Weak X ≤ Y at column i, componentwise (with explicit Sigma.sigma type).
        have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
          le_iff_dominates.mp hXY.le i
        -- Rewrite σ(Z)(i) using the mutation increment formula.
        rw [hstep4 i]
        -- split_ifs handles the three branches: in-range even, in-range odd, out-of-range.
        split_ifs with hin heven
        · -- In range, even i: σ(Z)(i) = σ(X)(i) + (0, 1), increment at .2 component.
          -- Suffices: (σ(X)(i)).2 < (σ(Y)(i)).2; integrality gives (σ(X)(i)).2 + 1 ≤ (σ(Y)(i)).2.
          suffices h : (Sigma.sigma X.1.val i).2 < (Sigma.sigma Y.1.val i).2 by
            constructor
            · -- (σ(X)(i) + (0,1)).1 = (σ(X)(i)).1 + 0 ≤ (σ(Y)(i)).1
              calc (Sigma.sigma X.1.val i + ((0, 1) : ℚ × ℚ)).1
                  = (Sigma.sigma X.1.val i).1 + 0 := rfl
                _ ≤ (Sigma.sigma Y.1.val i).1 := by linarith [hXY_i.1]
            · -- (σ(X)(i)).2 + 1 ≤ (σ(Y)(i)).2: sigma values of Pi-chromosomes are integers,
              -- so strict inequality implies gap ≥ 1.
              obtain ⟨nX, hnX⟩ := signature_pi_isNat (prime_mem_Pi_iterate X.1.2 (k := i))
              obtain ⟨nY, hnY⟩ := signature_pi_isNat (prime_mem_Pi_iterate Y.1.2 (k := i))
              simp only [Sigma.sigma] at h ⊢
              simp only [Prod.snd_add]
              rw [hnX, hnY] at h ⊢
              simp only at h ⊢
              have hnXY : nX.2 < nY.2 := Nat.cast_lt.mp h
              exact_mod_cast Nat.add_one_le_iff.mpr hnXY
          -- Step 1: predecessor i-1 exists (i ≥ 1) and is odd (i is even and i ≠ g₂.rank)
          have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
          have hi_lt : i < g₂.rank := by
            rcases Nat.lt_or_eq_of_le hin.2 with h | h
            · exact h
            · exact absurd heven (h ▸ hk_odd ▸ Nat.not_even_two_mul_add_one j)
          have hpred_odd : ¬Even (i - 1) := by
            simp only [Nat.even_iff] at *
            omega
          -- Step 2: X's .2-component difference at i-1 equals P
          have hX_eq : (Sigma.sigma X.1 (i - 1)).2 - (Sigma.sigma X.1 i).2 =
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            have h := hXchain (i - 1) (by omega)
            simp only [if_neg hpred_odd] at h
            rwa [Nat.sub_add_cancel hi_pos] at h
          -- Step 3: Y's .2-component difference at i-1 is ≤ c₀ − c₁
          have hY_le : (Sigma.sigma Y.1.val (i - 1)).2 - (Sigma.sigma Y.1.val i).2 ≤
              (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
            simp only [if_neg hpred_odd] at h
            rwa [Nat.sub_add_cancel hi_pos] at h
          -- Step 4: Y dominates X at column i-1 in the .2 component
          have hXY_pred : (Sigma.sigma X.1.val (i - 1)).2 ≤ (Sigma.sigma Y.1.val (i - 1)).2 :=
            (le_iff_dominates.mp hXY.le (i - 1)).2
          -- Step 5: chain c₀-c₁ < P = σX(i-1).2 - σX(i).2 with σX(i-1).2 ≤ σY(i-1).2
          linarith [hX_eq, hY_le, hstrict, hXY_pred]
        · -- In range, odd i: σ(Z)(i) = σ(X)(i) + (1, 0), increment at .1 component.
          -- Suffices: (σ(X)(i)).1 < (σ(Y)(i)).1; integrality gives (σ(X)(i)).1 + 1 ≤ (σ(Y)(i)).1.
          suffices h : (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.1.val i).1 by
            constructor
            · -- (σ(X)(i)).1 + 1 ≤ (σ(Y)(i)).1: follows from h by integrality.
              obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val i X.1.2
              obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val i Y.1.2
              rw [hnX, hnY] at h ⊢
              simp only [Prod.fst_add] at h ⊢
              exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp h)
            · -- (σ(X)(i) + (1,0)).2 = (σ(X)(i)).2 + 0 ≤ (σ(Y)(i)).2
              calc (Sigma.sigma X.1.val i + ((1, 0) : ℚ × ℚ)).2
                  = (Sigma.sigma X.1.val i).2 + 0 := rfl
                _ ≤ (Sigma.sigma Y.1.val i).2 := by linarith [hXY_i.2]
          -- Step 1: predecessor i-1 exists (i ≥ 1) and is even (i is odd)
          have hi_pos : 1 ≤ i := Nat.le_trans g₁.rank_pos hin.1
          have hpred_even : Even (i - 1) := by
            simp only [Nat.even_iff] at *
            omega
          -- Step 2: X's .1-component difference at i-1 equals P
          have hX_eq : (Sigma.sigma X.1 (i - 1)).1 - (Sigma.sigma X.1 i).1 =
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            have h := hXchain (i - 1) (by omega)
            simp only [if_pos hpred_even] at h
            rwa [Nat.sub_add_cancel hi_pos] at h
          -- Step 3: Y's .1-component difference at i-1 is ≤ c₀ − c₁
          have hY_le : (Sigma.sigma Y.1.val (i - 1)).1 - (Sigma.sigma Y.1.val i).1 ≤
              (Sigma.sigma Y.1.val 0).1 - (Sigma.sigma Y.1.val 1).1 := by
            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (i - 1) Y.1.2
            simp only [if_pos hpred_even] at h
            rwa [Nat.sub_add_cancel hi_pos] at h
          -- Step 4: Y dominates X at column i-1 in the .1 component
          have hXY_pred : (Sigma.sigma X.1.val (i - 1)).1 ≤ (Sigma.sigma Y.1.val (i - 1)).1 :=
            (le_iff_dominates.mp hXY.le (i - 1)).1
          -- Step 5: chain c₀-c₁ < P = σX(i-1).1 - σX(i).1 with σX(i-1).1 ≤ σY(i-1).1
          linarith [hX_eq, hY_le, hstrict, hXY_pred]
        · -- Outside mutation range: σ(Z)(i) = σ(X)(i) + (0,0) = σ(X)(i) ≤ σ(Y)(i).
          have h00 : ((0, 0) : ℚ × ℚ) = 0 := rfl
          rw [h00, add_zero]
          exact hXY_i
        -/
    · -- Cases 2-4
      by_cases hg₁_one : g₁.rank = 1
      · -- g₁.rank = 1 (case 2)
        sorry /-
        have hb₀_eq_d₀ : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
          sigma_zero_snd_eq X Y hXY.le
        have hb₀_gt_a₁ : (Sigma.sigma X.1 1).1 < (Sigma.sigma X.1 0).2 := by
          have hd₀_ge_c₁ : (Sigma.sigma Y.1 1).1 ≤ (Sigma.sigma Y.1 0).2 := by
            have h := Sigma.cond_15_5 Y.1.val 0
            rw [if_pos (by norm_num : Even (0 : ℕ))] at h; exact h
          linarith [hb₀_eq_d₀]
        have hg₂_neg : ∃ g₂ : Gene,
            g₂.type = .Negative ∧
            0 < X.1.val g₂ ∧
            ∀ g' : Gene, g'.type = .Negative → 0 < X.1.val g' → g₂.rank ≤ g'.rank := by
          have hSne : (X.1.val.support.filter (fun g => g.type = .Negative)).Nonempty := by
            obtain ⟨g, hgtype, hgpos⟩ := Sigma.neg_gene_of_b0_gt_a1 X.1.val X.1.2 hb₀_gt_a₁
            exact ⟨g, Finset.mem_filter.mpr
              ⟨Finsupp.mem_support_iff.mpr hgpos.ne', hgtype⟩⟩
          obtain ⟨g₂, hg₂S, hg₂min⟩ := Finset.exists_min_image _ Gene.rank hSne
          rw [Finset.mem_filter] at hg₂S
          exact ⟨g₂, hg₂S.2,
            Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂S.1),
            fun g' hg'_neg hg'_pos => hg₂min g'
              (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hg'_pos.ne', hg'_neg⟩)⟩

        obtain ⟨g₂, hg₂_type, hg₂_pos, hg₂_min⟩ := hg₂_neg
        -- g₁ has type Positive (not Negative from hε₁, not NonPolarized from polarization).
        have hg₁_type : g₁.type = .Positive := by
          have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁
            (Finsupp.mem_support_iff.mpr hXg₁)
          cases ht : g₁.type with
          | Positive => rfl
          | NonPolarized => exact absurd ht hpol
          | Negative =>
            exfalso; apply hε₁
            rw [ht, hg₁_one]; simp
        -- g₁ ≠ g₂ (Positive vs Negative types are distinct).
        have hg₁g₂_ne : g₁ ≠ g₂ := fun heq => by
          rw [← heq, hg₁_type] at hg₂_type; exact absurd hg₂_type (by decide)
        -- Hypotheses for Pi.Primitive.type1 (ε = Positive, m = 1, n = g₂.rank).
        have hε_pos : GeneType.Positive ≠ .NonPolarized := by decide
        have hle_ranks : 1 ≤ g₂.rank := g₂.rank_pos
        -- ofRank 1 .Positive = single g₁ 1 (using g₁.rank = 1, g₁.type = .Positive).
        have hg₁_ofRank : Gene.ofRank 1 GeneType.Positive = Finsupp.single g₁ 1 := by
          have h := @Gene.ofRank_eq_gene g₁; rw [hg₁_one, hg₁_type] at h; exact h
        -- ofRank g₂.rank .Negative = single g₂ 1 (using g₂.type = .Negative).
        have hg₂_ofRank : Gene.ofRank g₂.rank GeneType.Negative = Finsupp.single g₂ 1 := by
          have h := @Gene.ofRank_eq_gene g₂; rw [hg₂_type] at h; exact h
        -- The type1 source chromosome equals single g₁ 1 + single g₂ 1.
        have hsrc_val : (Pi.X1 hε_pos hle_ranks (le_refl 1) : Chromosome) =
            Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
          simp only [Pi.X1_eq, GeneType.neg_positive]; rw [hg₁_ofRank, hg₂_ofRank]
        -- src ≤ X.1.val pointwise.
        have hsrc_le : ∀ g : Gene,
            (Pi.X1 hε_pos hle_ranks (le_refl 1) : Chromosome) g ≤ X.1.val g := by
          intro g
          rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
          rcases eq_or_ne g g₁ with rfl | hne₁
          · simp only [↓reduceIte, if_neg (Ne.symm hg₁g₂_ne)]; exact hXg₁pos
          · rcases eq_or_ne g g₂ with rfl | hne₂
            · simp only [if_neg (Ne.symm hne₁), ↓reduceIte, zero_add]; exact hg₂_pos
            · simp only [if_neg (Ne.symm hne₁), if_neg (Ne.symm hne₂), add_zero, Nat.zero_le]
        -- rest = X.1 − src, still in Pi.
        let rest : Pi :=
          ⟨X.1.val - (Pi.X1 hε_pos hle_ranks (le_refl 1) : Chromosome),
            Variety.sub_mem_Pi _ X.1.2⟩
        -- X.1 decomposes as src + rest.
        have hdecomp : X.1 = Pi.X1 hε_pos hle_ranks (le_refl 1) + rest :=
          Subtype.val_injective
            (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
        -- Z is the type1 mutation result: ofRank (g₂.rank+1) .Positive + rest.
        let Z : Pi := Pi.Y1 hε_pos hle_ranks (le_refl 1) + rest
        -- Construct the Pi-step.
        have hstep : Pi.Step X.1 Z :=
          hdecomp.symm ▸ Pi.Step.mk
            (Pi.X1 hε_pos hle_ranks (le_refl 1))
            (Pi.Y1 hε_pos hle_ranks (le_refl 1))
            rest
            (Pi.Primitive.type1 GeneType.Positive hε_pos hle_ranks (le_refl 1))
        have hsigma_diff_XZ : ∀ i : ℕ, 1 ≤ i → i ≤ g₂.rank →
            (Sigma.sigma Z.val i) - (Sigma.sigma X.val i) = (1, 0) := by
          intro i i_lb i_ub
          simp [Z, hdecomp, Sigma.sigma_linearity, Pi.Y1_eq, Pi.X1_eq]
          simp [Sigma.sigma]
          simp [prime_iterate_ofRank]
          have : 1 - i = 0 := by omega
          simp [this]
          simp [signature_ofRank_positive (by omega : 1 ≤ g₂.rank + 1 - i),
              show g₂.rank + 1 - i - 1 = g₂.rank - i from by omega]
        have hsigma_diff_XY : ∀ i : ℕ, 1 ≤ i → i ≤ g₂.rank →
            (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.val i).1 := by
          intro i i_lb i_ub
          exact caseA2_strict_fst X Y hXY hg₂_min hb₀_eq_d₀ ha i_lb i_ub
        exact ⟨Z, hstep, by
          change Z.val ≤ Y.1.val
          rw [le_iff_dominates]
          intro i
          change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
          have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
            le_iff_dominates.mp hXY.le i
          by_cases hin : 1 ≤ i ∧ i ≤ g₂.rank
          · obtain ⟨hi1, hi2⟩ := hin
            have hdiff := hsigma_diff_XZ i hi1 hi2
            have hlt := hsigma_diff_XY i hi1 hi2
            -- Extract component equations: Z.1 = X.1 + 1 and Z.2 = X.2
            have hfst : (Sigma.sigma Z.val i).1 = (Sigma.sigma X.1.val i).1 + 1 := by
              have h : (Sigma.sigma Z.val i).1 - (Sigma.sigma X.1.val i).1 = 1 :=
                calc (Sigma.sigma Z.val i).1 - (Sigma.sigma X.1.val i).1
                    = (Sigma.sigma Z.val i - Sigma.sigma X.val i).1 := rfl
                  _ = ((1 : ℚ), (0 : ℚ)).1 := congr_arg Prod.fst hdiff
                  _ = 1 := rfl
              linarith
            have hsnd : (Sigma.sigma Z.val i).2 = (Sigma.sigma X.1.val i).2 := by
              have h : (Sigma.sigma Z.val i).2 - (Sigma.sigma X.1.val i).2 = 0 :=
                calc (Sigma.sigma Z.val i).2 - (Sigma.sigma X.1.val i).2
                    = (Sigma.sigma Z.val i - Sigma.sigma X.val i).2 := rfl
                  _ = ((1 : ℚ), (0 : ℚ)).2 := congr_arg Prod.snd hdiff
                  _ = 0 := rfl
              linarith
            constructor
            · -- (Z).1 = (X).1 + 1 ≤ (Y).1: (X).1 < (Y).1 strict, integrality absorbs the +1
              rw [hfst]
              suffices h : (Sigma.sigma X.1.val i).1 < (Sigma.sigma Y.1.val i).1 by
                obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val i X.1.2
                obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val i Y.1.2
                rw [hnX, hnY] at h ⊢
                simp only at h ⊢
                exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp h)
              exact hlt
            · -- (Z).2 = (X).2 ≤ (Y).2: no increment in second component
              linarith [hsnd, hXY_i.2]
          · push Not at hin
            -- Outside [1, g₂.rank]: type1 mutation does not alter sigma at i
            have hZ_eq : Sigma.sigma Z.val i = Sigma.sigma X.1.val i := by
              -- Split Z = Y1 + rest and X.1 = X1 + rest, reducing to sigma Y1 i = sigma X1 i
              have hZ_split : Sigma.sigma Z.val i =
                  Sigma.sigma (Pi.Y1 hε_pos hle_ranks (le_refl 1)).val i +
                  Sigma.sigma rest.val i := by
                change Sigma.sigma (Pi.Y1 hε_pos hle_ranks (le_refl 1) + rest : Variety.Pi).val i =
                 _
                simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
              have hX_split : Sigma.sigma X.1.val i =
                  Sigma.sigma (Pi.X1 hε_pos hle_ranks (le_refl 1)).val i +
                  Sigma.sigma rest.val i := by
                have hval : X.1.val = (Pi.X1 hε_pos hle_ranks (le_refl 1)).val + rest.val := by
                  have h := congrArg Subtype.val hdecomp
                  simp only [AddSubmonoid.coe_add] at h; exact h
                simp only [hval, Sigma.sigma, iterate_map_add, map_add]
              suffices h : Sigma.sigma (Pi.Y1 hε_pos hle_ranks (le_refl 1)).val i =
                           Sigma.sigma (Pi.X1 hε_pos hle_ranks (le_refl 1)).val i by
                rw [hZ_split, hX_split, h]
              -- push_neg gives hin : 1 ≤ i → g₂.rank < i; case split on whether 1 ≤ i
              by_cases hi1 : 1 ≤ i
              · -- i ≥ 1, so i > g₂.rank from hin
                have hi_gt : g₂.rank < i := hin hi1
                -- prime^[i] kills all genes in X1 (ranks 1, g₂.rank) and Y1 (rank g₂.rank+1)
                have hX1_zero : Sigma.sigma (Pi.X1 hε_pos hle_ranks (le_refl 1)).val i = 0 := by
                  simp only [Sigma.sigma, Pi.X1_eq, GeneType.neg_positive, iterate_map_add,
                             prime_iterate_ofRank,
                             show 1 - i = 0 from by omega,
                             show g₂.rank - i = 0 from by omega,
                             Gene.ofRank_zero, map_zero, add_zero]
                have hY1_zero : Sigma.sigma (Pi.Y1 hε_pos hle_ranks (le_refl 1)).val i = 0 := by
                  simp only [Sigma.sigma, Pi.Y1_eq, GeneType.neg_positive, prime_iterate_ofRank,
                             show (1 : ℕ) - 1 = 0 from rfl, Gene.ofRank_zero,
                             show g₂.rank + 1 - i = 0 from by omega,
                             map_zero, zero_add]
                rw [hY1_zero, hX1_zero]
              · -- i = 0: mutation_type1_signature_eq gives equal signatures at level 0
                have hi : i = 0 := by omega
                subst hi
                simp only [Sigma.sigma, Function.iterate_zero, id, Pi.Y1_eq, Pi.X1_eq]
                exact (mutation_type1_signature_eq hε_pos hle_ranks (le_refl 1)).symm
            rw [hZ_eq]
            exact hXY_i⟩
            -/
      · -- g₁.rank ≥ 2 (Case 3-4)
        have hg₁_ge2 : 2 ≤ g₁.rank := by
          have := g₁.rank_pos; omega
        by_cases h2g₁ : 2 ≤ X.1.val g₁
        · sorry /-
          -- Case 3: 2 * g₁ ≤ X (g₁ appears with multiplicity ≥ 2)
          -- g₁ is polarized (not NonPolarized)
          have hε : g₁.type ≠ .NonPolarized :=
            IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
          -- Gene.ofRank g₁.rank g₁.type = Finsupp.single g₁ 1
          have hg₁_ofRank : Gene.ofRank g₁.rank g₁.type = Finsupp.single g₁ 1 :=
            @Gene.ofRank_eq_gene g₁
          -- Pi.X2 (with m = n = g₁.rank) equals Finsupp.single g₁ 2
          have hsrc_val : (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 : Chromosome) =
              Finsupp.single g₁ 2 := by
            simp only [Pi.X2_eq, hg₁_ofRank]
            ext g; simp [Finsupp.single_apply]; split_ifs with heq <;> simp
          -- Pi.X2 ≤ X.1.val pointwise
          have hsrc_le : ∀ g : Gene,
              (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 : Chromosome) g ≤ X.1.val g := by
            intro g
            rw [hsrc_val, Finsupp.single_apply]
            split_ifs with heq
            · subst heq; exact h2g₁
            · exact Nat.zero_le _
          -- rest = X.1 − Pi.X2, still in Pi
          let rest : Pi :=
            ⟨X.1.val - (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 : Chromosome),
              Variety.sub_mem_Pi _ X.1.2⟩
          -- X.1 decomposes as Pi.X2 + rest
          have hdecomp : X.1 = Pi.X2 hε (le_refl g₁.rank) hg₁_ge2 + rest :=
            Subtype.val_injective
              (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
          -- Z is the type2 mutation result: Pi.Y2 + rest
          let Z : Pi := Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2 + rest
          -- Construct the Pi-step
          have hstep : Pi.Step X.1 Z :=
            hdecomp.symm ▸ Pi.Step.mk
              (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2)
              (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2)
              rest
              (Pi.Primitive.type2 g₁.type hε (le_refl g₁.rank) hg₁_ge2)
          -- b₁ - b₂ = a₀ - a₁
          have hb12_eq : (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 =
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            -- g₁.type is in the Positive family (not Negative by hε₁,
             --not NonPolarized by polarization)
            have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁
              (Finsupp.mem_support_iff.mpr hXg₁)
            have hg₁_pos_type : g₁.type = Int.negOnePow (g₁.rank - 1) • GeneType.Positive := by
              simp only [GeneType.negOnePow_smul, GeneType.neg_positive, GeneType.neg_negative]
                at hε₁ ⊢
              split_ifs with heven
              · simp only [if_pos heven] at hε₁
                cases ht : g₁.type with
                | Positive => rfl
                | Negative => exact absurd ht hε₁
                | NonPolarized => exact absurd ht hpol
              · simp only [if_neg heven] at hε₁
                cases ht : g₁.type with
                | Positive => exact absurd ht hε₁
                | Negative => rfl
                | NonPolarized => exact absurd ht hpol
            -- Gene.ofRankAlt g₁.rank Positive = single g₁ 1
            have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive = Finsupp.single g₁ 1
                := by
              rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
              congr 1; exact Gene.ext rfl hg₁_pos_type.symm
            -- Apply x_side_equalities at j = 1 (odd), using g₁ as the minimal Positive-family gene
            have h := x_side_equalities hXpn hg₁_ofRankAlt hXg₁pos
              (fun g' _ hg'_pos => hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
              (show 1 < g₁.rank from hg₁_ge2)
            simp only [show ¬Even 1 from by norm_num, ↓reduceIte] at h
            exact h
          -- a₀ - a₁ > c₀ - c₁
          have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
              (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
            have ha₀ := sigma_zero_fst_eq X Y hXY.le
            linarith
          -- c₀ - c₁ ≥ d₁ - d₂
          have hd12_le : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 ≤
              (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
            have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
            simp only [show ¬Even (2 - 1 : ℕ) from by norm_num, if_false] at h
            exact h
          -- b₁ ≤ d₁ from X ≤ Y at level 1
          have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
            (le_iff_dominates.mp hXY.le 1).2
          -- b₁ - b₂ > d₁ - d₂: chain hb12_eq > hstrict ≥ hd12_le
          have hb12_gt_d12 : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 <
              (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 := by
            linarith [hb12_eq, hstrict, hd12_le]
          -- d₂ > b₂: from b₁ ≤ d₁ and b₁ - b₂ > d₁ - d₂
          have hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2 := by
            linarith [hb1_le_d1, hb12_gt_d12]
          -- Extract the three parts of sigma_type2_same_rank:
          -- hleft : sigma(Pi.X2) = sigma(Pi.Y2) for i ≤ m - 2
          -- hright : sigma(Pi.X2) = sigma(Pi.Y2) for i ≥ m + 2
          -- hwindow : the nonzero differences at i = m-1, m, m+1
          obtain ⟨hleft, hright, hwindow⟩ :=
            Sigma.sigma_type2_same_rank g₁.type hε hg₁_ge2
          -- sigma(Z.val) = sigma(Pi.Y2.val) + sigma(rest.val)
          have hZ_split : ∀ i, Sigma.sigma Z.val i =
              Sigma.sigma (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2).val i +
              Sigma.sigma rest.val i := fun i => by
            change Sigma.sigma
              (Pi.Y2 hε (le_refl g₁.rank) hg₁_ge2 + rest : Variety.Pi).val i = _
            simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
          -- sigma(X.1.val) = sigma(Pi.X2.val) + sigma(rest.val)
          have hX_split : ∀ i, Sigma.sigma X.1.val i =
              Sigma.sigma (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2).val i +
              Sigma.sigma rest.val i := fun i => by
            have hval : X.1.val =
                (Pi.X2 hε (le_refl g₁.rank) hg₁_ge2).val + rest.val := by
              have h := congrArg Subtype.val hdecomp
              simp only [AddSubmonoid.coe_add] at h; exact h
            simp only [hval, Sigma.sigma, iterate_map_add, map_add]
          -- Prove Z ≤ Y.1 by checking each index
          refine ⟨Z, hstep, ?_⟩
          change Z.val ≤ Y.1.val
          rw [le_iff_dominates]
          intro i
          change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
          have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
            le_iff_dominates.mp hXY.le i
          by_cases hi1 : i ≤ g₁.rank - 2
          · -- Left of window: sigma(Pi.Y2) i = sigma(Pi.X2) i, so sigma Z i = sigma X.1 i
            rw [hZ_split, ← hleft i hi1, ← hX_split]; exact hXY_i
          · by_cases hi2 : g₁.rank + 2 ≤ i
            · -- Right of window: sigma(Pi.Y2) i = sigma(Pi.X2) i, so sigma Z i = sigma X.1 i
              rw [hZ_split, ← hright i hi2, ← hX_split]; exact hXY_i
            · -- Window: i ∈ {g₁.rank - 1, g₁.rank, g₁.rank + 1}
              have hi_range : i = g₁.rank - 1 ∨ i = g₁.rank ∨ i = g₁.rank + 1 := by omega

              by_cases heven : Even g₁.rank
              · -- g₁.rank is even
                -- for i = g₁.rank: c₁ - c_i ≤ d₀ - d_{i-1}
                have hc1_ci_rank : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
                  (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                  Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                -- for i = g₁.rank: d₀ - d_{i-1} ≤ b₀ - b_{i-1}
                have hd0_di_rank : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                  (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
                  have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                    sigma_zero_snd_eq X Y hXY.le
                  have hbm1_le_dm1 : (Sigma.sigma X.1 (g₁.rank - 1)).2 ≤
                      (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                    (le_iff_dominates.mp hXY.le (g₁.rank - 1)).2
                  linarith
                -- b₀ - b_{j-1} = a₁ - a_j for all 1 ≤ j ≤ g₁.rank
                have hb0_bi : ∀ j, 1 ≤ j → j ≤ g₁.rank →
                    (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (j - 1)).2 =
                    (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 j).1 :=
                  fun j hj1 hj2 => x_actual_negative_prefix_equalities
                    (fun g' _ hg'_pos =>
                      hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                    hj1 hj2
                -- for i = g₁.rank: b₀ - b_{i-1} = a₁ - a_i
                have hb0_bi_rank := hb0_bi g₁.rank (by omega) (le_refl _)
                -- for i = g₁.rank - 1: c₁ - c_i ≤ d₀ - d_{i-1}
                have hc1_ci_rank1 : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 ≤
                  (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                  Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                -- for i = g₁.rank - 1: d₀ - d_{i-1} ≤ b₀ - b_{i-1}
                have hd0_di_rank1 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 ≤
                  (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 := by
                  have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                    sigma_zero_snd_eq X Y hXY.le
                  have hbm2_le_dm2 : (Sigma.sigma X.1 (g₁.rank - 2)).2 ≤
                      (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                    (le_iff_dominates.mp hXY.le (g₁.rank - 2)).2
                  linarith
                -- for i = g₁.rank - 1: b₀ - b_{i-1} = a₁ - a_i
                have hb0_bi_rank1 := hb0_bi (g₁.rank - 1) (by omega) (by omega)
                simp only [show g₁.rank - 1 - 1 = g₁.rank - 2 from by omega] at hb0_bi_rank1
                -- a_{g₁.rank} < c_{g₁.rank}
                have ha_lt_c_rank : (Sigma.sigma X.1 g₁.rank).1 <
                    (Sigma.sigma Y.1 g₁.rank).1 := by
                  have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                    sigma_zero_fst_eq X Y hXY.le
                  linarith [hc1_ci_rank, hd0_di_rank, hb0_bi_rank, hstrict]
                -- a_{g₁.rank - 1} < c_{g₁.rank - 1}
                have ha_lt_c_rank1 : (Sigma.sigma X.1 (g₁.rank - 1)).1 <
                    (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
                  have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                    sigma_zero_fst_eq X Y hXY.le
                  linarith [hc1_ci_rank1, hd0_di_rank1, hb0_bi_rank1, hstrict]
                -- for i = g₁.rank - 1: d₂ - d_{i+1} ≤ c₁ - c_i
                have hd2_c1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                    (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
                  by_cases hrank2 : g₁.rank = 2
                  · simp only [hrank2, sub_self, le_refl]
                  · have h : g₁.rank - 1 ≥ 2 := by omega
                    have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
                    rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
                -- for i = g₁.rank - 1: d₂ - d_{i+1} ≤ d₀ - d_{i-1}
                have hd2_di1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                    (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                  hd2_c1_rank1.trans hc1_ci_rank1
                -- g₁.type = .Negative since rank is even and hε₁ rules out .Positive
                have hg₁_type : g₁.type = .Negative := by
                  have hne_pos : g₁.type ≠ .Positive := by
                    intro h; apply hε₁
                    have h_odd : ¬ Even ((g₁.rank : ℤ) - 1) := by
                      obtain ⟨r, hr⟩ := heven; intro ⟨k, hk⟩; omega
                    simp only [GeneType.negOnePow_smul, GeneType.neg_negative, if_neg h_odd, h]
                  cases ht : g₁.type with
                  | Positive => exact absurd ht hne_pos
                  | Negative => rfl
                  | NonPolarized => exact absurd ht hε
                -- all min-rank genes are Negative (else a pos-neg pair of equal rank exists)
                have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
                    g'.rank = g₁.rank → g'.type = .Negative := by
                  intro g' hg'_supp hg'_rank
                  have hg'_ne_np : g'.type ≠ .NonPolarized :=
                    IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
                  have hg'_ne_pos : g'.type ≠ .Positive := by
                    intro hg'_pos
                    apply hXpn
                    exact ⟨g', g₁, hg'_rank, hg'_pos, hg₁_type,
                           Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp), hXg₁pos⟩
                  cases ht' : g'.type with
                  | Positive => exact absurd ht' hg'_ne_pos
                  | Negative => rfl
                  | NonPolarized => exact absurd ht' hg'_ne_np
                have grank_bounds : g₁.rank ≥ 2 := by omega
                -- for i = g₁.rank - 1: b₀ - b_{i-1} = b₂ - b_{i+1}
                have hb0_b2_rank1 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
                    (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
                  have h := Sigma.b0_eq_b2_negative g₁.rank grank_bounds hg₁min
                    no_neg_gene_rank_g
                    (show g₁.rank - 2 ≤ g₁.rank - 1 from by omega)
                  simp only [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h
                  exact h
                -- for i = g₁.rank: b₀ - b_{i-1} = b₂ - b_{i+1}
                have hb0_b2_rank : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 =
                    (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 (g₁.rank + 1)).2 := by
                  have h := Sigma.b0_eq_b2_negative g₁.rank grank_bounds hg₁min
                    no_neg_gene_rank_g
                    (show g₁.rank - 1 ≤ g₁.rank - 1 from le_refl _)
                  simp only [show g₁.rank - 1 + 2 = g₁.rank + 1 from by omega] at h
                  exact h
                -- for i = g₁.rank: d₂ - d_{i+1} ≤ c₁ - c_i
                have hd2_c1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank + 1)).2 ≤
                    (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 :=
                  Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 hg₁_ge2
                -- for i = g₁.rank: d₂ - d_{i+1} ≤ d₀ - d_{i-1}
                have hd2_di1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank + 1)).2 ≤
                    (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                  hd2_c1_rank.trans hc1_ci_rank
                -- b_{g₁.rank} < d_{g₁.rank}
                have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
                    (Sigma.sigma Y.1 g₁.rank).2 := by
                  linarith [hd2_di1_rank1, hd0_di_rank1, hb0_b2_rank1, hd2_gt_b2]
                -- b_{g₁.rank + 1} < d_{g₁.rank + 1}
                have hb_lt_d_rank1 : (Sigma.sigma X.1 (g₁.rank + 1)).2 <
                    (Sigma.sigma Y.1 (g₁.rank + 1)).2 := by
                  linarith [hd2_di1_rank, hd0_di_rank, hb0_b2_rank, hd2_gt_b2]
                -- sigma Z i - sigma X.1 i equals the window difference from sigma_type2_same_rank
                have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
                    if i = g₁.rank then (1, 1)
                    else if i = g₁.rank - 1 then (1, 0)
                    else (0, 1) := by
                  -- Rewrite both sides using the Pi.Y2/Pi.X2 + rest decomposition;
                  -- the rest terms are equal so they cancel
                  rw [hZ_split, hX_split, add_sub_add_right_eq_sub]
                  -- Derive index bounds from hi_range to apply hwindow
                  have hibounds : g₁.rank - 1 ≤ i ∧ i ≤ g₁.rank + 1 := by
                    rcases hi_range with rfl | rfl | rfl <;> omega
                  -- Apply the window difference formula from sigma_type2_same_rank
                  rw [hwindow i hibounds.1 hibounds.2]
                  -- g₁.type = .Negative: rank is even so ↑g₁.rank - 1 is odd,
                  -- and hε₁ (type ≠ negOnePow(rank-1)•Negative) then gives type ≠ Positive
                  have htype_neg : g₁.type ≠ .Positive := by
                    intro h
                    apply hε₁
                    have h_odd : ¬ Even ((g₁.rank : ℤ) - 1) := by
                      simp [heven]
                    simp only [GeneType.negOnePow_smul, GeneType.neg_negative,
                                if_neg h_odd, h]
                  simp [if_neg htype_neg]
                rcases hi_range with hi | hi | hi
                · -- i = g₁.rank - 1
                  subst hi
                  have hZX_diff' : Sigma.sigma Z.val (g₁.rank - 1) -
                                  Sigma.sigma X.1.val (g₁.rank - 1) = (1, 0) := by
                    simpa [show g₁.rank - 1 ≠ g₁.rank from by omega] using hZX_diff
                  have hZX_diff' : Sigma.sigma Z.val (g₁.rank - 1) =
                                  Sigma.sigma X.1.val (g₁.rank - 1) + (1, 0) := by
                    have h := hZX_diff'; rw [← h]; ring
                  rw [hZX_diff']
                  constructor
                  · -- .1: (sigma X).1 + 1 ≤ (sigma Y).1 by ha_lt_c_rank1 and integrality
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val (g₁.rank - 1) X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val (g₁.rank - 1) Y.1.2
                    rw [hnX, hnY] at ha_lt_c_rank1 ⊢
                    simp only [Prod.fst_add] at ha_lt_c_rank1 ⊢
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank1)
                  · -- .2: (sigma X).2 + 0 ≤ (sigma Y).2 from hXY_i
                    simp only [Prod.snd_add]
                    linarith [hXY_i.2]
                · -- i = g₁.rank
                  subst hi
                  have hZX_diff' : Sigma.sigma Z.val g₁.rank -
                                   Sigma.sigma X.1.val g₁.rank = (1, 1) := by
                    simpa using hZX_diff
                  have hZX_diff' : Sigma.sigma Z.val g₁.rank =
                                   Sigma.sigma X.1.val g₁.rank + (1, 1) := by
                    have h := hZX_diff'; rw [← h]; ring
                  rw [hZX_diff']
                  constructor
                  · -- .1: (sigma X).1 + 1 ≤ (sigma Y).1 by ha_lt_c_rank and integrality
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val g₁.rank X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val g₁.rank Y.1.2
                    rw [hnX, hnY] at ha_lt_c_rank ⊢
                    simp only [Prod.fst_add] at ha_lt_c_rank ⊢
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank)
                  · -- .2: (sigma X).2 + 1 ≤ (sigma Y).2 by hb_lt_d_rank and integrality
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val g₁.rank X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val g₁.rank Y.1.2
                    rw [hnX, hnY] at hb_lt_d_rank ⊢
                    simp only [Prod.snd_add] at hb_lt_d_rank ⊢
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank)
                · -- i = g₁.rank + 1
                  subst hi
                  have hZX_diff' : Sigma.sigma Z.val (g₁.rank + 1) -
                                   Sigma.sigma X.1.val (g₁.rank + 1) = (0, 1) := by
                    simpa [show g₁.rank + 1 ≠ g₁.rank from by omega,
                           show g₁.rank + 1 ≠ g₁.rank - 1 from by omega] using hZX_diff
                  have hZX_diff' : Sigma.sigma Z.val (g₁.rank + 1) =
                                   Sigma.sigma X.1.val (g₁.rank + 1) + (0, 1) := by
                    have h := hZX_diff'; rw [← h]; ring
                  rw [hZX_diff']
                  constructor
                  · -- .1: (sigma X).1 + 0 ≤ (sigma Y).1 from hXY_i
                    simp only [Prod.fst_add]
                    linarith [hXY_i.1]
                  · -- .2: (sigma X).2 + 1 ≤ (sigma Y).2 by hb_lt_d_rank1 and integrality
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val (g₁.rank + 1) X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val (g₁.rank + 1) Y.1.2
                    rw [hnX, hnY] at hb_lt_d_rank1 ⊢
                    simp only [Prod.snd_add] at hb_lt_d_rank1 ⊢
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank1)
              · -- g₁.rank is odd
                have all_rel :
                    (Sigma.sigma X.1 g₁.rank).1       < (Sigma.sigma Y.1 g₁.rank).1       ∧
                    (Sigma.sigma X.1 (g₁.rank + 1)).1 < (Sigma.sigma Y.1 (g₁.rank + 1)).1 ∧
                    (Sigma.sigma X.1 g₁.rank).2       < (Sigma.sigma Y.1 g₁.rank).2       ∧
                    (Sigma.sigma X.1 (g₁.rank - 1)).2 < (Sigma.sigma Y.1 (g₁.rank - 1)).2 := by
                  -- Step 1: auxiliary inequalities for the .1 component
                  -- for i = g₁.rank: c₁ - c_{rank} ≤ d₀ - d_{rank-1}
                  have hc1_ci_rank : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
                      (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                    Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                  -- for i = g₁.rank: d₀ - d_{rank-1} ≤ b₀ - b_{rank-1}
                  have hd0_di_rank : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                      (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
                    have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                      sigma_zero_snd_eq X Y hXY.le
                    have hbm1_le_dm1 : (Sigma.sigma X.1 (g₁.rank - 1)).2 ≤
                        (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                      (le_iff_dominates.mp hXY.le (g₁.rank - 1)).2
                    linarith
                  -- b₀ - b_{j-1} = a₁ - a_j for all 1 ≤ j ≤ g₁.rank + 1
                  have hb0_bi : ∀ j, 1 ≤ j → j ≤ g₁.rank + 1 →
                      (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (j - 1)).2 =
                      (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 j).1 := by
                    intro j hj1 hj2
                    by_cases hj : j = 1
                    · subst hj; simp
                    · have hodd : Odd g₁.rank := Nat.not_even_iff_odd.mp heven
                      have hg₁_type : g₁.type = .Positive := by
                        have h_even : Even ((g₁.rank : ℤ) - 1) := by simp [hodd]
                        have hne_neg : g₁.type ≠ .Negative := by
                          intro h; apply hε₁
                          simp only [GeneType.negOnePow_smul, if_pos h_even, h]
                        cases ht : g₁.type with
                        | Positive => rfl
                        | Negative => exact absurd ht hne_neg
                        | NonPolarized => exact absurd ht hε
                      have no_neg_gene_rank_g : ∀g' ∈ X.1.val.support,
                          g'.rank = g₁.rank → g'.type = .Positive := by
                        intro g' hg'_supp hg'_rank
                        have hg'_ne_np : g'.type ≠ .NonPolarized :=
                          IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
                        have hg'_ne_neg : g'.type ≠ .Negative := by
                          intro hg'_neg
                          apply hXpn
                          exact ⟨g₁, g', hg'_rank.symm, hg₁_type, hg'_neg, hXg₁pos,
                                 Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp)⟩
                        cases ht' : g'.type with
                        | Positive => rfl
                        | Negative => exact absurd ht' hg'_ne_neg
                        | NonPolarized => exact absurd ht' hg'_ne_np
                      have h := Sigma.b0_bi_eq_a1_ai1 X.1.val X.1.2 (j - 1)
                          (fun g hg_supp hrank_le => by
                            have hg_rank_ge := hg₁min g hg_supp
                            have hg_rank_eq : g.rank = g₁.rank := by omega
                            exact no_neg_gene_rank_g g hg_supp hg_rank_eq)
                      rwa [Nat.sub_add_cancel hj1] at h
                  -- for j = g₁.rank: b₀ - b_{rank-1} = a₁ - a_{rank}
                  have hb0_bi_rank := hb0_bi g₁.rank (by omega) (by omega)
                  -- a_{g₁.rank} < c_{g₁.rank}
                  have ha_lt_c_rank : (Sigma.sigma X.1 g₁.rank).1 <
                      (Sigma.sigma Y.1 g₁.rank).1 := by
                    have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                      sigma_zero_fst_eq X Y hXY.le
                    linarith [hc1_ci_rank, hd0_di_rank, hb0_bi_rank, hstrict]
                  -- for i = g₁.rank + 1: c₁ - c_{rank+1} ≤ d₀ - d_{rank}
                  have hc1_ci_rank1 : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank + 1)).1 ≤
                      (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 g₁.rank).2 :=
                    Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                  -- for i = g₁.rank + 1: d₀ - d_{rank} ≤ b₀ - b_{rank}
                  have hd0_di_rank1 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                      (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 g₁.rank).2 := by
                    have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                      sigma_zero_snd_eq X Y hXY.le
                    have hb_le_d : (Sigma.sigma X.1 g₁.rank).2 ≤
                        (Sigma.sigma Y.1 g₁.rank).2 :=
                      (le_iff_dominates.mp hXY.le g₁.rank).2
                    linarith
                  -- for j = g₁.rank + 1: b₀ - b_{rank} = a₁ - a_{rank+1}
                  have hb0_bi_rank1 := hb0_bi (g₁.rank + 1) (by omega) (le_refl _)
                  simp only [show g₁.rank + 1 - 1 = g₁.rank from by omega] at hb0_bi_rank1
                  -- a_{g₁.rank + 1} < c_{g₁.rank + 1}
                  have ha_lt_c_rank1 : (Sigma.sigma X.1 (g₁.rank + 1)).1 <
                      (Sigma.sigma Y.1 (g₁.rank + 1)).1 := by
                    have ha0_eq : (Sigma.sigma X.1 0).1 = (Sigma.sigma Y.1 0).1 :=
                      sigma_zero_fst_eq X Y hXY.le
                    linarith [hc1_ci_rank1, hd0_di_rank1, hb0_bi_rank1, hstrict]
                  -- Step 2: auxiliary inequalities for the .2 component
                  -- d₂ - d_{rank} ≤ c₁ - c_{rank-1}  (from b2_bi_2_le_a1_ai at rank-1)
                  have hd2_c1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                      (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
                    have h : g₁.rank - 1 ≥ 2 := by
                      rcases Nat.even_or_odd g₁.rank with hev | ⟨k, hk⟩
                      · exact absurd hev heven
                      · omega
                    have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
                    rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
                  -- d₂ - d_{rank-1} ≤ c₁ - c_{rank-2}  (from b2_bi_2_le_a1_ai at rank-2)
                  have hd2_c1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                      (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 2)).1 := by
                    by_cases hrank3 : g₁.rank = 3
                    · simp [hrank3]
                    · have h : g₁.rank - 2 ≥ 2 := by
                        rcases Nat.even_or_odd g₁.rank with hev | ⟨k, hk⟩
                        · exact absurd hev heven
                        · omega
                      have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
                      rwa [show g₁.rank - 2 + 1 = g₁.rank - 1 from by omega] at this
                  -- chain to d₀ - d_{rank-2}
                  have hd2_di1_rank : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                      (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                    hd2_c1_rank.trans (Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega))
                  -- chain to d₀ - d_{rank-3}
                  have hd2_di1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                      (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 3)).2 :=
                    hd2_c1_rank1.trans (Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by
                      rcases Nat.even_or_odd g₁.rank with hev | ⟨k, hk⟩
                      · exact absurd hev heven
                      · omega))
                  -- b₀ - b_{rank-2} = b₂ - b_{rank}
                  have hb0_b2_rank : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
                      (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
                    have h := Sigma.b0_eq_b2_positive g₁.rank hg₁min
                      (show g₁.rank - 2 ≤ g₁.rank - 2 from by omega)
                    simp only [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h
                    exact h
                  -- b₀ - b_{rank-3} = b₂ - b_{rank-1}
                  have hb0_b2_rank1 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 3)).2 =
                      (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
                    have h := Sigma.b0_eq_b2_positive g₁.rank hg₁min
                      (show g₁.rank - 3 ≤ g₁.rank - 2 from by omega)
                    simp only [show g₁.rank - 3 + 2 = g₁.rank - 1 from by
                      rcases Nat.even_or_odd g₁.rank with hev | ⟨k, hk⟩
                      · exact absurd hev heven
                      · omega] at h
                    exact h
                  -- b_{rank} < d_{rank}
                  have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
                      (Sigma.sigma Y.1 g₁.rank).2 := by
                    have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                      sigma_zero_snd_eq X Y hXY.le
                    have hb_le_d : (Sigma.sigma X.1 (g₁.rank - 2)).2 ≤
                        (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                      (le_iff_dominates.mp hXY.le (g₁.rank - 2)).2
                    linarith [hd2_di1_rank, hb0_b2_rank, hd2_gt_b2]
                  -- b_{rank-1} < d_{rank-1}
                  have hb_lt_d_rank1 : (Sigma.sigma X.1 (g₁.rank - 1)).2 <
                      (Sigma.sigma Y.1 (g₁.rank - 1)).2 := by
                    have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                      sigma_zero_snd_eq X Y hXY.le
                    have hb_le_d : (Sigma.sigma X.1 (g₁.rank - 3)).2 ≤
                        (Sigma.sigma Y.1 (g₁.rank - 3)).2 :=
                      (le_iff_dominates.mp hXY.le (g₁.rank - 3)).2
                    linarith [hd2_di1_rank1, hb0_b2_rank1, hd2_gt_b2]
                  exact ⟨ha_lt_c_rank, ha_lt_c_rank1, hb_lt_d_rank, hb_lt_d_rank1⟩
                obtain ⟨ha_lt_c_rank, ha_lt_c_rank1, hb_lt_d_rank, hb_lt_d_rank1⟩ := all_rel
                have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
                    if i = g₁.rank then (1, 1)
                    else if i = g₁.rank - 1 then (0, 1)
                    else (1, 0) := by
                  rw [hZ_split, hX_split, add_sub_add_right_eq_sub]
                  have hibounds : g₁.rank - 1 ≤ i ∧ i ≤ g₁.rank + 1 := by
                    rcases hi_range with rfl | rfl | rfl <;> omega
                  rw [hwindow i hibounds.1 hibounds.2]
                  have htype_pos : g₁.type = .Positive := by
                    have h_even : Even ((g₁.rank : ℤ) - 1) := by
                      have : Odd g₁.rank := by simp_all
                      simp [this]
                    have hne_neg : g₁.type ≠ .Negative := by
                      intro h
                      apply hε₁
                      simp only [GeneType.negOnePow_smul, if_pos h_even, h]
                    cases htype : g₁.type with
                    | Positive => rfl
                    | Negative => exact absurd htype hne_neg
                    | NonPolarized => exact absurd htype hε
                  simp [htype_pos]
                rcases hi_range with hi | hi | hi
                · -- i = g₁.rank - 1, diff = (0, 1)
                  subst hi
                  have hZX_diff' : Sigma.sigma Z.val (g₁.rank - 1) -
                                   Sigma.sigma X.1.val (g₁.rank - 1) = (0, 1) := by
                    simpa [show g₁.rank - 1 ≠ g₁.rank from by omega] using hZX_diff
                  have hZX_diff' : Sigma.sigma Z.val (g₁.rank - 1) =
                                   Sigma.sigma X.1.val (g₁.rank - 1) + (0, 1) := by
                    have h := hZX_diff'; rw [← h]; ring
                  rw [hZX_diff']
                  constructor
                  · -- .1: (sigma X).1 + 0 ≤ (sigma Y).1 from hXY_i
                    simp only [Prod.fst_add]
                    linarith [hXY_i.1]
                  · -- .2: (sigma X).2 + 1 ≤ (sigma Y).2 by hb_lt_d_rank1 and integrality
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val (g₁.rank - 1) X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val (g₁.rank - 1) Y.1.2
                    rw [hnX, hnY] at hb_lt_d_rank1 ⊢
                    simp only [Prod.snd_add] at hb_lt_d_rank1 ⊢
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank1)
                · -- i = g₁.rank, diff = (1, 1)
                  subst hi
                  have hZX_diff' : Sigma.sigma Z.val g₁.rank -
                                   Sigma.sigma X.1.val g₁.rank = (1, 1) := by
                    simpa using hZX_diff
                  have hZX_diff' : Sigma.sigma Z.val g₁.rank =
                                   Sigma.sigma X.1.val g₁.rank + (1, 1) := by
                    have h := hZX_diff'; rw [← h]; ring
                  rw [hZX_diff']
                  constructor
                  · -- .1: (sigma X).1 + 1 ≤ (sigma Y).1 by ha_lt_c_rank and integrality
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val g₁.rank X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val g₁.rank Y.1.2
                    rw [hnX, hnY] at ha_lt_c_rank ⊢
                    simp only [Prod.fst_add] at ha_lt_c_rank ⊢
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank)
                  · -- .2: (sigma X).2 + 1 ≤ (sigma Y).2 by hb_lt_d_rank and integrality
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val g₁.rank X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val g₁.rank Y.1.2
                    rw [hnX, hnY] at hb_lt_d_rank ⊢
                    simp only [Prod.snd_add] at hb_lt_d_rank ⊢
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hb_lt_d_rank)
                · -- i = g₁.rank + 1, diff = (1, 0)
                  subst hi
                  have hZX_diff' : Sigma.sigma Z.val (g₁.rank + 1) -
                                   Sigma.sigma X.1.val (g₁.rank + 1) = (1, 0) := by
                    simpa [show g₁.rank + 1 ≠ g₁.rank from by omega,
                           show g₁.rank + 1 ≠ g₁.rank - 1 from by omega] using hZX_diff
                  have hZX_diff' : Sigma.sigma Z.val (g₁.rank + 1) =
                                   Sigma.sigma X.1.val (g₁.rank + 1) + (1, 0) := by
                    have h := hZX_diff'
                    rw [← h]; ring
                  rw [hZX_diff']
                  constructor
                  · -- .1: (sigma X).1 + 1 ≤ (sigma Y).1 by ha_lt_c_rank1 and integrality
                    obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val (g₁.rank + 1) X.1.2
                    obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val (g₁.rank + 1) Y.1.2
                    rw [hnX, hnY] at ha_lt_c_rank1 ⊢
                    simp only [Prod.fst_add] at ha_lt_c_rank1 ⊢
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp ha_lt_c_rank1)
                  · -- .2: (sigma X).2 + 0 ≤ (sigma Y).2 from hXY_i
                    simp only [Prod.snd_add]
                    linarith [hXY_i.2]
          -/
        · -- Case 4: g₁ appears with multiplicity 1 in X
          have hg₁_one : X.1.val g₁ = 1 := by omega
          have hprime_rank_ne_zero : prime^[g₁.rank] X.1.val ≠ 0 := by
            -- If prime^[g₁.rank] X = 0, we show X = single g₁ 1 and derive a contradiction.
            have hX_eq_g₁ : prime^[g₁.rank] X.1.val = 0 → X.1.val = Finsupp.single g₁ 1 := by
              intro hzero
              -- All genes in X have rank ≤ g₁.rank (prime_iterate_eq_zero_rank_le)
              have hrank_le : ∀ g ∈ X.1.val.support, g.rank ≤ g₁.rank :=
                fun g hg => prime_iterate_eq_zero_rank_le.2 hzero g hg
              -- Combined with hg₁min (minimal rank ≥ g₁.rank): rank = g₁.rank exactly
              have hrank_eq : ∀ g ∈ X.1.val.support, g.rank = g₁.rank :=
                fun g hg => le_antisymm (hrank_le g hg) (hg₁min g hg)
              -- All genes have type = g₁.type (else hXpn gives a pos-neg pair of equal rank)
              have htype_eq : ∀ g ∈ X.1.val.support, g.type = g₁.type := by
                intro g hg
                have hg_pol : g.type ≠ .NonPolarized :=
                  IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g hg
                have hg₁_pol : g₁.type ≠ .NonPolarized :=
                  IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
                by_contra hne
                apply hXpn
                cases ht : g.type with
                | NonPolarized => exact absurd ht hg_pol
                | Positive =>
                  have hg₁_neg : g₁.type = .Negative := by
                    cases ht₁ : g₁.type with
                    | NonPolarized => exact absurd ht₁ hg₁_pol
                    | Positive => exact False.elim (hne (ht.trans ht₁.symm))
                    | Negative => rfl
                  exact ⟨g, g₁, hrank_eq g hg, ht, hg₁_neg,
                    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg), hXg₁pos⟩
                | Negative =>
                  have hg₁_pos : g₁.type = .Positive := by
                    cases ht₁ : g₁.type with
                    | NonPolarized => exact absurd ht₁ hg₁_pol
                    | Negative => exact False.elim (hne (ht.trans ht₁.symm))
                    | Positive => rfl
                  exact ⟨g₁, g, (hrank_eq g hg).symm, hg₁_pos, ht,
                    hXg₁pos, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)⟩
              -- Every gene in the support equals g₁ (same rank and type)
              have hall_g₁ : ∀ g ∈ X.1.val.support, g = g₁ :=
                fun g hg => Gene.ext (hrank_eq g hg) (htype_eq g hg)
              -- X.1.val = single g₁ 1 since support ⊆ {g₁} and X.1.val g₁ = 1
              ext g
              rcases eq_or_ne g g₁ with rfl | hne
              · simp [hg₁_one]
              · have hg_zero : X.1.val g = 0 := by
                  by_contra h
                  exact hne (hall_g₁ g (Finsupp.mem_support_iff.mpr h))
                simp [hg_zero, hne]
            intro hzero
            have hX_rank_eq : X.1.val.rank = g₁.rank := by
              rw [hX_eq_g₁ hzero, rank_single, one_smul]
            have hYX_rank : Y.1.val.rank = X.1.val.rank := by
              simp only [Y.2, X.2]
            have hY_maxrank : Y.1.val.maxRank = X.1.val.maxRank := by
              have hX_maxrank : X.1.val.maxRank = g₁.rank := by
                rw [hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene, maxRank_ofRank]
              rw [hX_maxrank]
              apply Nat.le_antisymm
              · -- Upper: Y.maxRank ≤ Y.rank = X.rank = g₁.rank
                calc Y.1.val.maxRank
                    ≤ Y.1.val.rank := maxRank_le_rank _
                  _ = X.1.val.rank := hYX_rank
                  _ = g₁.rank      := hX_rank_eq
              · -- Lower: if Y.maxRank < g₁.rank then prime^[g₁.rank-1] Y = 0,
                --   but X ≤ Y forces sigma(X, g₁.rank-1) ≤ 0, contradicting
                --   prime^[g₁.rank-1] X = ofRank 1 g₁.type ≠ 0
                by_contra hlt
                push Not at hlt
                have hY_zero : prime^[g₁.rank - 1] Y.1.val = 0 :=
                  prime_iterate_zero_of_maxRank_le (by omega)
                have hX_ne : prime^[g₁.rank - 1] X.1.val ≠ 0 := by
                  rw [hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene, prime_iterate_ofRank,
                      show g₁.rank - (g₁.rank - 1) = 1 from by omega]
                  simp [Gene.ofRank_is_gene]
                have hle := (le_iff_dominates.mp hXY.le) (g₁.rank - 1)
                simp only [hY_zero, map_zero] at hle
                obtain ⟨n, hn⟩ := Sigma.sigma_isNat X.1.val (g₁.rank - 1) X.1.2
                have hzero_sig : signature (prime^[g₁.rank - 1] X.1.val) = 0 := by
                  simp only [Sigma.sigma] at hn
                  rw [hn] at hle ⊢
                  obtain ⟨h1, h2⟩ := Prod.le_def.mp hle
                  simp at h1 h2
                  have : ((0, 0) : ℚ × ℚ) = 0 := rfl
                  simp [h1, h2]
                exact hX_ne (signature_eq_zero hzero_sig)
            -- Re-establish X.maxRank = g₁.rank (local to hY_maxrank's proof, so re-derive)
            have hX_maxrank : X.1.val.maxRank = g₁.rank := by
              rw [hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene, maxRank_ofRank]
            -- Y.maxRank = g₁.rank
            have hY_maxrank_val : Y.1.val.maxRank = g₁.rank := hY_maxrank.trans hX_maxrank
            -- Y.rank = Y.maxRank (both equal g₁.rank)
            have hY_rank_maxrank : Y.1.val.rank = Y.1.val.maxRank :=
              (hYX_rank.trans hX_rank_eq).trans hY_maxrank_val.symm
            -- Y = single g₂ 1 for some g₂ with g₂.rank = g₁.rank
            obtain ⟨g₂, hg₂_maxrank, hY_eq⟩ := rank_eq_maxRank_single hY_rank_maxrank
              (by rw [hY_maxrank_val]; linarith)
            have hg₂_rank : g₂.rank = g₁.rank := hg₂_maxrank.trans hY_maxrank_val
            -- g₁ and g₂ are polarized (both chromosomes are in Pi)
            have hg₁_pol : g₁.type ≠ .NonPolarized :=
              IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
            have hg₂_in_supp : g₂ ∈ Y.1.val.support := by rw [hY_eq]; simp
            have hg₂_pol : g₂.type ≠ .NonPolarized :=
              IsPolarized_def'.mp (mem_Pi_iff.mp Y.1.2) g₂ hg₂_in_supp
            rcases eq_or_ne g₁ g₂ with rfl | hne
            · -- g₁ = g₂ ⟹ X.1.val = Y.1.val ⟹ X.1 = Y.1, contradicting X.1 < Y.1
              exact absurd
                (Subtype.val_injective ((hX_eq_g₁ hzero).trans hY_eq.symm))
                (ne_of_lt hXY)
            · -- g₁ ≠ g₂ but g₁.rank = g₂.rank ⟹ g₁.type ≠ g₂.type
              have htype_ne : g₁.type ≠ g₂.type := fun heq =>
                hne (Gene.ext hg₂_rank.symm heq)
              -- sigma inequality at k = g₁.rank - 1
              have hle : signature (prime^[g₁.rank - 1] X.1.val) ≤
                         signature (prime^[g₁.rank - 1] Y.1.val) :=
                (le_iff_dominates.mp hXY.le) (g₁.rank - 1)
              rw [hX_eq_g₁ hzero, ← Gene.ofRank_eq_gene, prime_iterate_ofRank,
                  show g₁.rank - (g₁.rank - 1) = 1 from by omega] at hle
              rw [hY_eq, ← Gene.ofRank_eq_gene, prime_iterate_ofRank,
                  show g₂.rank - (g₁.rank - 1) = 1 from by rw [hg₂_rank]; omega] at hle
              -- hle : signature(ofRank 1 g₁.type) ≤ signature(ofRank 1 g₂.type)
              -- Both types are polarized and differ ⟹ one is Positive, other Negative
              -- ⟹ (1,0) ≤ (0,1) or (0,1) ≤ (1,0), both impossible
              cases ht₁ : g₁.type with
              | NonPolarized => exact hg₁_pol ht₁
              | Positive =>
                cases ht₂ : g₂.type with
                | NonPolarized => exact hg₂_pol ht₂
                | Positive => exact htype_ne (ht₁.trans ht₂.symm)
                | Negative =>
                  simp only [ht₁, ht₂, signature_ofRank_one_positive,
                    signature_ofRank_one_negative] at hle
                  linarith [(Prod.le_def.mp hle).1]
              | Negative =>
                cases ht₂ : g₂.type with
                | NonPolarized => exact hg₂_pol ht₂
                | Positive =>
                  simp only [ht₁, ht₂, signature_ofRank_one_positive,
                    signature_ofRank_one_negative] at hle
                  linarith [(Prod.le_def.mp hle).2]
                | Negative => exact htype_ne (ht₁.trans ht₂.symm)
          have hg₂ : ∃ g₂ : Gene,
              0 < X.1.val g₂ ∧
              g₁.rank < g₂.rank ∧
              ∀ g' : Gene, 0 < X.1.val g' → g₁.rank < g'.rank → g₂.rank ≤ g'.rank := by
            -- The filter set S = { g ∈ X.1.val.support | g₁.rank < g.rank } is nonempty.
            -- Since prime^[g₁.rank] X.1.val ≠ 0, pick any g' in its support.
            -- By prime_iterate_coeff, (prime^[g₁.rank] X.1.val),
            --    g' = X.1.val ⟨g'.rank + g₁.rank, ...⟩ > 0,
            -- so ⟨g'.rank + g₁.rank, g'.type, _⟩ ∈ X.1.val.support with rank > g₁.rank.
            have hSne : (X.1.val.support.filter (fun g => g₁.rank < g.rank)).Nonempty := by
              -- Extract a gene g' from the nonempty support of prime^[g₁.rank] X.1.val
              obtain ⟨g', hg'⟩ := Finsupp.support_nonempty_iff.mpr hprime_rank_ne_zero
              -- Lift g' to a gene h of rank g'.rank + g₁.rank in X.1.val
              let h : Gene := ⟨g'.rank + g₁.rank, g'.type, Nat.le_add_right_of_le g'.rank_pos⟩
              refine ⟨h, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
              · -- h ∈ X.1.val.support: prime_iterate_coeff links (prime^[g₁.rank] X.1.val) g'
                --   = X.1.val h ≠ 0
                rw [Finsupp.mem_support_iff]
                have hne := Finsupp.mem_support_iff.mp hg'
                rwa [prime_iterate_coeff] at hne
              · -- g₁.rank < h.rank = g'.rank + g₁.rank, since g'.rank ≥ 1
                change g₁.rank < g'.rank + g₁.rank
                have := g'.rank_pos; omega
            -- Apply Finset.exists_min_image on S w.r.t. Gene.rank to get the minimal element g₂.
            obtain ⟨g₂, hg₂S, hg₂min⟩ := Finset.exists_min_image _ Gene.rank hSne
            rw [Finset.mem_filter] at hg₂S
            exact ⟨g₂, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₂S.1),
              hg₂S.2,
              fun g' hg'pos hg'rank => hg₂min g'
                (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hg'pos.ne', hg'rank⟩)⟩
          obtain ⟨g₂, hg₂pos, hg₂rank, hg₂min⟩ := hg₂
          by_cases hε₂ : g₂.type = -g₁.type
          · sorry
            /-
            -- Case 4a: g₂.type = -g₁.type (opposite type families)
            -- Mutation: Pi.Primitive.type1 with ε = g₁.type, m = g₁.rank, k = g₂.rank
            -- Source (Pi.X1): Gene.ofRank m ε + Gene.ofRank k (-ε) = single g₁ 1 + single g₂ 1
            -- Target (Pi.Y1): Gene.ofRank (m-1) (-ε) + Gene.ofRank (k+1) ε
            let ε := g₁.type
            have hε : ε ≠ .NonPolarized :=
              IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁ (Finsupp.mem_support_iff.mpr hXg₁)
            have hle : g₁.rank ≤ g₂.rank := le_of_lt hg₂rank
            -- ofRank g₁.rank ε = single g₁ 1
            have hg₁_ofRank : Gene.ofRank g₁.rank ε = Finsupp.single g₁ 1 :=
              Gene.ofRank_eq_gene
            -- ofRank g₂.rank (-ε) = single g₂ 1  (since g₂.type = -ε by hε₂)
            have hg₂_ofRank : Gene.ofRank g₂.rank (-ε) = Finsupp.single g₂ 1 := by
              have h := @Gene.ofRank_eq_gene g₂; rw [hε₂] at h; exact h
            -- The type1 source chromosome equals single g₁ 1 + single g₂ 1
            have hsrc_val : (Pi.X1 hε hle g₁.rank_pos : Chromosome) =
                Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
              simp only [Pi.X1_eq]; rw [hg₁_ofRank, hg₂_ofRank]
            -- src ≤ X.1.val pointwise
            have hsrc_le : ∀ g : Gene,
                (Pi.X1 hε hle g₁.rank_pos : Chromosome) g ≤ X.1.val g := by
              have hne : g₁ ≠ g₂ := fun h => absurd hg₂rank (h ▸ lt_irrefl _)
              intro gen
              rw [hsrc_val, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
              rcases eq_or_ne gen g₁ with rfl | hng₁
              · -- gen = g₁: 1 + 0 ≤ X.1.val g₁ = 1
                simp [Ne.symm hne, hg₁_one]
              · rcases eq_or_ne gen g₂ with rfl | hng₂
                · -- gen = g₂: 0 + 1 ≤ X.1.val g₂
                  simp only [Ne.symm hng₁]
                  exact hg₂pos
                · -- gen ∉ {g₁, g₂}: 0 ≤ X.1.val gen
                  simp [Ne.symm hng₁, Ne.symm hng₂]
            -- rest = X.1.val − src, still in Pi
            let rest : Pi :=
              ⟨X.1.val - (Pi.X1 hε hle g₁.rank_pos : Chromosome),
                Variety.sub_mem_Pi _ X.1.2⟩
            -- X.1 decomposes as src + rest
            have hdecomp : X.1 = Pi.X1 hε hle g₁.rank_pos + rest :=
              Subtype.val_injective
                (Finsupp.ext fun g => (add_tsub_cancel_of_le (hsrc_le g)).symm)
            -- Z is the type1 mutation result
            let Z : Pi := Pi.Y1 hε hle g₁.rank_pos + rest
            -- Construct the Pi-step
            have hstep : Pi.Step X.1 Z :=
              hdecomp.symm ▸ Pi.Step.mk
                (Pi.X1 hε hle g₁.rank_pos)
                (Pi.Y1 hε hle g₁.rank_pos)
                rest
                (Pi.Primitive.type1 ε hε hle g₁.rank_pos)
            exact ⟨Z, hstep, by
              change Z.val ≤ Y.1.val
              rw [le_iff_dominates]
              intro i
              change Sigma.sigma Z.val i ≤ Sigma.sigma Y.1.val i
              have hXY_i : Sigma.sigma X.1.val i ≤ Sigma.sigma Y.1.val i :=
                le_iff_dominates.mp hXY.le i
              have hZ_split : Sigma.sigma Z.val i =
                  Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val i + Sigma.sigma rest.val i := by
                change Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos + rest : Variety.Pi).val i = _
                simp only [AddSubmonoid.coe_add, Sigma.sigma, iterate_map_add, map_add]
              have hX_split : Sigma.sigma X.1.val i =
                  Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val i + Sigma.sigma rest.val i := by
                have hval : X.1.val = (Pi.X1 hε hle g₁.rank_pos).val + rest.val := by
                  have h := congrArg Subtype.val hdecomp
                  simp only [AddSubmonoid.coe_add] at h; exact h
                simp only [hval, Sigma.sigma, iterate_map_add, map_add]
              -- All conditions on the relationship between X and Y
              have hXY_sigma :
                  (∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
                    Sigma.sigma X.1.val j + (Gene.ofRank 1 ε).signature ≤
                    Sigma.sigma Y.1.val j) ∧
                  (∀ j, ¬(g₁.rank ≤ j ∧ j ≤ g₂.rank) →
                    Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val j =
                    Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val j) := by
                have h_outside_range : ∀ j, ¬(g₁.rank ≤ j ∧ j ≤ g₂.rank) →
                    Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val j =
                    Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val j := by
                    intro j hj
                    rcases not_and_or.mp hj with h | h
                    · -- j < g₁.rank: signature equality by mutation_type1_signature_eq
                      simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add,
                                 prime_iterate_ofRank]
                      rw [show g₁.rank - 1 - j = g₁.rank - j - 1 from by omega,
                          show g₂.rank + 1 - j = g₂.rank - j + 1 from by omega]
                      exact (mutation_type1_signature_eq hε (by omega) (by omega)).symm
                    · -- j > g₂.rank: both sigma values are 0
                      simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add,
                                 prime_iterate_ofRank,
                                 show g₁.rank - j = 0 from by omega,
                                 show g₂.rank - j = 0 from by omega,
                                 show g₁.rank - 1 - j = 0 from by omega,
                                 show g₂.rank + 1 - j = 0 from by omega,
                                 Gene.ofRank_zero, map_zero, add_zero]
                by_cases heven : Even g₁.rank
                · -- g₁.rank is even
                  have hε_neg : ε = .Negative := by
                    have hne_pos : ε ≠ .Positive := by
                      intro h; apply hε₁
                      have h_odd : ¬ Even ((g₁.rank : ℤ) - 1) := by
                        obtain ⟨r, hr⟩ := heven; intro ⟨k, hk⟩; omega
                      simp only [GeneType.negOnePow_smul, GeneType.neg_negative, if_neg h_odd]
                      rw [← h]
                    cases ht : ε with
                    | Positive => exact absurd ht hne_pos
                    | Negative => rfl
                    | NonPolarized => exact absurd ht hε
                  -- b_{rank} < d_{rank}
                  have hb_lt_d_rank : (Sigma.sigma X.1 g₁.rank).2 <
                      (Sigma.sigma Y.1 g₁.rank).2 := by
                    have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                      linarith [sigma_zero_fst_eq X Y hXY.le]
                    have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
                      (le_iff_dominates.mp hXY.le 1).2
                    have hb12_eq : (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 =
                      (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                      -- g₁.type is in the Positive family (not Negative by hε₁,
                       --not NonPolarized by polarization)
                      have hpol := IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁
                        (Finsupp.mem_support_iff.mpr hXg₁)
                      have hg₁_pos_type : g₁.type =
                          Int.negOnePow (g₁.rank - 1) • GeneType.Positive := by
                        simp only [GeneType.negOnePow_smul,
                                   GeneType.neg_positive,
                                   GeneType.neg_negative]
                          at hε₁ ⊢
                        split_ifs with heven
                        · simp only [if_pos heven] at hε₁
                          cases ht : g₁.type with
                          | Positive => rfl
                          | Negative => exact absurd ht hε₁
                          | NonPolarized => exact absurd ht hpol
                        · simp only [if_neg heven] at hε₁
                          cases ht : g₁.type with
                          | Positive => exact absurd ht hε₁
                          | Negative => rfl
                          | NonPolarized => exact absurd ht hpol
                      -- Gene.ofRankAlt g₁.rank Positive = single g₁ 1
                      have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive =
                           Finsupp.single g₁ 1 := by
                        rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
                        congr 1; exact Gene.ext rfl hg₁_pos_type.symm
                      -- Apply x_side_equalities at j = 1 (odd),
                        -- using g₁ as the minimal Positive-family gene
                      have h := x_side_equalities hXpn hg₁_ofRankAlt hXg₁pos
                        (fun g' _ hg'_pos => hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                        (show 1 < g₁.rank from hg₁_ge2)
                      simp only [show ¬Even 1 from by norm_num, ↓reduceIte] at h
                      exact h
                    have hd12_le : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 ≤
                        (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
                      have h := Sigma.cond_15_6_compare_k_to_0 Y.1.val (2 - 1) Y.1.2
                      simp only [show ¬Even (2 - 1 : ℕ) from by norm_num, if_false] at h
                      exact h
                    have hb12_gt_d12 : (Sigma.sigma Y.1 1).2 - (Sigma.sigma Y.1 2).2 <
                      (Sigma.sigma X.1 1).2 - (Sigma.sigma X.1 2).2 := by
                      linarith [hb12_eq, hstrict, hd12_le]
                    have hd2_gt_b2 : (Sigma.sigma X.1 2).2 < (Sigma.sigma Y.1 2).2 := by
                      linarith [hb1_le_d1, hb12_gt_d12]
                    have no_neg_gene_rank_g : ∀ g' ∈ X.1.val.support,
                        g'.rank = g₁.rank → g'.type = .Negative := by
                      intro g' hg'_supp hg'_rank
                      have hg'_ne_np := IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g' hg'_supp
                      have hg'_ne_pos : g'.type ≠ .Positive := fun hg'_pos => hXpn
                        ⟨g', g₁, hg'_rank, hg'_pos, hε_neg,
                         Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'_supp), hXg₁pos⟩
                      cases ht' : g'.type with
                      | Positive => exact absurd ht' hg'_ne_pos
                      | Negative => rfl
                      | NonPolarized => exact absurd ht' hg'_ne_np
                    have hc1_ci_rank1 : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 ≤
                        (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                      Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                    have hb0_b2_rank1 : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 =
                        (Sigma.sigma X.1 2).2 - (Sigma.sigma X.1 g₁.rank).2 := by
                      have h := Sigma.b0_eq_b2_negative g₁.rank hg₁_ge2 hg₁min
                        no_neg_gene_rank_g (show g₁.rank - 2 ≤ g₁.rank - 1 from by omega)
                      simp only [show g₁.rank - 2 + 2 = g₁.rank from by omega] at h; exact h
                    have hd0_di_rank1 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 ≤
                        (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 2)).2 := by
                      have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                        sigma_zero_snd_eq X Y hXY.le
                      have hbm2_le_dm2 : (Sigma.sigma X.1 (g₁.rank - 2)).2 ≤
                          (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                        (le_iff_dominates.mp hXY.le (g₁.rank - 2)).2
                      linarith
                    have hd2_c1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                        (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 (g₁.rank - 1)).1 := by
                      by_cases hrank2 : g₁.rank = 2
                      · simp only [hrank2, sub_self, le_refl]
                      · have h : g₁.rank - 1 ≥ 2 := by omega
                        have := Sigma.b2_bi_2_le_a1_ai Y.1.val Y.1.2 h
                        rwa [show g₁.rank - 1 + 1 = g₁.rank from by omega] at this
                    have hd2_di1_rank1 : (Sigma.sigma Y.1 2).2 - (Sigma.sigma Y.1 g₁.rank).2 ≤
                        (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 2)).2 :=
                      hd2_c1_rank1.trans hc1_ci_rank1
                    linarith [hd2_di1_rank1, hd0_di_rank1, hb0_b2_rank1, hd2_gt_b2]
                  have hdi_sub_le_bi_sub : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank - 1 →
                      (Sigma.sigma Y.1 j).2 - (Sigma.sigma Y.1 (j + 1)).2 ≤
                      (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 := by
                    intro j hj1 hj2
                    by_cases hjeven : Even j
                    · -- j is even
                      have hdj_le_d0 : (Sigma.sigma Y.1 j).2 - (Sigma.sigma Y.1 (j + 1)).2 ≤
                          (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 1).2 := by
                        have key : ∀ n : ℕ,
                            (Sigma.sigma Y.1.val (n + n)).2 -
                            (Sigma.sigma Y.1.val (n + n + 1)).2 ≤
                            (Sigma.sigma Y.1.val 0).2 - (Sigma.sigma Y.1.val 1).2 := by
                          intro n
                          induction n with
                          | zero => simp
                          | succ n ih =>
                            have h1 : (Sigma.drop Y.1.val (n + n + 2)).2 ≤
                                (Sigma.drop Y.1.val (n + n + 1)).1 := by
                              have h := Sigma.cond_15_7_drop Y.1.val (n + n + 1) Y.1.2
                              rw [if_neg (fun heven =>
                                (Nat.even_add_one.mp heven) ⟨n, rfl⟩)] at h; exact h
                            have h2 : (Sigma.drop Y.1.val (n + n + 1)).1 ≤
                                (Sigma.drop Y.1.val (n + n)).2 := by
                              have h := Sigma.cond_15_7_drop Y.1.val (n + n) Y.1.2
                              rw [if_pos ⟨n, rfl⟩] at h; exact h
                            simp only [Sigma.drop_snd, Sigma.drop_fst] at h1 h2
                            rw [show n + 1 + (n + 1) = n + n + 2 from by omega]; linarith
                        obtain ⟨m, hm⟩ := hjeven
                        rw [hm]; exact key m
                      have hd0_le_b0 : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 1).2 ≤
                          (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 := by
                        have hb0_eq_d0 := sigma_zero_snd_eq X Y hXY.le
                        have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
                          (le_iff_dominates.mp hXY.le 1).2
                        linarith
                      have hb0_eq_bj : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                          (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 := by
                        have hLHS : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              0 < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Negative),
                            (X.1.val g : ℚ) := by
                          have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                          have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                          simp only [Function.iterate_zero, id] at h1 h2
                          exact h1.trans h2
                        have hRHS : (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              j < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Negative),
                            (X.1.val g : ℚ) := by
                          have h1 := Sigma.sigma_snd_diff X.1.val j X.1.2
                          have h2 := Sigma.prime_iterate_sum_eq X.1.val j GeneType.Negative
                          simp only [show Int.negOnePow (j : ℤ) = 1 from
                            Int.negOnePow_even _ (by exact_mod_cast hjeven),
                            one_smul] at h2
                          exact h1.trans h2
                        have hfilter_eq :
                            X.1.val.support.filter (fun g =>
                              0 < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Negative) =
                            X.1.val.support.filter (fun g =>
                              j < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Negative) := by
                          ext g
                          simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                          constructor
                          · rintro ⟨hg_supp, _, hg_type⟩
                            refine ⟨hg_supp, ?_, hg_type⟩
                            have hmin := hg₁min g (Finsupp.mem_support_iff.mpr hg_supp)
                            rcases eq_or_lt_of_le hmin with h_eq | h_lt
                            · have halttype :
                                  Sigma.altType g.rank GeneType.Negative =
                                  GeneType.Positive := by
                                rw [show g.rank = g₁.rank from h_eq.symm,
                                    Sigma.altType_even g₁.rank heven,
                                    GeneType.neg_negative]
                              rw [halttype] at hg_type
                              exact absurd hXpn (not_not.mpr
                                ⟨g, g₁, h_eq.symm, hg_type, hε_neg,
                                 Nat.pos_of_ne_zero hg_supp, hXg₁pos⟩)
                            · exact by
                                have := hg₂min g (Nat.pos_of_ne_zero hg_supp) h_lt
                                omega
                          · rintro ⟨hg_supp, hg_rank, hg_type⟩
                            exact ⟨hg_supp, g.rank_pos, hg_type⟩
                        rw [hLHS, hRHS, hfilter_eq]
                      linarith
                    · -- j is odd
                      have hdj_le_c01 : (Sigma.sigma Y.1 j).2 - (Sigma.sigma Y.1 (j + 1)).2 ≤
                          (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
                        simpa [hjeven] using Sigma.cond_15_6_compare_k_to_0 Y.1.val j Y.1.2
                      have hc01_le_a01_sub1 : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 ≤
                          (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 := by
                        have ha0_eq_c0 := sigma_zero_fst_eq X Y hXY.le
                        have ha : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                          linarith [sigma_zero_fst_eq X Y hXY.le]
                        obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val 1 X.1.2
                        obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val 1 Y.1.2
                        have hX1 : (Sigma.sigma X.1 1).1 = ↑nX.1 := congr_arg Prod.fst hnX
                        have hY1 : (Sigma.sigma Y.1 1).1 = ↑nY.1 := congr_arg Prod.fst hnY
                        have hlt : (↑nX.1 : ℚ) < ↑nY.1 := by linarith
                        have hlt_nat : nX.1 < nY.1 := by exact_mod_cast hlt
                        have hle : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 := by
                          exact_mod_cast (by omega : nX.1 + 1 ≤ nY.1)
                        linarith
                      have ha01_sub1_eq_bm : (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 =
                          (Sigma.sigma X.1 (g₁.rank - 1)).2 - (Sigma.sigma X.1 g₁.rank).2 - 1 := by
                        have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                          rw [Sigma.altType_even g₁.rank heven, GeneType.neg_positive]; exact hε_neg
                        have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive =
                            Finsupp.single g₁ 1 := by
                          rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
                          congr 1; exact Gene.ext rfl hg₁_altType.symm
                        have h := x_side_equalities hXpn hg₁_ofRankAlt hXg₁pos
                          (fun g' _ hg' => hg₁min g' (Finsupp.mem_support_iff.mpr hg'.ne'))
                          (show g₁.rank - 1 < g₁.rank from by omega)
                        rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
                        have hodd : ¬Even (g₁.rank - 1) := by
                          obtain ⟨r, hr⟩ := heven; intro ⟨s, hs⟩; omega
                        simp only [hodd, if_false] at h
                        linarith
                      have hbm_sub1_eq_am : (Sigma.sigma X.1 (g₁.rank - 1)).2 -
                          (Sigma.sigma X.1 g₁.rank).2 - 1 =
                          (Sigma.sigma X.1 g₁.rank).1 - (Sigma.sigma X.1 (g₁.rank + 1)).1 := by
                        -- Step 1: rewrite LHS drop via sigma_snd_diff +
                        -- prime_iterate_sum_neg_eq
                        have hLHS : (Sigma.sigma X.1 (g₁.rank - 1)).2 -
                            (Sigma.sigma X.1 g₁.rank).2 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              g₁.rank - 1 < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive),
                            (X.1.val g : ℚ) := by
                          have h := Sigma.sigma_snd_diff X.1.val (g₁.rank - 1) X.1.2
                          rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
                          rw [h, Sigma.prime_iterate_sum_neg_eq X.1.val (g₁.rank - 1)
                                  (show ¬Even (g₁.rank - 1) from by
                                    obtain ⟨r, hr⟩ := heven
                                    intro ⟨s, hs⟩; omega)]
                          rfl
                        -- Step 2: rewrite RHS drop via sigma_fst_diff + prime_iterate_sum_pos_eq
                        have hRHS : (Sigma.sigma X.1 g₁.rank).1 -
                            (Sigma.sigma X.1 (g₁.rank + 1)).1 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              g₁.rank < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive),
                            (X.1.val g : ℚ) := by
                          rw [Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2,
                              Sigma.prime_iterate_sum_pos_eq X.1.val g₁.rank heven]
                          rfl
                        -- g₁ satisfies the LHS filter:
                        --  altType g₁.rank Positive = Negative = g₁.type
                        have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                          rw [Sigma.altType_even g₁.rank heven, GeneType.neg_positive]
                          exact hε_neg
                        -- Split: LHS filter = {g₁} ∪ RHS filter (g₁ not in RHS filter)
                        have hfilter_split :
                            X.1.val.support.filter (fun g =>
                              g₁.rank - 1 < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive) =
                            {g₁} ∪ X.1.val.support.filter (fun g =>
                              g₁.rank < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive) := by
                          ext g
                          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
                                     Finsupp.mem_support_iff]
                          constructor
                          · rintro ⟨hsupp, hrank, htype⟩
                            by_cases heq : g = g₁
                            · left; exact heq
                            · right
                              refine ⟨hsupp, ?_, htype⟩
                              rcases Nat.lt_or_eq_of_le
                                (show g₁.rank ≤ g.rank from by omega) with h | h
                              · exact h
                              · exfalso; apply heq
                                exact Gene.ext h.symm
                                  (by rw [← h, ← hg₁_altType] at htype; exact htype)
                          · rintro (rfl | ⟨hsupp, hrank, htype⟩)
                            · exact ⟨by rw [hg₁_one]; exact one_ne_zero, by omega, hg₁_altType⟩
                            · exact ⟨hsupp, by omega, htype⟩
                        have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                            g₁.rank < g.rank ∧ g.type =
                            Sigma.altType g.rank GeneType.Positive)) := by
                          simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_filter]
                          rintro g rfl ⟨_, hlt, _⟩
                          exact absurd hlt (lt_irrefl _)
                        rw [hLHS, hfilter_split, Finset.sum_union hdisjoint, Finset.sum_singleton,
                            show (X.1.val g₁ : ℚ) = 1 from by exact_mod_cast hg₁_one, hRHS]
                        ring
                      have ham_eq_bj : (Sigma.sigma X.1 g₁.rank).1 -
                          (Sigma.sigma X.1 (g₁.rank + 1)).1 =
                          (Sigma.sigma X.1 j).2 - (Sigma.sigma X.1 (j + 1)).2 := by
                        have hLHS : (Sigma.sigma X.1 g₁.rank).1 -
                            (Sigma.sigma X.1 (g₁.rank + 1)).1 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              g₁.rank < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive),
                            (X.1.val g : ℚ) := by
                          rw [Sigma.sigma_fst_diff X.1.val g₁.rank X.1.2,
                              Sigma.prime_iterate_sum_pos_eq X.1.val g₁.rank heven]
                          rfl
                        have hRHS : (Sigma.sigma X.1 j).2 -
                            (Sigma.sigma X.1 (j + 1)).2 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              j < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive),
                            (X.1.val g : ℚ) := by
                          rw [Sigma.sigma_snd_diff X.1.val j X.1.2,
                              Sigma.prime_iterate_sum_neg_eq X.1.val j hjeven]
                          rfl
                        have hfilter_eq :
                            X.1.val.support.filter (fun g =>
                              g₁.rank < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive) =
                            X.1.val.support.filter (fun g =>
                              j < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive) := by
                          ext g
                          simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                          constructor
                          · rintro ⟨hg_supp, hg_rank, hg_type⟩
                            exact ⟨hg_supp,
                              by have := hg₂min g
                                    (Nat.pos_of_ne_zero hg_supp)
                                    hg_rank; omega,
                              hg_type⟩
                          · rintro ⟨hg_supp, hg_rank, hg_type⟩
                            exact ⟨hg_supp, by omega, hg_type⟩
                        rw [hLHS, hRHS, hfilter_eq]
                      linarith
                  have hbj_lt_dj : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
                      (Sigma.sigma X.1 j).2 < (Sigma.sigma Y.1 j).2 := by
                    intro j hj1 hj2
                    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj1
                    induction d with
                    | zero => simpa using hb_lt_d_rank
                    | succ d ih =>
                      have ihd := ih (by omega) (by omega)
                      have hstep := hdi_sub_le_bi_sub (g₁.rank + d) (by omega) (by omega)
                      change (Sigma.sigma X.1 (g₁.rank + d + 1)).2 <
                           (Sigma.sigma Y.1 (g₁.rank + d + 1)).2
                      simp at hstep
                      linarith
                  refine ⟨fun j hj1 hj2 => ?_, h_outside_range⟩
                  have hbj := hbj_lt_dj j hj1 hj2
                  obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val j X.1.2
                  obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val j Y.1.2
                  rw [hnX, hnY] at hbj ⊢
                  rw [show (Gene.ofRank 1 ε).signature = (0, 1) from by
                    rw [hε_neg]
                    simp [Gene.signature, Gene.ofRank, show ¬ Even 1 from by decide]]
                  constructor
                  · have h1 := (le_iff_dominates.mp hXY.le j).1
                    simp at h1
                    simp only [Prod.fst_add, add_zero]
                    simp [Sigma.sigma] at hnX
                    simp [Sigma.sigma] at hnY
                    rw [hnX, hnY] at h1
                    exact h1
                  · simp only [Prod.snd_add]
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp hbj)
                · -- g₁.rank is odd
                  have hε_pos : ε = .Positive := by
                    have hne_neg : ε ≠ .Negative := by
                      intro h; apply hε₁
                      have h_even : Even ((g₁.rank : ℤ) - 1) := by
                        have hodd : Odd g₁.rank := Nat.not_even_iff_odd.mp heven
                        obtain ⟨r, hr⟩ := hodd
                        exact ⟨↑r, by push_cast [hr]; ring⟩
                      simp only [GeneType.negOnePow_smul, if_pos h_even]
                      rw [← h]
                    cases ht : ε with
                    | Positive => rfl
                    | Negative => exact absurd ht hne_neg
                    | NonPolarized => exact absurd ht hε
                  -- a_{rank} < c_{rank}
                  have ha_lt_c_rank : (Sigma.sigma X.1 g₁.rank).1 <
                      (Sigma.sigma Y.1 g₁.rank).1 := by
                    have hstrict : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                        (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                      linarith [sigma_zero_fst_eq X Y hXY.le]
                    have hc1_ci_rank : (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 g₁.rank).1 ≤
                        (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                      Sigma.a1_ai_le_b0_bi_1 Y.1.val Y.1.2 (by omega)
                    have hd0_di_rank : (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 (g₁.rank - 1)).2 ≤
                        (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 := by
                      have hb0_eq_d0 : (Sigma.sigma X.1 0).2 = (Sigma.sigma Y.1 0).2 :=
                        sigma_zero_snd_eq X Y hXY.le
                      have hbm1_le_dm1 : (Sigma.sigma X.1 (g₁.rank - 1)).2 ≤
                          (Sigma.sigma Y.1 (g₁.rank - 1)).2 :=
                        (le_iff_dominates.mp hXY.le (g₁.rank - 1)).2
                      linarith
                    have hb0_bi_rank : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 (g₁.rank - 1)).2 =
                        (Sigma.sigma X.1 1).1 - (Sigma.sigma X.1 g₁.rank).1 :=
                      x_actual_negative_prefix_equalities
                        (fun g' _ hg'_pos => hg₁min g' (Finsupp.mem_support_iff.mpr hg'_pos.ne'))
                        (by omega) (le_refl _)
                    linarith [sigma_zero_fst_eq X Y hXY.le, hc1_ci_rank, hd0_di_rank,
                      hb0_bi_rank, hstrict]
                  have hci_sub_le_ai_sub : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank - 1 →
                      (Sigma.sigma Y.1 j).1 - (Sigma.sigma Y.1 (j + 1)).1 ≤
                      (Sigma.sigma X.1 j).1 - (Sigma.sigma X.1 (j + 1)).1 := by
                    intro j hj1 hj2
                    by_cases hjeven : Even j
                    · -- j is even
                      have hcj_le_c01 :
                          (Sigma.sigma Y.1 j).1 - (Sigma.sigma Y.1 (j + 1)).1 ≤
                          (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 := by
                        simpa [hjeven] using Sigma.cond_15_6_compare_k_to_0 Y.1.val j Y.1.2
                      have hc01_le_a01_sub1 :
                          (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 ≤
                          (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 := by
                        have ha0_eq_c0 := sigma_zero_fst_eq X Y hXY.le
                        have ha : (Sigma.sigma Y.1 0).1 - (Sigma.sigma Y.1 1).1 <
                            (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 := by
                          linarith [sigma_zero_fst_eq X Y hXY.le]
                        obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val 1 X.1.2
                        obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val 1 Y.1.2
                        have hX1 : (Sigma.sigma X.1 1).1 = ↑nX.1 := congr_arg Prod.fst hnX
                        have hY1 : (Sigma.sigma Y.1 1).1 = ↑nY.1 := congr_arg Prod.fst hnY
                        have hlt : (↑nX.1 : ℚ) < ↑nY.1 := by linarith
                        have hlt_nat : nX.1 < nY.1 := by exact_mod_cast hlt
                        have hle : (↑nX.1 : ℚ) + 1 ≤ ↑nY.1 := by
                          exact_mod_cast (by omega : nX.1 + 1 ≤ nY.1)
                        linarith
                      have ha01_sub1_eq_am_sub1 :
                          (Sigma.sigma X.1 0).1 - (Sigma.sigma X.1 1).1 - 1 =
                          (Sigma.sigma X.1 (g₁.rank - 1)).1 - (Sigma.sigma X.1 g₁.rank).1 - 1 := by
                        have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                          rw [Sigma.altType_odd g₁.rank heven]; exact hε_pos
                        have hg₁_ofRankAlt : Gene.ofRankAlt g₁.rank GeneType.Positive =
                            Finsupp.single g₁ 1 := by
                          rw [Gene.ofRankAlt_eq_gene g₁.rank_pos]
                          congr 1; exact Gene.ext rfl hg₁_altType.symm
                        have h := x_side_equalities hXpn hg₁_ofRankAlt hXg₁pos
                          (fun g' _ hg' => hg₁min g' (Finsupp.mem_support_iff.mpr hg'.ne'))
                          (show g₁.rank - 1 < g₁.rank from by omega)
                        rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
                        have heven_sub1 : Even (g₁.rank - 1) := by
                          obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp heven
                          exact ⟨r, by omega⟩
                        simp only [if_pos heven_sub1] at h
                        linarith
                      have ham_sub1_eq_bm :
                          (Sigma.sigma X.1 (g₁.rank - 1)).1 - (Sigma.sigma X.1 g₁.rank).1 - 1 =
                          (Sigma.sigma X.1 g₁.rank).2 - (Sigma.sigma X.1 (g₁.rank + 1)).2 := by
                        have hLHS : (Sigma.sigma X.1 (g₁.rank - 1)).1 -
                            (Sigma.sigma X.1 g₁.rank).1 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              g₁.rank - 1 < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive),
                            (X.1.val g : ℚ) := by
                          have h := Sigma.sigma_fst_diff X.1.val (g₁.rank - 1) X.1.2
                          rw [show (g₁.rank - 1) + 1 = g₁.rank from by omega] at h
                          rw [h, Sigma.prime_iterate_sum_pos_eq X.1.val (g₁.rank - 1)
                                  (show Even (g₁.rank - 1) from by
                                    obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp heven
                                    exact ⟨r, by omega⟩)]
                          rfl
                        have hRHS : (Sigma.sigma X.1 g₁.rank).2 -
                            (Sigma.sigma X.1 (g₁.rank + 1)).2 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              g₁.rank < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive),
                            (X.1.val g : ℚ) := by
                          rw [Sigma.sigma_snd_diff X.1.val g₁.rank X.1.2,
                              Sigma.prime_iterate_sum_neg_eq X.1.val g₁.rank heven]
                          rfl
                        have hg₁_altType : g₁.type = Sigma.altType g₁.rank GeneType.Positive := by
                          rw [Sigma.altType_odd g₁.rank heven]; exact hε_pos
                        have hfilter_split :
                            X.1.val.support.filter (fun g =>
                              g₁.rank - 1 < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive) =
                            {g₁} ∪ X.1.val.support.filter (fun g =>
                              g₁.rank < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive) := by
                          ext g
                          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
                                     Finsupp.mem_support_iff]
                          constructor
                          · rintro ⟨hsupp, hrank, htype⟩
                            by_cases heq : g = g₁
                            · left; exact heq
                            · right
                              refine ⟨hsupp, ?_, htype⟩
                              rcases Nat.lt_or_eq_of_le
                                (show g₁.rank ≤ g.rank from by omega) with h | h
                              · exact h
                              · exfalso; apply heq
                                exact Gene.ext h.symm
                                  (by rw [← h, ← hg₁_altType] at htype; exact htype)
                          · rintro (rfl | ⟨hsupp, hrank, htype⟩)
                            · exact ⟨by rw [hg₁_one]; exact one_ne_zero, by omega, hg₁_altType⟩
                            · exact ⟨hsupp, by omega, htype⟩
                        have hdisjoint : Disjoint {g₁} (X.1.val.support.filter (fun g =>
                            g₁.rank < g.rank ∧ g.type =
                            Sigma.altType g.rank GeneType.Positive)) := by
                          simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_filter]
                          rintro g rfl ⟨_, hlt, _⟩
                          exact absurd hlt (lt_irrefl _)
                        rw [hLHS, hfilter_split, Finset.sum_union hdisjoint, Finset.sum_singleton,
                            show (X.1.val g₁ : ℚ) = 1 from by exact_mod_cast hg₁_one, hRHS]
                        ring
                      have hbm_eq_aj :
                          (Sigma.sigma X.1 g₁.rank).2 - (Sigma.sigma X.1 (g₁.rank + 1)).2 =
                          (Sigma.sigma X.1 j).1 - (Sigma.sigma X.1 (j + 1)).1 := by
                        have hLHS : (Sigma.sigma X.1 g₁.rank).2 -
                            (Sigma.sigma X.1 (g₁.rank + 1)).2 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              g₁.rank < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive),
                            (X.1.val g : ℚ) := by
                          rw [Sigma.sigma_snd_diff X.1.val g₁.rank X.1.2,
                              Sigma.prime_iterate_sum_neg_eq X.1.val g₁.rank heven]
                          rfl
                        have hRHS : (Sigma.sigma X.1 j).1 -
                            (Sigma.sigma X.1 (j + 1)).1 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              j < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive),
                            (X.1.val g : ℚ) := by
                          rw [Sigma.sigma_fst_diff X.1.val j X.1.2,
                              Sigma.prime_iterate_sum_pos_eq X.1.val j hjeven]
                          rfl
                        have hfilter_eq :
                            X.1.val.support.filter (fun g =>
                              g₁.rank < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive) =
                            X.1.val.support.filter (fun g =>
                              j < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Positive) := by
                          ext g
                          simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                          constructor
                          · rintro ⟨hg_supp, hg_rank, hg_type⟩
                            exact ⟨hg_supp,
                              by have := hg₂min g
                                    (Nat.pos_of_ne_zero hg_supp)
                                    hg_rank; omega,
                              hg_type⟩
                          · rintro ⟨hg_supp, hg_rank, hg_type⟩
                            exact ⟨hg_supp, by omega, hg_type⟩
                        rw [hLHS, hRHS, hfilter_eq]
                      linarith
                    · -- j is odd
                      have hcj_le_c12 :
                          (Sigma.sigma Y.1 j).1 - (Sigma.sigma Y.1 (j + 1)).1 ≤
                          (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 2).1 := by
                        have key : ∀ n : ℕ,
                            (Sigma.sigma Y.1.val (n + n + 1)).1 -
                            (Sigma.sigma Y.1.val (n + n + 2)).1 ≤
                            (Sigma.sigma Y.1.val 1).1 - (Sigma.sigma Y.1.val 2).1 := by
                          intro n
                          induction n with
                          | zero => simp
                          | succ n ih =>
                            have h1 : (Sigma.drop Y.1.val (n + n + 3)).1 ≤
                                (Sigma.drop Y.1.val (n + n + 2)).2 := by
                              have h := Sigma.cond_15_7_drop Y.1.val (n + n + 2) Y.1.2
                              rw [if_pos ⟨n + 1, by omega⟩] at h; exact h
                            have h2 : (Sigma.drop Y.1.val (n + n + 2)).2 ≤
                                (Sigma.drop Y.1.val (n + n + 1)).1 := by
                              have h := Sigma.cond_15_7_drop Y.1.val (n + n + 1) Y.1.2
                              rw [if_neg (fun heven =>
                                (Nat.even_add_one.mp heven) ⟨n, rfl⟩)] at h; exact h
                            simp only [Sigma.drop_fst, Sigma.drop_snd] at h1 h2
                            rw [show n + 1 + (n + 1) + 1 = n + n + 3 from by omega,
                                show n + 1 + (n + 1) + 2 = n + n + 4 from by omega]
                            linarith
                        obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hjeven
                        rw [show j = m + m + 1 from by omega]
                        exact key m
                      have hc12_le_d01 :
                          (Sigma.sigma Y.1 1).1 - (Sigma.sigma Y.1 2).1 ≤
                          (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 1).2 := by
                        simpa using Sigma.cond_15_7 Y.1.val 0 Y.1.2
                      have hd01_le_b01 :
                          (Sigma.sigma Y.1 0).2 - (Sigma.sigma Y.1 1).2 ≤
                          (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 := by
                        have hb0_eq_d0 := sigma_zero_snd_eq X Y hXY.le
                        have hb1_le_d1 : (Sigma.sigma X.1 1).2 ≤ (Sigma.sigma Y.1 1).2 :=
                          (le_iff_dominates.mp hXY.le 1).2
                        linarith
                      have hb01_eq_aj :
                          (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                          (Sigma.sigma X.1 j).1 - (Sigma.sigma X.1 (j + 1)).1 := by
                        have hLHS : (Sigma.sigma X.1 0).2 - (Sigma.sigma X.1 1).2 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              0 < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Negative),
                            (X.1.val g : ℚ) := by
                          have h1 := Sigma.sigma_snd_diff X.1.val 0 X.1.2
                          have h2 := Sigma.prime_iterate_sum_eq X.1.val 0 GeneType.Negative
                          simp only [Function.iterate_zero, id] at h1 h2
                          exact h1.trans h2
                        have hRHS : (Sigma.sigma X.1 j).1 - (Sigma.sigma X.1 (j + 1)).1 =
                            ∑ g ∈ X.1.val.support.filter (fun g =>
                              j < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Negative),
                            (X.1.val g : ℚ) := by
                          have hkodd : Int.negOnePow (j : ℤ) = -1 :=
                            Int.negOnePow_odd _ (by exact_mod_cast Nat.not_even_iff_odd.mp hjeven)
                          have h1 := Sigma.sigma_fst_diff X.1.val j X.1.2
                          have h2 := Sigma.prime_iterate_sum_eq X.1.val j GeneType.Positive
                          simp only [hkodd, GeneType.neg_one_smul, GeneType.neg_positive] at h2
                          exact h1.trans h2
                        have hfilter_eq :
                            X.1.val.support.filter (fun g =>
                              0 < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Negative) =
                            X.1.val.support.filter (fun g =>
                              j < g.rank ∧
                              g.type = Sigma.altType g.rank GeneType.Negative) := by
                          ext g
                          simp only [Finset.mem_filter, Finsupp.mem_support_iff]
                          constructor
                          · rintro ⟨hg_supp, _, hg_type⟩
                            refine ⟨hg_supp, ?_, hg_type⟩
                            have hmin := hg₁min g (Finsupp.mem_support_iff.mpr hg_supp)
                            rcases eq_or_lt_of_le hmin with h_eq | h_lt
                            · have halttype :
                                  Sigma.altType g.rank GeneType.Negative =
                                  GeneType.Negative := by
                                rw [show g.rank = g₁.rank from h_eq.symm,
                                    Sigma.altType_odd g₁.rank heven]
                              rw [halttype] at hg_type
                              exact absurd hXpn (not_not.mpr
                                ⟨g₁, g, h_eq, hε_pos, hg_type,
                                 hXg₁pos, Nat.pos_of_ne_zero hg_supp⟩)
                            · exact by
                                have := hg₂min g (Nat.pos_of_ne_zero hg_supp) h_lt
                                omega
                          · rintro ⟨hg_supp, hg_rank, hg_type⟩
                            exact ⟨hg_supp, g.rank_pos, hg_type⟩
                        rw [hLHS, hRHS, hfilter_eq]
                      linarith
                  have haj_lt_cj : ∀ j, g₁.rank ≤ j → j ≤ g₂.rank →
                      (Sigma.sigma X.1 j).1 < (Sigma.sigma Y.1 j).1 := by
                    intro j hj1 hj2
                    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj1
                    induction d with
                    | zero => simpa using ha_lt_c_rank
                    | succ d ih =>
                      have ihd := ih (by omega) (by omega)
                      have hstep := hci_sub_le_ai_sub (g₁.rank + d) (by omega) (by omega)
                      change (Sigma.sigma X.1 (g₁.rank + d + 1)).1 <
                           (Sigma.sigma Y.1 (g₁.rank + d + 1)).1
                      simp at hstep
                      linarith
                  refine ⟨fun j hj1 hj2 => ?_, h_outside_range⟩
                  have haj := haj_lt_cj j hj1 hj2
                  obtain ⟨nX, hnX⟩ := Sigma.sigma_isNat X.1.val j X.1.2
                  obtain ⟨nY, hnY⟩ := Sigma.sigma_isNat Y.1.val j Y.1.2
                  rw [hnX, hnY] at haj ⊢
                  rw [show (Gene.ofRank 1 ε).signature = (1, 0) from by
                    rw [hε_pos]
                    simp [Gene.signature, Gene.ofRank, show ¬ Even 1 from by decide]]
                  constructor
                  · simp only [Prod.fst_add]
                    exact_mod_cast Nat.add_one_le_iff.mpr (Nat.cast_lt.mp haj)
                  · have h2 := (le_iff_dominates.mp hXY.le j).2
                    simp at h2
                    simp only [Prod.snd_add, add_zero]
                    simp [Sigma.sigma] at hnX
                    simp [Sigma.sigma] at hnY
                    rw [hnX, hnY] at h2
                    exact h2
              by_cases hin : g₁.rank ≤ i ∧ i ≤ g₂.rank
              · obtain ⟨hi1, hi2⟩ := hin
                -- Inside [g₁.rank, g₂.rank]: sigma(Y1)(i) - sigma(X1)(i) = sig(ofRank 1 ε)
                have hdiff : Sigma.sigma (Pi.Y1 hε hle g₁.rank_pos).val i -
                    Sigma.sigma (Pi.X1 hε hle g₁.rank_pos).val i =
                    (Gene.ofRank 1 ε).signature := by
                  simp only [Sigma.sigma, Pi.Y1_eq, Pi.X1_eq, iterate_map_add,
                    prime_iterate_ofRank,
                    show g₁.rank - i = 0 from Nat.sub_eq_zero_of_le hi1,
                    show g₁.rank - 1 - i = 0 from Nat.sub_eq_zero_of_le (by omega),
                    Gene.ofRank_zero, zero_add]
                  rw [signature_ofRank_general (show 1 ≤ g₂.rank + 1 - i from by omega) hε,
                    show g₂.rank + 1 - i - 1 = g₂.rank - i from by omega]
                  ring
                -- sigma(Z)(i) = sigma(X)(i) + sig(ofRank 1 ε)
                have hZX_diff : Sigma.sigma Z.val i - Sigma.sigma X.1.val i =
                    (Gene.ofRank 1 ε).signature := by
                  rw [hZ_split, hX_split, add_sub_add_right_eq_sub]; exact hdiff
                have hZX_eq : Sigma.sigma Z.val i =
                    Sigma.sigma X.1.val i + (Gene.ofRank 1 ε).signature :=
                  Prod.ext
                    (by have h : (Sigma.sigma Z.val i).1 - (Sigma.sigma X.1.val i).1 =
                            (Gene.ofRank 1 ε).signature.1 :=
                          calc (Sigma.sigma Z.val i).1 - (Sigma.sigma X.1.val i).1
                              = (Sigma.sigma Z.val i - Sigma.sigma X.1.val i).1 := rfl
                            _ = _ := congr_arg Prod.fst hZX_diff
                        simp_all
                        linarith)
                    (by have h : (Sigma.sigma Z.val i).2 - (Sigma.sigma X.1.val i).2 =
                            (Gene.ofRank 1 ε).signature.2 :=
                          calc (Sigma.sigma Z.val i).2 - (Sigma.sigma X.1.val i).2
                              = (Sigma.sigma Z.val i - Sigma.sigma X.1.val i).2 := rfl
                            _ = _ := congr_arg Prod.snd hZX_diff
                        simp_all
                        linarith)
                rw [hZX_eq]
                exact hXY_sigma.1 i hi1 hi2
              · -- Outside [g₁.rank, g₂.rank]: sigma(Z)(i) = sigma(X)(i) ≤ sigma(Y)(i)
                rw [hZ_split, hXY_sigma.2 i hin, ← hX_split]; exact hXY_i⟩
           -/
          · -- Case 4b: g₂.type ≠ -g₁.type (same type family)
            sorry
  · -- Case B: a₁ = c₁ for all relevant k, so b₁ < d₁ (from hsigeq and dominance).
    sorry

/-! ## Main theorem -/

/--
Proposition after (15.7) [Djoković 1982, p. 29]:
Let X, Y ∈ Π(n) with X < Y.  Then there exists a Π-mutation X → Z such that Z ≤ Y.
-/
theorem exists_mutation_le (n : ℕ) (X Y : nPi n)
    (hXY : X.1 < Y.1) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  revert X Y hXY
  refine Nat.strongRecOn n ?_
  intro n ih X Y hXY
  cases n with
  | zero =>
    exfalso
    have hX0 : X.1.val = 0 := rank_zero X.2
    have hY0 : Y.1.val = 0 := rank_zero Y.2
    exact absurd (Subtype.ext (hX0.trans hY0.symm)) (ne_of_lt hXY)
  | succ n =>
    cases n with
    | zero =>
      exfalso
      have hsig_le : signature X.1.val ≤ signature Y.1.val :=
        (le_iff_dominates.mp hXY.le) 0
      have hXsum : (signature X.1.val).1 + (signature X.1.val).2 = 1 := by
        rcases rank_one_pi_sig X.1.2 X.2 with h | h <;> simp [h]
      have hYsum : (signature Y.1.val).1 + (signature Y.1.val).2 = 1 := by
        rcases rank_one_pi_sig Y.1.2 Y.2 with h | h <;> simp [h]
      have hsig_eq : signature X.1.val = signature Y.1.val := by
        obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
        exact Prod.ext (le_antisymm h1_le (by linarith [h2_le]))
                       (le_antisymm h2_le (by linarith [h1_le]))
      exact absurd (Subtype.ext (Pi_rank_one_eq_of_sig_eq X.1.2 Y.1.2 X.2 Y.2 hsig_eq))
                   (ne_of_lt hXY)
    | succ m =>
      have ha₀_eq_c₀ := sigma_zero_fst_eq X Y hXY.le
      by_cases hcommon : ∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g
      · exact exists_mutation_le_shared_gene m ih X Y hXY hcommon
      · by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
            Sigma.sigma X.1 k = Sigma.sigma Y.1 k
        · exact exists_mutation_le_disjoint_sigma_eq m ih X.1 Y hXY hcommon hsigeq
        · by_cases hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
              g.type = .Positive ∧ h.type = .Negative ∧
              0 < X.1.val g ∧ 0 < X.1.val h
          · exact exists_mutation_le_disjoint_pair X.1 Y.1 hXY hcommon hsigeq hXpn
          · exact exists_mutation_le_fifteen_ten m ih X Y hXY hcommon hsigeq hXpn
