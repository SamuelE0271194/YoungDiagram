import YoungDiagram.Sigma
import YoungDiagram.Lifting.Pi

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
      -- Step 4: σ(Z) = σ(X) + (0, 1) on [g₁.rank, g₂.rank], zero elsewhere.
      -- The type-3 mutation with ε = Negative shifts the second sigma component up by 1
      -- at each column i ∈ [g₁.rank, g₂.rank] and is the identity on all other columns.
      have hstep4 : ∀ i : ℕ,
          Sigma.sigma Z.val i =
          Sigma.sigma X.1.val i +
          if g₁.rank ≤ i ∧ i ≤ g₂.rank then (0, 1) else (0, 0) := by
        sorry
      -- It remains to show Z ≤ Y.1.
      refine ⟨Z, hstep, ?_⟩
      -- Case split on the parity of k = g₂.rank.
      rcases Nat.even_or_odd g₂.rank with ⟨j, hk_even⟩ | ⟨j, hk_odd⟩
      · -- k even
        sorry
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
        sorry
    · -- Cases 2–4: ε₁ ≠ − (Type 1 mutation with ε₁ = + or NonPolarized).
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
