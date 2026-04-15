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

/-! ## (15.10): X has no positive-negative gene pair of equal rank -/

/-- Cases 1–4 of §15.10 (all sorry). -/
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
  by_cases ha : ∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      (Sigma.sigma X.1 k).1 < (Sigma.sigma Y.1 k).1
  · -- Case A: a₁ < c₁ (paper §15.10, Cases 1–4).
    -- Let k be a witness; in practice take k minimal.
    obtain ⟨k, hkpos, hYkne, hak⟩ := ha
    -- Split on Case 1 (ε₁ = −, g₁ = g_{-}(m) at minimal rank m) vs Cases 2–4 (ε₁ = +).
    -- g_{-}(m) = g^{(-1)^m}(m): Negative when m odd, Positive when m even.
    by_cases hcase1 : ∃ g₁ : Gene, 0 < X.1.val g₁ ∧
        (∀ g : Gene, 0 < X.1.val g → g₁.rank ≤ g.rank) ∧
        (Odd g₁.rank ↔ g₁.type = .Negative)
    · -- Case 1: ε₁ = −, g₁ = g_{-}(m) is the gene of minimal rank m in X.
      --   g₂ = g_{+}(k) = g^{(-1)^{k-1}}(k), whose sign depends on parity of k.
      obtain ⟨g₁, hXg₁, hg₁min, hg₁type⟩ := hcase1
      -- Split on parity of k: Case 1a (k odd) vs Case 1b (k even).
      by_cases hkodd : Odd k
      · -- Case 1a: k odd, so g₂ = g^+(k) = Positive gene at rank k.
        --   The type-3 mutation (ε = .Negative):
        --     Gene.ofRankAlt g₁.rank .Negative + Gene.ofRankAlt k .Positive
        --       → Gene.ofRankAlt (g₁.rank − 1) .Positive + Gene.ofRankAlt (k+1) .Negative
        --
        -- Step 1: X has a Positive gene g₂ at rank k.
        -- This comes from σ(X, k).fst < σ(Y, k).fst and the structure of X.
        have hg₂_exists : ∃ (g₂ : Gene), g₂.rank = k ∧ g₂.type = .Positive ∧
            0 < X.1.val g₂ := by
          sorry
        obtain ⟨g₂, hg₂rank, hg₂type, hXg₂⟩ := hg₂_exists
        -- Step 2: g₁.rank ≤ k (minimality of g₁ in X, since g₂ ∈ X has rank k).
        have hm_le_k : g₁.rank ≤ k := hg₂rank ▸ hg₁min g₂ hXg₂
        -- Step 3: g₁ ≠ g₂.
        -- If g₁ = g₂ then g₁.rank = k is odd (hkodd) yet g₁.type = .Positive ≠ .Negative
        -- forces ¬Odd g₁.rank via hg₁type — contradiction.
        have hg₁_ne_g₂ : g₁ ≠ g₂ := by
          intro heq
          have hpos : g₁.type = .Positive := heq ▸ hg₂type
          have hnotNeg : g₁.type ≠ .Negative := hpos ▸ (by decide)
          have hnotOdd : ¬Odd g₁.rank := mt hg₁type.mp hnotNeg
          exact hnotOdd (heq ▸ hg₂rank ▸ hkodd)
        -- Step 4: chromosome equalities.
        -- g₁.type = negOnePow(g₁.rank-1) • .Negative (alternating-sign gene):
        --   g₁.rank odd  → rank-1 even → negOnePow = +1 → .Negative = g₁.type ✓
        --   g₁.rank even → rank-1 odd  → negOnePow = -1 → .Positive = g₁.type ✓
        have hg₁_type_eq : (Int.negOnePow (↑(g₁.rank - 1))) • GeneType.Negative = g₁.type := by
          have hpol : g₁.type ≠ .NonPolarized :=
            IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁
              (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hXg₁))
          rw [GeneType.negOnePow_smul']
          rcases Nat.even_or_odd (g₁.rank - 1) with ⟨n, hn⟩ | ⟨n, hn⟩
          · -- g₁.rank - 1 = 2n → g₁.rank = 2n + 1, Odd
            have heven : Even (g₁.rank - 1) := ⟨n, hn⟩
            simp only [if_pos heven]
            exact (hg₁type.mp ⟨n, by have := g₁.rank_pos; omega⟩).symm
          · -- g₁.rank - 1 = 2n + 1 → g₁.rank = 2n + 2, Even
            have hnoteven : ¬Even (g₁.rank - 1) := fun ⟨m, hm⟩ ↦ by omega
            simp only [if_neg hnoteven]
            have hnotNeg : g₁.type ≠ .Negative := by
              intro h
              obtain ⟨m, hm⟩ := hg₁type.mpr h
              exact hnoteven ⟨n + 1, by omega⟩
            cases ht : g₁.type with
            | NonPolarized => exact absurd ht hpol
            | Positive => rfl
            | Negative => exact absurd ht hnotNeg
        -- g₂.type = negOnePow(k-1) • .Positive: k odd → k-1 even → negOnePow = +1 → .Positive ✓
        have hg₂_type_eq : (Int.negOnePow (↑(k - 1))) • GeneType.Positive = g₂.type := by
          rw [GeneType.negOnePow_smul']
          rcases hkodd with ⟨n, hn⟩
          have heven : Even (k - 1) := ⟨n, by omega⟩
          simp only [if_pos heven]
          exact hg₂type.symm
        -- Gene.ofRankAlt g₁.rank .Negative = Finsupp.single g₁ 1
        have hg₁_chr : Gene.ofRankAlt g₁.rank .Negative = Finsupp.single g₁ 1 := by
          rw [Gene.ofRankAlt_def,
            show (↑g₁.rank : ℤ) - 1 = ↑(g₁.rank - 1) from (Nat.cast_sub g₁.rank_pos).symm,
            hg₁_type_eq, Gene.ofRank_eq_gene]
        -- Gene.ofRankAlt k .Positive = Finsupp.single g₂ 1
        have hg₂_chr : Gene.ofRankAlt k .Positive = Finsupp.single g₂ 1 := by
          have hkpos : 0 < k := by obtain ⟨n, hn⟩ := hkodd; omega
          rw [Gene.ofRankAlt_def,
            show (↑k : ℤ) - 1 = ↑(k - 1) from (Nat.cast_sub hkpos).symm,
            hg₂_type_eq, ← hg₂rank, Gene.ofRank_eq_gene]
        -- Step 5: Set up the type-3 primitive mutation.
        let ε : GeneType := .Negative
        have hε : ε ≠ .NonPolarized := by decide
        let X3 : Pi := Pi.X3 hε hm_le_k g₁.rank_pos
        let Y3 : Pi := Pi.Y3 hε hm_le_k g₁.rank_pos
        -- X3.val = Gene.ofRankAlt g₁.rank .Negative + Gene.ofRankAlt k .Positive
        --        = single g₁ 1 + single g₂ 1
        have hX3_eq : X3.val = Finsupp.single g₁ 1 + Finsupp.single g₂ 1 := by
          rw [Pi.X3_eq, GeneType.neg_negative, hg₁_chr, hg₂_chr]
        -- Define rest = X.1.val − single g₁ 1 − single g₂ 1
        let restval := X.1.val - Finsupp.single g₁ 1 - Finsupp.single g₂ 1
        have hrest_mem : restval ∈ Pi := sub_mem_Pi _ (sub_mem_Pi _ X.1.2)
        let rest_pi : Pi := ⟨restval, hrest_mem⟩
        -- X.1.val = X3.val + restval
        have hX_eq : X3.val + restval = X.1.val := by
          rw [hX3_eq]; exact X_eq_X1_add_rest hXg₁ hXg₂ hg₁_ne_g₂
        -- Step 6: Construct Z = Y3 + rest and prove Pi.Step X Z.
        let Z : Pi := ⟨Y3.val + restval, add_mem Y3.2 hrest_mem⟩
        have hprim : Pi.Primitive X3 Y3 := Pi.Primitive.type3 ε hε hm_le_k g₁.rank_pos
        have hX_sub : X3 + rest_pi = X.1 := Subtype.ext hX_eq
        refine ⟨Z, hX_sub ▸ Pi.Step.mk X3 Y3 rest_pi hprim, ?_⟩
        -- Step 7: Show Z ≤ Y, i.e. Y3.val + restval ≤ Y.1.val.
        -- Equivalently: Δ(X3→Y3, j) ≤ Δ(X→Y, j) at every sigma level j,
        -- where Δ = sigma(Y,j) − sigma(X,j).
        change Y3.val + restval ≤ Y.1.val
        rw [le_iff_dominates]
        intro j
        rw [iterate_map_add, map_add]
        have hdecomp : signature (prime^[j] X.1.val) =
            signature (prime^[j] X3.val) + signature (prime^[j] restval) := by
          rw [← hX_eq, iterate_map_add, map_add]
        have hXYj : signature (prime^[j] X.1.val) ≤ signature (prime^[j] Y.1.val) :=
          le_iff_dominates.mp hXY.le j
        -- Split on j relative to g₁.rank and k.
        rcases Nat.lt_or_ge j g₁.rank with hjm | hjm
        · -- j < g₁.rank: mutation preserves sigma (Δ(X3→Y3, j) = 0).
          -- prime^[j] X3 and prime^[j] Y3 have equal signatures by the iterate
          -- signature equality for type-3 mutations.
          have hY3X3 : signature (prime^[j] Y3.val) = signature (prime^[j] X3.val) := by
            rw [Pi.Y3_eq, Pi.X3_eq]
            have hpol : g₁.type ≠ .NonPolarized :=
              IsPolarized_def'.mp (mem_Pi_iff.mp X.1.2) g₁
                (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hXg₁))
            have hg₁pos := g₁.rank_pos
            -- negOnePow(g₁.rank-1)² = 1, so negOnePow(g₁.rank-1) • g₁.type = .Negative
            have htype1 : (Int.negOnePow (↑(g₁.rank - 1))) • g₁.type = .Negative := by
              rw [← hg₁_type_eq, GeneType.negOnePow_smul_smul,
                show (↑(g₁.rank - 1) : ℤ) + ↑(g₁.rank - 1) = 2 * ↑(g₁.rank - 1) from by ring,
                Int.negOnePow_two_mul, one_smul]
            -- Apply mutation_type3_iterate_signature_eq with ε_lemma = g₁.type, m = 1,
            -- n = k - g₁.rank + 1, k_param = g₁.rank - 1.
            have h := mutation_type3_iterate_signature_eq (ε := g₁.type) hpol
              (show 1 ≤ k - g₁.rank + 1 from by omega) le_rfl j (g₁.rank - 1) (by omega)
            simp only [show 1 + (g₁.rank - 1) = g₁.rank from by omega,
              show k - g₁.rank + 1 + (g₁.rank - 1) = k from by omega,
              show 1 + (g₁.rank - 1) - 1 = g₁.rank - 1 from by omega,
              show k - g₁.rank + 1 + (g₁.rank - 1) + 1 = k + 1 from by omega,
              GeneType.smul_neg, htype1, show -GeneType.Negative = .Positive from rfl] at h
            exact h.symm
          rw [hY3X3, ← hdecomp]; exact hXYj
        · by_cases hkj : k + 1 ≤ j
          · -- j ≥ k+1: all genes in X3/Y3 have rank ≤ k+1 ≤ j, so prime^[j] = 0.
            have hX3j : signature (prime^[j] X3.val) = 0 := by
              rw [hX3_eq, iterate_map_add, map_add]
              simp only [← Gene.ofRank_eq_gene, prime_iterate_ofRank,
                show g₁.rank - j = 0 from by omega,
                show g₂.rank - j = 0 from by rw [hg₂rank]; omega,
                Gene.ofRank_zero, map_zero, add_zero]
            have hY3j : signature (prime^[j] Y3.val) = 0 := by
              rw [Pi.Y3_eq, iterate_map_add, map_add]
              simp only [Gene.ofRankAlt_def, prime_iterate_ofRank,
                show g₁.rank - 1 - j = 0 from by have := g₁.rank_pos; omega,
                show k + 1 - j = 0 from by omega,
                Gene.ofRank_zero, map_zero, add_zero]
            rw [hY3j, zero_add]
            rw [hdecomp, hX3j, zero_add] at hXYj
            exact hXYj
          · -- g₁.rank ≤ j ≤ k: intermediate range — need chain inequalities from §15.6/15.7.
            -- c_{k-1}−c_k ≤ ⋯ ≤ c_0−c_1 < α = a_{k-1}−a_k shows Δ(X3→Y3,j) ≤ Δ(X→Y,j).
            sorry
      · -- Case 1b: k even, so g₂ = g^-(k).
        --   Mutation: g_{-}(m) + g^-(k) → g_{-}(m-1) + g^+(k+1).
        sorry
    · -- Cases 2–4: ε₁ = +, Case 1 fails.
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
