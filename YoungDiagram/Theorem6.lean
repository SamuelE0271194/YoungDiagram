import YoungDiagram.Sigma
import YoungDiagram.Lifting.Pi

open Variety hiding prime
open Chromosome

abbrev nPi (n : ℕ) := {X : Pi // X.1.rank = n}

/-! ## Case 1: X and Y share a gene -/

lemma sub_single_add_single_eq {X : Chromosome} {g : Gene} (hg : 0 < X g) :
    X - Finsupp.single g 1 + Finsupp.single g 1 = X :=
  Finsupp.sub_add_single_one_cancel (Nat.ne_zero_of_lt hg)

lemma sub_single_mem_Pi {X : Chromosome} (hXPi : X ∈ Pi) {g : Gene} :
    X - Finsupp.single g 1 ∈ Pi := by
  rw [mem_Pi_iff, IsPolarized_def'] at hXPi ⊢
  intro h hh
  apply hXPi h
  rw [Finsupp.mem_support_iff] at hh ⊢
  intro hXh; apply hh
  simp only [Finsupp.tsub_apply, Finsupp.single_apply, hXh]; omega

lemma rank_sub_single {X : Chromosome} {g : Gene} (hg : 0 < X g) :
    (X - Finsupp.single g 1).rank = X.rank - g.rank := by
  have h := congr_arg rank (sub_single_add_single_eq hg)
  rw [map_add, rank_single, one_nsmul] at h
  omega

lemma sub_single_lt_sub_single {X Y : Pi} {g : Gene} (hgX : 0 < X.val g) (hgY : 0 < Y.val g)
    (hXY : X < Y) (hXPi : X.val - Finsupp.single g 1 ∈ Pi)
    (hYPi : Y.val - Finsupp.single g 1 ∈ Pi) :
    (⟨X.val - Finsupp.single g 1, hXPi⟩ : Pi) < ⟨Y.val - Finsupp.single g 1, hYPi⟩ := by
  have hX_eq := sub_single_add_single_eq hgX
  have hY_eq := sub_single_add_single_eq hgY
  change _ ∧ _
  refine ⟨fun k => ?_, fun hge => lt_irrefl X (lt_of_lt_of_le hXY (fun k => ?_))⟩
  · have h : signature (prime^[k] X.val) ≤ signature (prime^[k] Y.val) :=
      (le_iff_dominates.mp hXY.le) k
    nth_rw 1 [← hX_eq, ← hY_eq] at h
    simp only [iterate_map_add, map_add, add_le_add_iff_right] at h
    exact h
  · have h : signature (prime^[k] (Y.val - Finsupp.single g 1)) ≤
             signature (prime^[k] (X.val - Finsupp.single g 1)) := hge k
    have h2 : signature (prime^[k] Y.val) ≤ signature (prime^[k] X.val) := by
      nth_rw 1 [← hY_eq, ← hX_eq]
      simp only [iterate_map_add, map_add, add_le_add_iff_right]
      exact h
    exact h2

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
  have hX'Pi : X'v ∈ Pi := sub_single_mem_Pi X.1.2
  have hY'Pi : Y'v ∈ Pi := sub_single_mem_Pi Y.1.2
  have hlt' : (⟨X'v, hX'Pi⟩ : Pi) < ⟨Y'v, hY'Pi⟩ :=
    sub_single_lt_sub_single hgX hgY hXY hX'Pi hY'Pi
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

private lemma prime_iterate_rank_lt_of_ne_zero {X : Chromosome} {k : ℕ} (hk : 0 < k)
    (hne : prime^[k] X ≠ 0) : (prime^[k] X).rank < X.rank := by
  have hiter_ne : ∀ j ≤ k, prime^[j] X ≠ 0 := by
    intro j hj hc; apply hne
    rw [show k = (k - j) + j from (Nat.sub_add_cancel hj).symm,
        Function.iterate_add_apply, hc]
    exact Function.iterate_fixed (map_zero prime) _
  suffices h : ∀ j, j ≤ k → (prime^[j] X).rank + j ≤ X.rank by linarith [h k le_rfl]
  intro j hj; induction j with
  | zero => simp
  | succ j' ih =>
    rw [Function.iterate_succ_apply']
    linarith [prime_rank_lt (hiter_ne j' (Nat.le_of_succ_le hj)), ih (Nat.le_of_succ_le hj)]

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
  push Not at hcommon
  push Not at hsigeq
  obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXgpos, hXgneg⟩ := hXpn
  -- Y contains no gene of rank gpos.rank
  have hY_no_gene : ∀ (g : Gene), g.rank = gpos.rank → Y.val g = 0 := by
    intro g hgr
    by_contra hne
    have hYg : 0 < Y.val g := Nat.pos_of_ne_zero hne
    have hg_pol : g.type ≠ .NonPolarized :=
      IsPolarized_def'.mp (mem_Pi_iff.mp Y.2) g
        (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hYg))
    cases ht : g.type with
    | NonPolarized => exact hg_pol ht
    | Positive =>
      have hgeq : g = gpos := by
        obtain ⟨rg, tg, hg_r⟩ := g
        obtain ⟨rp, tp, hp_r⟩ := gpos
        obtain rfl : rg = rp := hgr
        obtain rfl : tg = tp := ht.trans hgpos.symm
        congr 1;
      subst hgeq
      have h := hcommon g hXgpos
      omega
    | Negative =>
      have hgeq : g = gneg := by
        obtain ⟨rg, tg, hg_r⟩ := g
        obtain ⟨rn, tn, hn_r⟩ := gneg
        obtain rfl : rg = rn := hgr.trans hrank
        obtain rfl : tg = tn := ht.trans hgneg.symm
        congr 1
      subst hgeq
      have h := hcommon g hXgneg
      omega
  -- Step 1: Prove prime^[r] Y.val ≠ 0.
  let r := gpos.rank
  have hr : 1 ≤ r := gpos.rank_pos
  have h1a : 1 ≤ (signature (prime^[r - 1] X.val)).1 := by
    have hgpos_single : Gene.ofRank r .Positive =
      (Finsupp.single gpos 1 : Chromosome) := by
      have h := Gene.ofRank_eq_gene (g := gpos)
      rw [hgpos] at h; exact h
    have hprime_gpos : prime^[r - 1] (Finsupp.single gpos 1 : Chromosome) =
        Gene.ofRank 1 .Positive := by
      rw [← hgpos_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
    have hXeq : X.val = Finsupp.single gpos 1 + (X.val - Finsupp.single gpos 1) := by
      apply Finsupp.ext; intro h
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with heq
      · subst heq; omega
      · omega
    have hrest_nonneg := signature_nonneg (prime^[r - 1]
      (X.val - Finsupp.single gpos 1))
    calc (1 : ℚ)
        = (signature (Gene.ofRank 1 .Positive : Chromosome)).1 := by
            simp [signature_ofRank_one_positive]
      _ = (signature (prime^[r - 1] (Finsupp.single gpos 1 : Chromosome))).1
        := by
            rw [hprime_gpos]
      _ ≤ (signature (prime^[r - 1] X.val)).1 := by
            conv_rhs => rw [hXeq]
            rw [iterate_map_add, map_add]
            exact le_add_of_nonneg_right hrest_nonneg.1
  have h1b : 1 ≤ (signature (prime^[r - 1] Y.val)).1 := by
    have hdom := le_iff_dominates.mp hXY.le (r - 1)
    exact le_trans h1a hdom.1
  have h1c : prime^[r - 1] Y.val ≠ 0 := by
    intro heq
    have : (signature (prime^[r - 1] Y.val)).1 = 0 := by simp [heq]
    linarith
  -- Step 1d: prime^[r] Y.val ≠ 0.
  have hYr : prime^[r] Y.val ≠ 0 := by
    rw [show r = 1 + (r - 1) from by omega,
        Function.iterate_add_apply, Function.iterate_one]
    apply prime_ne_zero_of_rank_ge_two h1c
    have hkey : ∀ (j : ℕ), j ≤ r - 1 → ∀ h : Gene, h.rank = r - j →
        (prime^[j] Y.val) h = 0 := by
      intro j
      induction j with
      | zero =>
        intro _ h' hh'
        simp only [Function.iterate_zero, id]
        exact hY_no_gene h' (by omega)
      | succ j ihj =>
        intro hjsucc h' hh'
        simp only [Function.iterate_succ', Function.comp,
                   prime, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
                   Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
        simp only [Finsupp.sum]
        apply Finset.sum_eq_zero
        intro g hg
        have hg_ne : (prime^[j] Y.val) g ≠ 0 :=
          Finsupp.mem_support_iff.mp hg
        by_cases hrk : g.rank - 1 = h'.rank
        · exfalso
          exact hg_ne (ihj (by omega) g (by omega))
        · simp only [Nat.mul_eq_zero]
          right
          simp only [primeGene, Gene.ofRank_def]
          split_ifs with h0
          · rfl
          · rw [Finsupp.single_apply, if_neg]
            intro heq
            exact hrk (congrArg Gene.rank heq)
    intro h hmem
    rw [Finsupp.mem_support_iff] at hmem
    by_contra hlt
    push Not at hlt
    have hh1 : h.rank = 1 := le_antisymm (by omega) h.rank_pos
    exact hmem (hkey (r - 1) (le_refl _) h (by omega))
  -- Step 2: Strict sigma inequality at level r.
  have hsig_ne : Sigma.sigma X r ≠ Sigma.sigma Y r :=
    hsigeq r gpos.rank_pos hYr
  have hle_r : Sigma.sigma X r ≤ Sigma.sigma Y r := by
    simp only [Sigma.sigma]
    exact le_iff_dominates.mp hXY.le r
  have hsig_lt : (Sigma.sigma X r).1 < (Sigma.sigma Y r).1 ∨
                 (Sigma.sigma X r).2 < (Sigma.sigma Y r).2 := by
    rcases lt_or_eq_of_le hle_r.1 with h1 | h1
    · exact Or.inl h1
    · rcases lt_or_eq_of_le hle_r.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd (Prod.ext h1 h2) hsig_ne
  -- Step 3: Construct the mutation X → Z.
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
    intro hX0
    apply hg
    simp only [restval, Finsupp.tsub_apply, Finsupp.single_apply, hX0]
    omega
  have hX_eq_of : ∀ (sg sg' : Chromosome),
      sg = Finsupp.single gpos 1 → sg' = Finsupp.single gneg 1 →
      sg + sg' + restval = X.val := by
    intro sg sg' hsg hsg'
    subst hsg hsg'
    ext g
    simp only [Finsupp.add_apply, restval, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h1 h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [← h1]; omega
    · have : gneg = g := by
        assumption
      rw [← this]; omega
    · omega
  -- Case split on which sigma component is strict.
  rcases hsig_lt with h_pos | h_neg
  · -- ε = .Positive
    let ε : GeneType := .Positive
    have hε : ε ≠ .NonPolarized := by decide
    let X1 : Pi := Pi.X1 hε (le_refl r) hr
    let Y1 : Pi := Pi.Y1 hε (le_refl r) hr
    let rest_pi : Pi := ⟨restval, rest_mem⟩
    have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
      rw [Pi.X1_eq, GeneType.neg_positive, hgpos_eq, hgneg_eq]
    have hX_eq : X1.val + restval = X.val := by
      rw [hX1_val]; exact hX_eq_of _ _ rfl rfl
    let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
    have hprim : Pi.Primitive X1 Y1 :=
      Pi.Primitive.type1 ε hε (le_refl r) hr
    have hstep_raw : Pi.Step (X1 + rest_pi) (Y1 + rest_pi) :=
      Pi.Step.mk X1 Y1 rest_pi hprim
    have hX_sub : X1 + rest_pi = X := Subtype.ext hX_eq
    refine ⟨Z, hX_sub ▸ hstep_raw, ?_⟩
    change Y1.val + restval ≤ Y.val
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp : signature (prime^[j] X.val) =
        signature (prime^[j] X1.val) +
        signature (prime^[j] restval) := by
      rw [← hX_eq, iterate_map_add, map_add]
    have hXYj : signature (prime^[j] X.val) ≤
        signature (prime^[j] Y.val) :=
      le_iff_dominates.mp hXY.le j
    rcases lt_trichotomy j r with hjr | rfl | hjr
    · have hY1X1 : signature (prime^[j] Y1.val) =
          signature (prime^[j] X1.val) := by
        rw [Pi.Y1_eq, Pi.X1_eq]
        have key := mutation_type1_iterate_signature_eq hε le_rfl le_rfl j (r - 1)
          (by omega)
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
      have hrest_eq : signature (prime^[r] restval) =
          signature (prime^[r] X.val) := by
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
      have hrestj : signature (prime^[j] restval) =
          signature (prime^[j] X.val) := by
        rw [hdecomp, hX1j, zero_add]
      rw [hY1j, zero_add, hrestj]; exact hXYj
  · -- ε = .Negative (symmetric)
    let ε : GeneType := .Negative
    have hε : ε ≠ .NonPolarized := by decide
    let X1 : Pi := Pi.X1 hε (le_refl r) hr
    let Y1 : Pi := Pi.Y1 hε (le_refl r) hr
    let rest_pi : Pi := ⟨restval, rest_mem⟩
    have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
      rw [Pi.X1_eq, GeneType.neg_negative, hgneg_eq, hgpos_eq, add_comm]
    have hX_eq : X1.val + restval = X.val := by
      rw [hX1_val]; exact hX_eq_of _ _ rfl rfl
    let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
    have hprim : Pi.Primitive X1 Y1 :=
      Pi.Primitive.type1 ε hε (le_refl r) hr
    have hstep_raw : Pi.Step (X1 + rest_pi) (Y1 + rest_pi) :=
      Pi.Step.mk X1 Y1 rest_pi hprim
    have hX_sub : X1 + rest_pi = X := Subtype.ext hX_eq
    refine ⟨Z, hX_sub ▸ hstep_raw, ?_⟩
    change Y1.val + restval ≤ Y.val
    rw [le_iff_dominates]
    intro j
    rw [iterate_map_add, map_add]
    have hdecomp : signature (prime^[j] X.val) =
        signature (prime^[j] X1.val) +
        signature (prime^[j] restval) := by
      rw [← hX_eq, iterate_map_add, map_add]
    have hXYj : signature (prime^[j] X.val) ≤
        signature (prime^[j] Y.val) :=
      le_iff_dominates.mp hXY.le j
    rcases lt_trichotomy j r with hjr | rfl | hjr
    · have hY1X1 : signature (prime^[j] Y1.val) =
          signature (prime^[j] X1.val) := by
        rw [Pi.Y1_eq, Pi.X1_eq]
        have key := mutation_type1_iterate_signature_eq hε le_rfl le_rfl j (r - 1)
          (by omega)
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
      have hrest_eq : signature (prime^[r] restval) =
          signature (prime^[r] X.val) := by
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
      have hrestj : signature (prime^[j] restval) =
          signature (prime^[j] X.val) := by
        rw [hdecomp, hX1j, zero_add]
      rw [hY1j, zero_add, hrestj]; exact hXYj

/-! ## (15.10): X has no positive-negative gene pair of equal rank -/

/-- Case 1 of §15.10. -/
private lemma exists_mutation_le_fifteen_ten_case1 (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (k : ℕ) (hkpos : 0 < k) (hYkne : prime^[k] Y.1.val ≠ 0)
    (hak : (Sigma.sigma X.1 k).1 < (Sigma.sigma Y.1 k).1)
    (gpos gneg : Gene) (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hrlt : gpos.rank < gneg.rank) (hrlek : gpos.rank ≤ k)
    (hXgpos : 0 < X.1.val gpos) (hXgneg : 0 < X.1.val gneg) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hcommon hsigeq hXpn
  sorry

/-- Case 2 of §15.10. -/
private lemma exists_mutation_le_fifteen_ten_case2 (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (k : ℕ) (hkpos : 0 < k) (hYkne : prime^[k] Y.1.val ≠ 0)
    (hak : (Sigma.sigma X.1 k).1 < (Sigma.sigma Y.1 k).1)
    (gneg gpos : Gene) (hgneg : gneg.type = .Negative) (hgpos : gpos.type = .Positive)
    (hrlt : gneg.rank < gpos.rank) (hrlek : gneg.rank ≤ k)
    (hXgneg : 0 < X.1.val gneg) (hXgpos : 0 < X.1.val gpos) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hcommon hsigeq hXpn
  sorry

/-- Case 3 of §15.10. -/
private lemma exists_mutation_le_fifteen_ten_case3 (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (k : ℕ) (hkpos : 0 < k) (hYkne : prime^[k] Y.1.val ≠ 0)
    (hak : (Sigma.sigma X.1 k).1 < (Sigma.sigma Y.1 k).1)
    (g1 g2 : Gene) (hg1pos : g1.type = .Positive) (hg2pos : g2.type = .Positive)
    (hg1le : g1.rank ≤ g2.rank) (hg1m : 1 < g1.rank)
    (hXg1 : 0 < X.1.val g1) (hXg2 : 0 < X.1.val g2) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hcommon hsigeq hXpn
  sorry

/-- Case 4 of §15.10. -/
private lemma exists_mutation_le_fifteen_ten_case4 (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (k : ℕ) (hkpos : 0 < k) (hYkne : prime^[k] Y.1.val ≠ 0)
    (hak : (Sigma.sigma X.1 k).1 < (Sigma.sigma Y.1 k).1)
    (hcase1 : ¬∃ gpos gneg : Gene, gpos.type = .Positive ∧ gneg.type = .Negative
      ∧ gpos.rank < gneg.rank ∧ gpos.rank ≤ k ∧ 0 < X.1.val gpos ∧ 0 < X.1.val gneg)
    (hcase2 : ¬∃ gneg gpos : Gene, gneg.type = .Negative ∧ gpos.type = .Positive
      ∧ gneg.rank < gpos.rank ∧ gneg.rank ≤ k ∧ 0 < X.1.val gneg ∧ 0 < X.1.val gpos)
    (hcase3 : ¬∃ g1 g2 : Gene, g1.type = .Positive ∧ g2.type = .Positive
      ∧ g1.rank ≤ g2.rank ∧ 1 < g1.rank ∧ 0 < X.1.val g1 ∧ 0 < X.1.val g2) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hcommon hsigeq hXpn
  sorry

/-- The a_k = c_k case of §15.10. -/
private lemma exists_mutation_le_fifteen_ten_ak_eq_ck (m : ℕ)
    (ih : ∀ k, k < m + 2 → ∀ X Y : nPi k, X.1 < Y.1 →
      ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1)
    (X Y : nPi (m + 2)) (hXY : X.1 < Y.1)
    (hcommon : ¬∃ g : Gene, 0 < X.1.val g ∧ 0 < Y.1.val g)
    (hsigeq : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      Sigma.sigma X.1 k = Sigma.sigma Y.1 k)
    (hXpn : ¬∃ (g h : Gene), g.rank = h.rank ∧
      g.type = .Positive ∧ h.type = .Negative ∧
      0 < X.1.val g ∧ 0 < X.1.val h)
    (ha : ¬∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      (Sigma.sigma X.1 k).1 < (Sigma.sigma Y.1 k).1) :
    ∃ Z : Pi, Pi.Step X.1 Z ∧ Z ≤ Y.1 := by
  push Not at hcommon hsigeq hXpn
  push Not at ha
  sorry

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
  by_cases ha : ∃ k : ℕ, 0 < k ∧ prime^[k] Y.1.val ≠ 0 ∧
      (Sigma.sigma X.1 k).1 < (Sigma.sigma Y.1 k).1
  · -- a_k < c_k for some k ≥ 1 with Y^(k) ≠ 0 (paper: "assume a₁ < c₁", Cases 1–4).
    obtain ⟨k, hkpos, hYkne, hak⟩ := ha
    -- Cases 1–4: split on what gene pair X contains (Djoković §15).
    by_cases hcase1 : ∃ gpos gneg : Gene, gpos.type = .Positive ∧
        gneg.type = .Negative ∧ gpos.rank < gneg.rank ∧ gpos.rank ≤ k ∧
        0 < X.1.val gpos ∧ 0 < X.1.val gneg
    · -- Case 1: X has g⁺(r) with r ≤ k and g⁻(s) with r < s.
      --   Type 1 mutation (ε = .Positive): g⁺(r) + g⁻(s) → g⁻(r−1) + g⁺(s+1).
      obtain ⟨gpos, gneg, hgpos, hgneg, hrlt, hrlek, hXgpos, hXgneg⟩ := hcase1
      exact exists_mutation_le_fifteen_ten_case1 m ih X Y hXY hcommon hsigeq hXpn k hkpos hYkne hak
        gpos gneg hgpos hgneg hrlt hrlek hXgpos hXgneg
    · by_cases hcase2 : ∃ gneg gpos : Gene, gneg.type = .Negative ∧
          gpos.type = .Positive ∧ gneg.rank < gpos.rank ∧ gneg.rank ≤ k ∧
          0 < X.1.val gneg ∧ 0 < X.1.val gpos
      · -- Case 2: X has g⁻(r) with r ≤ k and g⁺(s) with r < s.
        --   Type 1 mutation (ε = .Negative): g⁻(r) + g⁺(s) → g⁺(r−1) + g⁻(s+1).
        obtain ⟨gneg, gpos, hgneg, hgpos, hrlt, hrlek, hXgneg, hXgpos⟩ := hcase2
        exact exists_mutation_le_fifteen_ten_case2 m ih X Y hXY hcommon
          hsigeq hXpn k hkpos hYkne hak
          gneg gpos hgneg hgpos hrlt hrlek hXgneg hXgpos
      · by_cases hcase3 : ∃ g1 g2 : Gene, g1.type = .Positive ∧
            g2.type = .Positive ∧ g1.rank ≤ g2.rank ∧ 1 < g1.rank ∧
            0 < X.1.val g1 ∧ 0 < X.1.val g2
        · -- Case 3: X has two positive genes with smallest rank ≥ 2.
          --   Type 2 mutation (ε = .Positive): g⁺(r₁) + g⁺(r₂) → g⁺(r₁−2) + g⁺(r₂+2).
          obtain ⟨g1, g2, hg1pos, hg2pos, hg1le, hg1m, hXg1, hXg2⟩ := hcase3
          exact exists_mutation_le_fifteen_ten_case3 m ih X Y hXY hcommon
            hsigeq hXpn k hkpos hYkne hak
            g1 g2 hg1pos hg2pos hg1le hg1m hXg1 hXg2
        · -- Case 4: X has two negative genes with smallest rank ≥ 2
          --   (exhaustive given Cases 1–3 fail).
          --   Type 2 mutation (ε = .Negative): g⁻(r₁) + g⁻(r₂) → g⁻(r₁−2) + g⁻(r₂+2).
          exact exists_mutation_le_fifteen_ten_case4 m ih X Y hXY hcommon
            hsigeq hXpn k hkpos hYkne hak
            hcase1 hcase2 hcase3
  · -- For all k ≥ 1 with Y^(k) ≠ 0: a_k = c_k, so b_k < d_k (from hsigeq).
    exact exists_mutation_le_fifteen_ten_ak_eq_ck m ih X Y hXY hcommon hsigeq hXpn ha

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
