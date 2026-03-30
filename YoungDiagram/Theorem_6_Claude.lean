import YoungDiagram.Sigma
import YoungDiagram.Lifting

open Chromosome Variety

/--
`Pi_n n` is the set of elements of `Π` (the polarized variety) with rank equal to `n`.
This corresponds to `Π(n)` in the paper.
-/
def Pi_n (n : ℕ) : Set Variety.Pi := { X | X.val.rank = n }

/-- `Pi.Step` is compatible with adding a Pi element on the right. -/
private lemma Pi.Step.add_right_pi (W : Variety.Pi) {A B : Variety.Pi}
    (h : Pi.Step A B) : Pi.Step (A + W) (B + W) := by
  cases h with
  | mk X Y Z hPrim =>
    rw [add_assoc, add_assoc]
    exact Pi.Step.mk X Y (Z + W) hPrim

/--
Proposition after (15.7) [Djoković 1982, p. 29]:
Let X, Y ∈ Π(n) with X < Y.  Then there exists a Π-mutation X → Z such that Z ≤ Y.

Here:
- `Π(n)` is the set of polarized chromosomes of rank `n`
- `X < Y` is the pointwise (Finsupp) strict order on chromosomes
- `Pi.Step X Z` witnesses a single Π-mutation step from X to Z
- `Z ≤ Y` is the pointwise order on `Variety.Pi`
-/
theorem exists_mutation_le (n : ℕ) (X Y : Variety.Pi)
    (hX : X ∈ Pi_n n) (hY : Y ∈ Pi_n n)
    (hXY : X < Y) :
    ∃ Z : Variety.Pi, Pi.Step X Z ∧ Z ≤ Y := by
  -- Use strong induction so that subtracting a gene of any rank stays in range.
  revert X Y hX hY hXY
  refine Nat.strongRecOn n ?_
  intro n ih X Y hX hY hXY
  cases n with
  | zero =>
    -- rank 0 forces X = Y = 0, contradicting X < Y.
    exfalso
    have hX0 : X.val = 0 := rank_zero hX
    have hY0 : Y.val = 0 := rank_zero hY
    exact absurd (Subtype.ext (hX0.trans hY0.symm)) (ne_of_lt hXY)
  | succ n =>
    cases n with
    | zero =>
      -- X, Y ∈ Π(1): rank-1 in Π forces X = Y, contradicting X < Y.
      exfalso
      have hsig_le : signature X.val ≤ signature Y.val :=
        (le_iff_dominates.mp hXY.le) 0
      have hXsum : (signature X.val).1 + (signature X.val).2 = 1 := by
        rcases rank_one_pi_sig X.2 hX with h | h <;> simp [h]
      have hYsum : (signature Y.val).1 + (signature Y.val).2 = 1 := by
        rcases rank_one_pi_sig Y.2 hY with h | h <;> simp [h]
      have hsig_eq : signature X.val = signature Y.val := by
        obtain ⟨h1_le, h2_le⟩ := Prod.le_def.mp hsig_le
        exact Prod.ext (le_antisymm h1_le (by linarith [h2_le]))
                       (le_antisymm h2_le (by linarith [h1_le]))
      exact absurd (Subtype.ext (Pi_rank_one_eq_of_sig_eq X.2 Y.2 hX hY hsig_eq))
                   (ne_of_lt hXY)
    | succ m =>
      -- X, Y ∈ Π(m+2). Decide whether X and Y share a gene.
      by_cases hcommon : ∃ g : Gene, 0 < X.val g ∧ 0 < Y.val g
      · -- Case 1: shared gene g. Remove one copy from both, apply IH, reattach.
        obtain ⟨g, hgX, hgY⟩ := hcommon
        -- g is polarized (it is in the support of X ∈ Π)
        have hg_pol : g.type ≠ .NonPolarized :=
          IsPolarized_def'.mp (mem_Pi_iff.mp X.2) g
            (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hgX))
        -- Finsupp.single g 1 ∈ Π
        have hg1_Pi : Finsupp.single g 1 ∈ Variety.Pi :=
          mem_Pi_iff.mpr <| (IsPolarized_single Nat.one_ne_zero).2 hg_pol
        -- Define X' = X.val − single g 1 and Y' = Y.val − single g 1
        set X'v : Chromosome := X.val - Finsupp.single g 1
        set Y'v : Chromosome := Y.val - Finsupp.single g 1
        -- Adding back single g 1 recovers X.val / Y.val
        have hX_eq : X'v + Finsupp.single g 1 = X.val := by
          apply Finsupp.ext; intro h
          simp only [X'v, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with heq
          · subst heq; omega
          · omega
        have hY_eq : Y'v + Finsupp.single g 1 = Y.val := by
          apply Finsupp.ext; intro h
          simp only [Y'v, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with heq
          · subst heq; omega
          · omega
        -- X'v and Y'v are in Π (their support ⊆ that of X.val / Y.val)
        have hX'Pi : X'v ∈ Variety.Pi := by
          rw [mem_Pi_iff, IsPolarized_def']
          intro h hh
          apply IsPolarized_def'.mp (mem_Pi_iff.mp X.2) h
          rw [Finsupp.mem_support_iff] at hh ⊢
          intro hXh; apply hh
          simp only [X'v, Finsupp.tsub_apply, Finsupp.single_apply, hXh]; omega
        have hY'Pi : Y'v ∈ Variety.Pi := by
          rw [mem_Pi_iff, IsPolarized_def']
          intro h hh
          apply IsPolarized_def'.mp (mem_Pi_iff.mp Y.2) h
          rw [Finsupp.mem_support_iff] at hh ⊢
          intro hYh; apply hh
          simp only [Y'v, Finsupp.tsub_apply, Finsupp.single_apply, hYh]; omega
        -- rank (single g 1) = g.rank
        have hrank_g : Chromosome.rank (Finsupp.single g 1) = g.rank := by
          simp only [Chromosome.rank_def]
          rw [Finsupp.sum_single_index (by simp : (0 : ℕ) • g.rank = 0)]
          simp
        -- X'v.rank = m + 2 − g.rank
        have hX'rank : X'v.rank = m + 2 - g.rank := by
          have h1 : X'v.rank + g.rank = m + 2 := by
            have heq := congr_arg Chromosome.rank hX_eq
            rw [map_add, hrank_g] at heq
            linarith [show X.val.rank = m + 2 from hX]
          omega
        have hY'rank : Y'v.rank = m + 2 - g.rank := by
          have h1 : Y'v.rank + g.rank = m + 2 := by
            have heq := congr_arg Chromosome.rank hY_eq
            rw [map_add, hrank_g] at heq
            linarith [show Y.val.rank = m + 2 from hY]
          omega
        -- ⟨X'v, _⟩ < ⟨Y'v, _⟩ in Variety.Pi (cancel single g 1 from X < Y)
        -- The goal is definitionally Y'v.Dominates X'v ∧ ¬X'v.Dominates Y'v
        have hlt' : (⟨X'v, hX'Pi⟩ : Variety.Pi) < ⟨Y'v, hY'Pi⟩ := by
          change Y'v.Dominates X'v ∧ ¬X'v.Dominates Y'v
          refine ⟨fun k => ?_, fun hge => ?_⟩
          · -- Y'v.Dominates X'v at step k
            have h := (le_iff_dominates.mp hXY.le) k
            simp only [← hX_eq, ← hY_eq, iterate_map_add, map_add,
                       add_le_add_iff_right] at h
            exact h
          · -- ¬X'v.Dominates Y'v: hge yields Y ≤ X (dominance), so X < X, absurd
            exact lt_irrefl X (lt_of_lt_of_le hXY (fun k => by
              simp only [← hX_eq, ← hY_eq, iterate_map_add, map_add,
                         add_le_add_iff_right]
              exact hge k))
        -- Apply strong IH at rank m + 2 − g.rank (< m + 2 since g.rank ≥ 1)
        obtain ⟨Z', hmut', hle'⟩ :=
          ih (m + 2 - g.rank) (Nat.sub_lt (by omega) g.rank_pos)
            ⟨X'v, hX'Pi⟩ ⟨Y'v, hY'Pi⟩ hX'rank hY'rank hlt'
        -- Return Z = Z' + single g 1
        refine ⟨⟨Z'.val + Finsupp.single g 1,
            mem_Pi_iff.mpr (IsPolarized_iff_add.mpr
              ⟨mem_Pi_iff.mp Z'.2, mem_Pi_iff.mp hg1_Pi⟩)⟩, ?_, ?_⟩
        · -- Pi.Step X ⟨Z'.val + single g 1, _⟩
          -- hmut' : Pi.Step ⟨X'v, _⟩ Z'; add ⟨single g 1, _⟩ to both sides, then coerce.
          convert Pi.Step.add_right_pi ⟨Finsupp.single g 1, hg1_Pi⟩ hmut' using 1
          exact Subtype.ext hX_eq.symm
        · -- Z' + single g 1 ≤ Y.val
          change Z'.val + Finsupp.single g 1 ≤ Y.val
          rw [← hY_eq, le_iff_dominates]
          intro k
          have h := (le_iff_dominates.mp hle') k
          simp only [iterate_map_add, map_add, add_le_add_iff_right]
          exact h
      · -- Case 2: disjoint supports.
        push_neg at hcommon
        -- Sub-case split: does there exist k with Y^(k) ≠ 0 and sigma X k = sigma Y k?
        by_cases hsigeq : ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.val ≠ 0 ∧
           Sigma.sigma X k = Sigma.sigma Y k
        · -- Sub-case 2a: some positive sigma column agrees (with Y^(k) ≠ 0).
          obtain ⟨k, hkpos, hYkne, hk⟩ := hsigeq
          -- prime^[k] X ≤ prime^[k] Y follows from X ≤ Y by restricting to indices ≥ k
          have hle_k : Chromosome.prime^[k] X.val ≤ Chromosome.prime^[k] Y.val := by
            intro j
            simp only [← Function.iterate_add_apply]
            exact le_iff_dominates.mp hXY.le (j + k)
          -- prime^[k] X and prime^[k] Y have disjoint supports:
          -- prime^[k] maps gene g injectively to rank (g.rank - k) with the same type,
          -- so any gene g' in supp(prime^[k] X) comes from a unique gene in supp(X),
          -- which by hcommon cannot also be in supp(Y), so g' ∉ supp(prime^[k] Y).
          have hdisj_k : ∀ (g' : Gene), 0 < (Chromosome.prime^[k] X.val) g' →
              (Chromosome.prime^[k] Y.val) g' = 0 := by
            intro g' hg'
            -- Coefficient formula: (prime^[k'] C) g' = C ⟨g'.rank + k', g'.type, _⟩
            -- Proved by induction: each prime shifts the contributing index by 1,
            -- using Finsupp.sum_eq_single to isolate the unique gene that contributes.
            -- Key formula: (prime^[k'] D) h = D ⟨h.rank + k', h.type, _⟩
            -- Universally quantified over h so the induction step can shift the gene.
            have prime_iterate_coeff : ∀ (k' : ℕ) (D : Chromosome) (h : Gene),
                (Chromosome.prime^[k'] D) h =
                  D ⟨h.rank + k', h.type, by linarith [h.rank_pos]⟩ := by
              intro k'
              induction k' with
              | zero =>
                intro D h
                simp only [Function.iterate_zero, id, Nat.add_zero]
              | succ k' ih =>
                intro D h
                rw [Function.iterate_succ_apply']
                -- One application of prime: prime D' h = D' ⟨h.rank + 1, h.type, _⟩
                have hstep : Chromosome.prime (Chromosome.prime^[k'] D) h =
                    (Chromosome.prime^[k'] D)
                      ⟨h.rank + 1, h.type, by linarith [h.rank_pos]⟩ := by
                  simp only [Chromosome.prime, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
                             Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul,
                             Chromosome.primeGene]
                  rw [Finsupp.sum_eq_single (⟨h.rank + 1, h.type,
                        by linarith [h.rank_pos]⟩ : Gene)]
                  · -- The unique contributing gene is ⟨h.rank + 1, ...⟩
                    have hrank_sub : (⟨h.rank + 1, h.type,
                          by linarith [h.rank_pos]⟩ : Gene).rank - 1 = h.rank := by
                      simp only;
                      omega
                    simp [hrank_sub, Gene.ofRank_eq_gene, Finsupp.single_eq_same]
                  · -- All other genes contribute 0
                    intro g _ hne
                    simp only [Gene.ofRank_def]
                    split_ifs with hZ
                    · simp [Finsupp.zero_apply]
                    · rw [Finsupp.single_apply]
                      split_ifs with heq
                      · exfalso; apply hne
                        have hr := congr_arg Gene.rank heq
                        have ht := congr_arg Gene.type heq
                        obtain ⟨rg, tg, hrg⟩ := g
                        simp only at *
                        simp only [Gene.mk.injEq]
                        exact ⟨by omega, ht⟩
                      · simp
                  · intro _; simp
                -- Apply IH at shifted gene ⟨h.rank + 1, ...⟩
                have ih_shifted := ih D ⟨h.rank + 1, h.type, by linarith [h.rank_pos]⟩
                rw [hstep, ih_shifted]
                congr 1
                simp only [Gene.mk.injEq]
                exact ⟨by omega, trivial⟩
            -- Use the formula: (prime^[k] X) g' > 0 means X at ⟨g'.rank+k, ...⟩ > 0,
            -- and hcommon gives Y at that same gene ≤ 0, so (prime^[k] Y) g' = 0.
            rw [prime_iterate_coeff k X.val g'] at hg'
            rw [prime_iterate_coeff k Y.val g']
            have hle := hcommon ⟨g'.rank + k, g'.type, by linarith [g'.rank_pos]⟩ hg'
            omega

          -- Form prime^[k] X and prime^[k] Y as Pi elements.
          let Xk : Variety.Pi := ⟨Chromosome.prime^[k] X.val, prime_mem_Pi_iterate X.2⟩
          let Yk : Variety.Pi := ⟨Chromosome.prime^[k] Y.val, prime_mem_Pi_iterate Y.2⟩
          -- Step 1: Xk and Yk have the same rank, since hk says their signatures agree.
          have hXk_Yk_rank : Xk.val.rank = Yk.val.rank := by
            have h := congr_arg (fun p : ℚ × ℚ => p.1 + p.2) hk
            simp only [Sigma.sigma, signature_sum_eq_rank] at h
            exact_mod_cast h
          -- Step 2: Xk.val.rank < m + 2.
          -- Key lemma: prime strictly decreases Chromosome.rank for nonzero chromosomes.
          -- Proof sketch: rank(prime C) = C.sum (fun g m => m*(g.rank-1)) and
          -- rank C = C.sum (fun g m => m*g.rank), so their difference is
          -- C.sum (fun _ m => m) ≥ 1 when C ≠ 0.
          have prime_rank_lt : ∀ (C : Chromosome), C ≠ 0 →
              (Chromosome.prime C).rank < C.rank := by
            intro C hCne
            -- (prime C).rank = C.sum (fun g m => m * (g.rank - 1)):
            -- rank is an AddMonoidHom, prime C = C.sum (fun g m => m • primeGene g),
            -- so rank(prime C) = C.sum (fun g m => m * rank(primeGene g))
            --                  = C.sum (fun g m => m * (g.rank - 1))  [by rank_of_geneOfRank].
            -- Local helper: rank of a single-gene chromosome Gene.ofRank n ε equals n.
            have rank_ofRank : ∀ (n : ℕ) (typ : GeneType),
                Chromosome.rank (Gene.ofRank n typ) = n := by
              intro n typ
              simp only [Gene.ofRank_def]
              split_ifs with h
              · simp [h]
              · simp [Chromosome.rank_def, Finsupp.sum_single_index]
            have hrank_prime :
                (Chromosome.prime C).rank = C.sum (fun g m => m * (g.rank - 1)) := by
              simp only [Chromosome.prime, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
                         Finsupp.sum, map_sum Chromosome.rank, map_nsmul, smul_eq_mul,
                         Chromosome.primeGene, rank_ofRank]
            -- rank C = C.sum (fun g m => m * g.rank)  [unfolding the AddMonoidHom].
            have hrank_C : C.rank = C.sum (fun g m => m * g.rank) := by
              simp only [Chromosome.rank_def, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul]
            -- Therefore rank C = rank(prime C) + C.sum (fun _ m => m):
            -- each gene g contributes m*g.rank on the left and m*(g.rank-1)+m on the right,
            -- which are equal since g.rank - 1 + 1 = g.rank (g.rank ≥ 1).
            have hdecomp : C.rank = (Chromosome.prime C).rank + C.sum (fun _ m => m) := by
              rw [hrank_C, hrank_prime]
              simp only [Finsupp.sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro g _
              have hg : g.rank - 1 + 1 = g.rank := Nat.succ_pred_eq_of_pos g.rank_pos
              calc C g * g.rank
                  = C g * (g.rank - 1 + 1) := by rw [hg]
                _ = C g * (g.rank - 1) + C g := by ring
            -- C.sum (fun _ m => m) ≥ 1 since C has a nonempty support.
            have htotal : 1 ≤ C.sum (fun _ m => m) := by
              obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hCne
              exact le_trans (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg))
                (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg)
            omega
          have hXk_rank_lt : Xk.val.rank < m + 2 := by
            rw [hXk_Yk_rank, show m + 2 = Y.val.rank from hY.symm]
            -- All prime^[j] Y.val for j ≤ k are nonzero:
            -- if prime^[j] Y.val = 0 then prime^[k] Y.val = prime^[k-j](0) = 0,
            -- contradicting hYkne.
            have hiter_ne : ∀ j ≤ k, Chromosome.prime^[j] Y.val ≠ 0 := by
              intro j hj hcontra
              apply hYkne
              rw [show k = (k - j) + j from (Nat.sub_add_cancel hj).symm,
                  Function.iterate_add_apply, hcontra]
              exact Function.iterate_fixed (map_zero Chromosome.prime) _
            -- By induction: rank(prime^[j] Y.val) + j ≤ rank Y.val.
            have rank_iterate_le : ∀ j, j ≤ k →
                (Chromosome.prime^[j] Y.val).rank + j ≤ Y.val.rank := by
              intro j hj
              induction j with
              | zero => simp
              | succ j' ih =>
                rw [Function.iterate_succ_apply']
                have hlt := prime_rank_lt _ (hiter_ne j' (Nat.le_of_succ_le hj))
                linarith [ih (Nat.le_of_succ_le hj)]
            linarith [rank_iterate_le k le_rfl]
          -- Step 3: Xk < Yk.
          have hlt_k : Xk < Yk := by
            change Yk.val.Dominates Xk.val ∧ ¬Xk.val.Dominates Yk.val
            refine ⟨le_iff_dominates.mp hle_k, fun hcontra => ?_⟩
            -- From hle_k and hcontra, sig(prime^[j] Xk.val) = sig(prime^[j] Yk.val) for all j.
            -- By Pi antisymmetry (the sigma-matrix uniquely determines a Pi chromosome),
            -- this implies Xk.val = Yk.val.
            have hXkYk_eq : Xk.val = Yk.val :=
              pi_chromosome_antisymm Xk.2 Yk.2 hle_k (le_iff_dominates.mpr hcontra)
            -- Since Yk.val ≠ 0, there exists g' with 0 < Yk.val g'.
            obtain ⟨g', hg'⟩ : ∃ g', 0 < Yk.val g' := by
              obtain ⟨g', hg'mem⟩ := Finsupp.support_nonempty_iff.mpr hYkne
              exact ⟨g', Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg'mem)⟩
            -- Since Xk.val = Yk.val, g' is also in Xk.val's support.
            have hXkg' : 0 < Xk.val g' := by rwa [hXkYk_eq]
            -- hdisj_k gives Yk.val g' = 0 (disjoint supports), contradicting hg'.
            have hYkg'zero : Yk.val g' = 0 := hdisj_k g' hXkg'
            omega
          -- Step 4: Apply the strong induction hypothesis to Xk < Yk.
          -- The IH now gives Pi.Step Xk U directly (theorem conclusion uses Pi.Step).
          obtain ⟨U, hU_step, hU_le⟩ : ∃ U : Variety.Pi, Pi.Step Xk U ∧ U ≤ Yk :=
            ih Xk.val.rank hXk_rank_lt Xk Yk rfl hXk_Yk_rank.symm hlt_k
          -- Step 5: Lift the mutation from prime^[k] X to X via mutation_lifting.
          -- Step 5b: Call mutation_lifting.
          -- The membership coercion: U.2 : U.val ∈ Pi transports along
          -- Label (Label.prime^[k] 0) = Label 0 = Pi.
          -- The Step coercion: bridging Pi.Step Xk U to
          -- Mutation.Step (Label.prime^[k] 0) ... requires mutation_lifting_Pi to be public.
          obtain ⟨Z, hZ, hZ_step, hZ_prime, hZ_sig⟩ :=
            mutation_lifting (0 : Fin 5) k X.2
              ((congrArg (U.val ∈ ·) (congrArg Label (@Label.prime_iterate_zero k))).mpr U.2)
              (by
                have hU_step' : Mutation.Step (0 : Fin 5) Xk U := hU_step
                have h0 : Label (Label.prime^[k] (0 : Fin 5)) = Label 0 :=
                  congrArg Label Label.prime_iterate_zero
                convert hU_step'
                · exact Label.prime_iterate_zero
                · exact (Subtype.heq_iff_coe_eq (fun x => Iff.of_eq (congrArg (x ∈ ·) h0))).mpr rfl
                · exact (Subtype.heq_iff_coe_eq (fun x => Iff.of_eq (congrArg (x ∈ ·) h0))).mpr rfl)
          -- Step 6: Construct the witness ⟨Z, hZ⟩ and prove it ≤ Y.
          have hZ_pi : Pi.Step X ⟨Z, hZ⟩ := hZ_step
          refine ⟨⟨Z, hZ⟩, hZ_pi, ?_⟩
          -- Goal: ⟨Z, hZ⟩ ≤ Y in Variety.Pi, i.e., Z ≤ Y.val in Chromosome.
          change Z ≤ Y.val
          rw [le_iff_dominates]
          intro j
          by_cases hjk : j ≤ k
          · -- j ≤ k: hZ_sig gives sig(prime^j Z) = sig(prime^j X.val),
            --        then X ≤ Y gives sig(prime^j X.val) ≤ sig(prime^j Y.val).
            calc signature (Chromosome.prime^[j] Z)
                = signature (Chromosome.prime^[j] X.val) := (hZ_sig j hjk).symm
              _ ≤ signature (Chromosome.prime^[j] Y.val) := le_iff_dominates.mp hXY.le j
          · -- j > k: prime^[j] Z = prime^[j-k] (prime^[k] Z) = prime^[j-k] U.val,
            --        then U ≤ Yk gives sig(prime^[j-k] U.val) ≤ sig(prime^[j-k] Yk.val),
            --        and Yk.val = prime^[k] Y.val so sig(prime^[j-k] Yk.val) = sig(prime^j Y.val).
            push_neg at hjk
            have hjk' : k ≤ j := hjk.le
            calc signature (Chromosome.prime^[j] Z)
                = signature (Chromosome.prime^[j - k] U.val) := by
                    conv_lhs =>
                      rw [show j = (j - k) + k from (Nat.sub_add_cancel hjk').symm,
                          Function.iterate_add_apply, hZ_prime]
              _ ≤ signature (Chromosome.prime^[j - k] Yk.val) :=
                    le_iff_dominates.mp hU_le (j - k)
              _ = signature (Chromosome.prime^[j] Y.val) := by
                    simp only [Yk]
                    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjk']
        · -- Sub-case 2b: all sigma columns differ (hsigeq :
            --∀ k > 0, Y^(k) ≠ 0 → sigma X k ≠ sigma Y k).
          push_neg at hsigeq
          -- Now assume X ⊇ g⁺(k) + g⁻(k) for some k (paper: line after 15.9).
          -- If true, we construct a mutation g⁺(k) + g⁻(k) → g⁺(k+1) + g⁻(k-1).
          -- If false (15.10): X ⊉ g⁺(k) + g⁻(k) for all k ≥ 1, handled separately.
          by_cases hXpn : ∃ (g h : Gene), g.rank = h.rank ∧
              g.type = .Positive ∧ h.type = .Negative ∧
              0 < X.val g ∧ 0 < X.val h
          · -- X contains g⁺(k) + g⁻(k): mutation g⁺(k) + g⁻(k) → g⁺(k+1) + g⁻(k-1).
            obtain ⟨gpos, gneg, hrank, hgpos, hgneg, hXgpos, hXgneg⟩ := hXpn
            -- Y contains no gene of rank gpos.rank:
            -- any such gene equals gpos or gneg (by rank+type), but X already has both,
            -- contradicting hcommon (X and Y share no gene).
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
                -- g.rank = gpos.rank and g.type = Positive = gpos.type, so g = gpos
                have hgeq : g = gpos := by
                  obtain ⟨rg, tg, hg_r⟩ := g
                  obtain ⟨rp, tp, hp_r⟩ := gpos
                  obtain rfl : rg = rp := hgr
                  obtain rfl : tg = tp := ht.trans hgpos.symm
                  congr 1;
                -- After identifying g = gpos, X has gpos (hXgpos) and hcommon gives Y.val g ≤ 0
                subst hgeq
                -- now hXgpos : 0 < ↑X g, hcommon g hXgpos : ↑Y g ≤ 0, hYg : 0 < ↑Y g
                have h := hcommon g hXgpos
                omega
              | Negative =>
                -- g.rank = gneg.rank (via hrank) and g.type = Negative = gneg.type, so g = gneg
                have hgeq : g = gneg := by
                  obtain ⟨rg, tg, hg_r⟩ := g
                  obtain ⟨rn, tn, hn_r⟩ := gneg
                  obtain rfl : rg = rn := hgr.trans hrank
                  obtain rfl : tg = tn := ht.trans hgneg.symm
                  congr 1
                -- After identifying g = gneg, X has gneg (hXgneg) and hcommon gives Y.val g ≤ 0
                subst hgeq
                -- now hXgneg : 0 < ↑X g, hcommon g hXgneg : ↑Y g ≤ 0, hYg : 0 < ↑Y g
                have h := hcommon g hXgneg
                omega
            -- Step 1: Prove prime^[r] Y.val ≠ 0.
            let r := gpos.rank
            have hr : 1 ≤ r := gpos.rank_pos
            -- Step 1a: (signature (prime^[r-1] X.val)).1 ≥ 1.
            -- Key: prime^[r-1] gpos = Gene.ofRank 1 .Positive (by prime_iterate_ofRank),
            -- X.val ≥ Finsupp.single gpos 1 pointwise (from hXgpos),
            -- prime^[r-1] is an AddMonoidHom so it is monotone,
            -- signature .1 is monotone, and signature (Gene.ofRank 1 .Positive) = (1, 0).
            have h1a : 1 ≤ (signature (Chromosome.prime^[r - 1] X.val)).1 := by
              -- Identify Finsupp.single gpos 1 = Gene.ofRank r .Positive as Chromosomes
              have hgpos_single : Gene.ofRank r .Positive =
                (Finsupp.single gpos 1 : Chromosome) := by
                have h := Gene.ofRank_eq_gene (g := gpos)
                rw [hgpos] at h; exact h
              -- prime^[r-1] (Finsupp.single gpos 1) = Gene.ofRank 1 .Positive
              have hprime_gpos : Chromosome.prime^[r - 1] (Finsupp.single gpos 1 : Chromosome) =
                  Gene.ofRank 1 .Positive := by
                rw [← hgpos_single, prime_iterate_ofRank, Nat.sub_sub_self hr]
              -- X.val = Finsupp.single gpos 1 + (X.val - Finsupp.single gpos 1)
              -- (valid since X.val gpos ≥ 1)
              have hXeq : X.val = Finsupp.single gpos 1 + (X.val - Finsupp.single gpos 1) := by
                apply Finsupp.ext; intro h
                simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
                split_ifs with heq
                · subst heq; omega
                · omega
              -- signature (prime^[r-1] (X.val - single gpos 1)) ≥ 0 (all signatures nonneg)
              have hrest_nonneg := signature_nonneg (Chromosome.prime^[r - 1]
                (X.val - Finsupp.single gpos 1))
              -- Combine: 1 = sig(Gene.ofRank 1 .Pos).1 = sig(prime^[r-1](single gpos 1)).1
              --              ≤ sig(prime^[r-1] X.val).1
              calc (1 : ℚ)
                  = (signature (Gene.ofRank 1 .Positive : Chromosome)).1 := by
                      simp [signature_ofRank_one_positive]
                _ = (signature (Chromosome.prime^[r - 1] (Finsupp.single gpos 1 : Chromosome))).1
                  := by
                      rw [hprime_gpos]
                _ ≤ (signature (Chromosome.prime^[r - 1] X.val)).1 := by
                      conv_rhs => rw [hXeq]
                      rw [iterate_map_add, map_add]
                      exact le_add_of_nonneg_right hrest_nonneg.1
            -- Step 1b: (signature (prime^[r-1] Y.val)).1 ≥ 1.
            -- From le_iff_dominates.mp hXY.le (r-1) and h1a.
            have h1b : 1 ≤ (signature (Chromosome.prime^[r - 1] Y.val)).1 := by
              have hdom := le_iff_dominates.mp hXY.le (r - 1)
              exact le_trans h1a hdom.1
            -- Step 1c: prime^[r-1] Y.val ≠ 0.
            -- If it were 0, signature 0 = (0, 0) so .1 = 0, contradicting h1b.
            have h1c : Chromosome.prime^[r - 1] Y.val ≠ 0 := by
              intro heq
              have : (signature (Chromosome.prime^[r - 1] Y.val)).1 = 0 := by simp [heq]
              linarith
            -- Auxiliary: if C ≠ 0 and every gene in C.support has rank ≥ 2, then prime C ≠ 0.
            have prime_ne_zero_of_rank_ge_two :
                ∀ C : Chromosome, C ≠ 0 → (∀ g ∈ C.support, 2 ≤ g.rank) →
                Chromosome.prime C ≠ 0 := by
              intro C hCne hrank hcontra
              -- Pick any g₀ in C's support
              obtain ⟨g₀, hg₀⟩ := Finsupp.support_nonempty_iff.mpr hCne
              have hCg₀ : 0 < C g₀ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg₀)
              have hg₀rank : 2 ≤ g₀.rank := hrank g₀ hg₀
              -- Witness: h₁ = gene of rank g₀.rank − 1, same type
              have h₁_pos : 1 ≤ g₀.rank - 1 := by omega
              let h₁ : Gene := ⟨g₀.rank - 1, g₀.type, h₁_pos⟩
              -- (primeGene g₀) h₁ = 1
              have hpg₀ : (Chromosome.primeGene g₀) h₁ = 1 := by
                simp only [Chromosome.primeGene]
                change (Gene.ofRank h₁.rank h₁.type) h₁ = 1
                rw [Gene.ofRank_eq_gene, Finsupp.single_eq_same]
              -- Expand (prime C) h₁ to C.sum form (keep as Finsupp.sum, not Finset.sum)
              have hexpand : (Chromosome.prime C) h₁ =
                  C.sum (fun g m => m * (Chromosome.primeGene g) h₁) := by
                simp only [Chromosome.prime, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
                           Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
              -- C g₀ * 1 ≤ C.sum (...) and C g₀ > 0, so (prime C) h₁ > 0
              have hlt : 0 < (Chromosome.prime C) h₁ := by
                rw [hexpand]
                calc 0 < C g₀ := hCg₀
                    _ = C g₀ * (Chromosome.primeGene g₀) h₁ := by rw [hpg₀, mul_one]
                    _ ≤ C.sum (fun g m => m * (Chromosome.primeGene g) h₁) := by
                          simp only [Finsupp.sum]
                          exact Finset.single_le_sum
                            (f := fun g => C g * (Chromosome.primeGene g) h₁)
                            (fun _ _ => Nat.zero_le _) hg₀
              -- But prime C = 0 forces (prime C) h₁ = 0
              have hzero : (Chromosome.prime C) h₁ = 0 := by rw [hcontra]; rfl
              omega
            -- Step 1d: prime^[r] Y.val ≠ 0.
            -- Rewrite prime^[r] = prime ∘ prime^[r-1].
            -- Every gene in (prime^[r-1] Y.val).support has rank ≥ 2 because:
            -- Y has no genes of rank r (hY_no_gene), so all genes of Y contributing to
            -- prime^[r-1] Y.val come from Y-genes of rank ≥ r+1, which after r-1 prime
            -- applications land at rank ≥ 2.
            have hYr : Chromosome.prime^[r] Y.val ≠ 0 := by
              rw [show r = 1 + (r - 1) from by omega,
                  Function.iterate_add_apply, Function.iterate_one]
              apply prime_ne_zero_of_rank_ge_two _ h1c
              -- Key induction: (prime^[j] Y.val) h = 0 when h.rank = r - j.
              -- So no gene of rank 1 appears in (prime^[r-1] Y.val).
              have hkey : ∀ (j : ℕ), j ≤ r - 1 → ∀ h : Gene, h.rank = r - j →
                  (Chromosome.prime^[j] Y.val) h = 0 := by
                intro j
                induction j with
                | zero =>
                  intro _ h' hh'
                  simp only [Function.iterate_zero, id]
                  exact hY_no_gene h' (by omega)
                | succ j ihj =>
                  intro hjsucc h' hh'
                  simp only [Function.iterate_succ', Function.comp,
                             Chromosome.prime, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
                             Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
                  simp only [Finsupp.sum]
                  apply Finset.sum_eq_zero
                  intro g hg
                  have hg_ne : (Chromosome.prime^[j] Y.val) g ≠ 0 :=
                    Finsupp.mem_support_iff.mp hg
                  by_cases hrk : g.rank - 1 = h'.rank
                  · exfalso
                    exact hg_ne (ihj (by omega) g (by omega))
                  · simp only [Nat.mul_eq_zero]
                    right
                    simp only [Chromosome.primeGene, Gene.ofRank_def]
                    split_ifs with h0
                    · rfl
                    · rw [Finsupp.single_apply, if_neg]
                      intro heq
                      exact hrk (congrArg Gene.rank heq)
              -- Apply hkey at j = r-1: any gene h with h.rank = 1 is 0 in prime^[r-1] Y.val.
              intro h hmem
              rw [Finsupp.mem_support_iff] at hmem
              by_contra hlt
              push_neg at hlt
              have hh1 : h.rank = 1 := le_antisymm (by omega) h.rank_pos
              exact hmem (hkey (r - 1) (le_refl _) h (by omega))
            -- Step 2: Strict sigma inequality at level r.
            have hsig_ne : Sigma.sigma X r ≠ Sigma.sigma Y r :=
              hsigeq r gpos.rank_pos hYr
            have hle_r : Sigma.sigma X r ≤ Sigma.sigma Y r := by
              simp only [Sigma.sigma]
              exact le_iff_dominates.mp hXY.le r
            -- From ≤ and ≠, at least one component is strict.
            have hsig_lt : (Sigma.sigma X r).1 < (Sigma.sigma Y r).1 ∨
                           (Sigma.sigma X r).2 < (Sigma.sigma Y r).2 := by
              rcases lt_or_eq_of_le hle_r.1 with h1 | h1
              · exact Or.inl h1
              · rcases lt_or_eq_of_le hle_r.2 with h2 | h2
                · exact Or.inr h2
                · exact absurd (Prod.ext h1 h2) hsig_ne
            -- Step 3: Construct the mutation X → Z.
            -- Shared setup: rest = X.val − single gpos 1 − single gneg 1.
            let restval := X.val - Finsupp.single gpos 1 - Finsupp.single gneg 1
            -- gpos ≠ gneg (different types).
            have hne : gpos ≠ gneg := fun h =>
              absurd (congrArg Gene.type h) (by rw [hgpos, hgneg]; decide)
            -- Rewrite genes-of-rank as single chromosomes.
            have hgpos_eq : Gene.ofRank r .Positive = (Finsupp.single gpos 1 : Chromosome) := by
              rw [← hgpos]; exact Gene.ofRank_eq_gene
            have hgneg_eq : Gene.ofRank r .Negative = (Finsupp.single gneg 1 : Chromosome) := by
              have h := Gene.ofRank_eq_gene (g := gneg)
              rw [hgneg] at h; rwa [← hrank] at h
            -- rest ∈ Pi: all genes in rest.support ⊆ X.val.support, which is polarized.
            have rest_mem : restval ∈ Pi := by
              rw [mem_Pi_iff, IsPolarized_def']
              intro g hg
              apply IsPolarized_def'.mp (mem_Pi_iff.mp X.2) g
              rw [Finsupp.mem_support_iff] at hg ⊢
              intro hX0
              apply hg
              simp only [restval, Finsupp.tsub_apply, Finsupp.single_apply, hX0]
              omega
            -- Common hX_eq proof: X1.val + restval = X.val, given X1.val = sg + sg'.
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
                -- rw [← h2]; omega
              · omega
            -- Case split on which sigma component is strict; both cases are symmetric.
            rcases hsig_lt with h_pos | h_neg
            · -- ε = .Positive
              let ε : GeneType := .Positive
              have hε : ε ≠ .NonPolarized := by decide
              let X1 : Pi := Pi.X1 hε (le_refl r) hr
              let Y1 : Pi := Pi.Y1 hε (le_refl r) hr
              let rest_pi : Pi := ⟨restval, rest_mem⟩
              -- X1.val = single gpos 1 + single gneg 1
              have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
                -- show (Pi.X1 hε (le_refl r) hr : Chromosome) = _
                rw [Pi.X1_eq, GeneType.neg_positive, hgpos_eq, hgneg_eq]
              -- X1.val + restval = X.val
              have hX_eq : X1.val + restval = X.val := by
                rw [hX1_val]; exact hX_eq_of _ _ rfl rfl
              -- Z = Y1 + rest_pi
              let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
              -- Pi.Step X Z via Pi.Primitive.type1
              have hprim : Pi.Primitive X1 Y1 :=
                Pi.Primitive.type1 ε hε (le_refl r) hr
              have hstep_raw : Pi.Step (X1 + rest_pi) (Y1 + rest_pi) :=
                Pi.Step.mk X1 Y1 rest_pi hprim
              have hX_sub : X1 + rest_pi = X := Subtype.ext hX_eq
              refine ⟨Z, hX_sub ▸ hstep_raw, ?_⟩
              -- step 4: Z ≤ Y (three subcases: j < r, j = r, j > r)
              -- ε = .Positive: Y1.val = Gene.ofRank (r-1) .Negative + Gene.ofRank (r+1) .Positive
              change Y1.val + restval ≤ Y.val
              rw [le_iff_dominates]
              intro j
              rw [iterate_map_add, map_add]
              have hdecomp : signature (Chromosome.prime^[j] X.val) =
                  signature (Chromosome.prime^[j] X1.val) +
                  signature (Chromosome.prime^[j] restval) := by
                rw [← hX_eq, iterate_map_add, map_add]
              have hXYj : signature (Chromosome.prime^[j] X.val) ≤
                  signature (Chromosome.prime^[j] Y.val) :=
                le_iff_dominates.mp hXY.le j
              rcases lt_trichotomy j r with hjr | rfl | hjr
              · -- Subcase j < r: sig(prime^[j] Y1) = sig(prime^[j] X1)
                have hY1X1 : signature (Chromosome.prime^[j] Y1.val) =
                    signature (Chromosome.prime^[j] X1.val) := by
                  rw [Pi.Y1_eq, Pi.X1_eq]
                  have key := mutation_type1_iterate_signature_eq hε le_rfl le_rfl j (r - 1)
                    (by omega)
                  simp only [show 1 + (r - 1) = r from by omega] at key
                  exact key.symm
                rw [hY1X1, ← hdecomp]; exact hXYj
              · -- Subcase j = r: X1 contributes 0, Y1 contributes (1,0)
                have hX1r : signature (Chromosome.prime^[r] X1.val) = 0 := by
                  rw [Pi.X1_eq]
                  simp only [iterate_map_add, prime_iterate_ofRank,
                             Nat.sub_self, Gene.ofRank_zero, map_zero, add_zero]
                have hY1r : signature (Chromosome.prime^[r] Y1.val) = (1, 0) := by
                  rw [Pi.Y1_eq]
                  simp only [iterate_map_add, prime_iterate_ofRank,
                             show r - 1 - r = 0 from by omega,
                             show r + 1 - r = 1 from by omega,
                             Gene.ofRank_zero, zero_add]
                  exact signature_ofRank_one_positive
                have hrest_eq : signature (Chromosome.prime^[r] restval) =
                    signature (Chromosome.prime^[r] X.val) := by
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
              · -- Subcase j > r: both X1 and Y1 vanish under prime^[j]
                have hX1j : signature (Chromosome.prime^[j] X1.val) = 0 := by
                  rw [Pi.X1_eq]
                  simp only [iterate_map_add, prime_iterate_ofRank,
                             show r - j = 0 from by omega,
                             Gene.ofRank_zero, map_zero, add_zero]
                have hY1j : signature (Chromosome.prime^[j] Y1.val) = 0 := by
                  rw [Pi.Y1_eq]
                  simp only [iterate_map_add, prime_iterate_ofRank,
                             show r - 1 - j = 0 from by omega,
                             show r + 1 - j = 0 from by omega,
                             Gene.ofRank_zero, map_zero, add_zero]
                have hrestj : signature (Chromosome.prime^[j] restval) =
                    signature (Chromosome.prime^[j] X.val) := by
                  rw [hdecomp, hX1j, zero_add]
                rw [hY1j, zero_add, hrestj]; exact hXYj
            · -- ε = .Negative (symmetric)
              let ε : GeneType := .Negative
              have hε : ε ≠ .NonPolarized := by decide
              let X1 : Pi := Pi.X1 hε (le_refl r) hr
              let Y1 : Pi := Pi.Y1 hε (le_refl r) hr
              let rest_pi : Pi := ⟨restval, rest_mem⟩
              -- X1.val = single gneg 1 + single gpos 1 = single gpos 1 + single gneg 1
              have hX1_val : X1.val = Finsupp.single gpos 1 + Finsupp.single gneg 1 := by
                -- show (Pi.X1 hε (le_refl r) hr : Chromosome) = _
                rw [Pi.X1_eq, GeneType.neg_negative, hgneg_eq, hgpos_eq, add_comm]
              -- X1.val + restval = X.val
              have hX_eq : X1.val + restval = X.val := by
                rw [hX1_val]; exact hX_eq_of _ _ rfl rfl
              -- Z = Y1 + rest_pi
              let Z : Pi := ⟨Y1.val + restval, add_mem Y1.2 rest_mem⟩
              -- Pi.Step X Z via Pi.Primitive.type1
              have hprim : Pi.Primitive X1 Y1 :=
                Pi.Primitive.type1 ε hε (le_refl r) hr
              have hstep_raw : Pi.Step (X1 + rest_pi) (Y1 + rest_pi) :=
                Pi.Step.mk X1 Y1 rest_pi hprim
              have hX_sub : X1 + rest_pi = X := Subtype.ext hX_eq
              refine ⟨Z, hX_sub ▸ hstep_raw, ?_⟩
              -- step 4: Z ≤ Y (three subcases: j < r, j = r, j > r)
              -- ε = .Negative: Y1.val = Gene.ofRank (r-1) .Positive + Gene.ofRank (r+1) .Negative
              change Y1.val + restval ≤ Y.val
              rw [le_iff_dominates]
              intro j
              rw [iterate_map_add, map_add]
              -- Key decomposition from hX_eq: X.val = X1.val + restval
              have hdecomp : signature (Chromosome.prime^[j] X.val) =
                  signature (Chromosome.prime^[j] X1.val) +
                  signature (Chromosome.prime^[j] restval) := by
                rw [← hX_eq, iterate_map_add, map_add]
              have hXYj : signature (Chromosome.prime^[j] X.val) ≤
                  signature (Chromosome.prime^[j] Y.val) :=
                le_iff_dominates.mp hXY.le j
              rcases lt_trichotomy j r with hjr | rfl | hjr
              · -- Subcase j < r: sig(prime^[j] Y1) = sig(prime^[j] X1)
                have hY1X1 : signature (Chromosome.prime^[j] Y1.val) =
                    signature (Chromosome.prime^[j] X1.val) := by
                  rw [Pi.Y1_eq, Pi.X1_eq]
                  have key := mutation_type1_iterate_signature_eq hε le_rfl le_rfl j (r - 1)
                    (by omega)
                  simp only [show 1 + (r - 1) = r from by omega] at key
                  exact key.symm
                rw [hY1X1, ← hdecomp]; exact hXYj
              · -- Subcase j = r: X1 contributes 0, Y1 contributes (0,1)
                have hX1r : signature (Chromosome.prime^[r] X1.val) = 0 := by
                  rw [Pi.X1_eq]
                  simp only [iterate_map_add, prime_iterate_ofRank,
                             Nat.sub_self, Gene.ofRank_zero, map_zero, zero_add]
                have hY1r : signature (Chromosome.prime^[r] Y1.val) = (0, 1) := by
                  rw [Pi.Y1_eq]
                  simp only [iterate_map_add, prime_iterate_ofRank,
                             show r - 1 - r = 0 from by omega,
                             show r + 1 - r = 1 from by omega,
                             Gene.ofRank_zero, zero_add]
                  exact signature_ofRank_one_negative
                have hrest_eq : signature (Chromosome.prime^[r] restval) =
                    signature (Chromosome.prime^[r] X.val) := by
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
              · -- Subcase j > r: both X1 and Y1 vanish under prime^[j]
                have hX1j : signature (Chromosome.prime^[j] X1.val) = 0 := by
                  rw [Pi.X1_eq]
                  simp only [iterate_map_add, prime_iterate_ofRank,
                             show r - j = 0 from by omega,
                             Gene.ofRank_zero, map_zero, add_zero]
                have hY1j : signature (Chromosome.prime^[j] Y1.val) = 0 := by
                  rw [Pi.Y1_eq]
                  simp only [iterate_map_add, prime_iterate_ofRank,
                             show r - 1 - j = 0 from by omega,
                             show r + 1 - j = 0 from by omega,
                             Gene.ofRank_zero, map_zero, add_zero]
                have hrestj : signature (Chromosome.prime^[j] restval) =
                    signature (Chromosome.prime^[j] X.val) := by
                  rw [hdecomp, hX1j, zero_add]
                rw [hY1j, zero_add, hrestj]; exact hXYj
          · -- (15.10): X ⊉ g⁺(k) + g⁻(k) for all k ≥ 1.
            push_neg at hXpn
            -- From hsigeq: for k ≥ 1 with Y^(k) ≠ 0, sigma X k ≠ sigma Y k.
            -- Combined with X < Y: (a_k, b_k) ≤ (c_k, d_k), so a_k < c_k or b_k < d_k.
            -- Split: either some k has a_k < c_k, or for all such k a_k = c_k (so b_k < d_k).
            by_cases ha : ∃ k : ℕ, 0 < k ∧ Chromosome.prime^[k] Y.val ≠ 0 ∧
                (Sigma.sigma X k).1 < (Sigma.sigma Y k).1
            · -- a_k < c_k for some k ≥ 1 with Y^(k) ≠ 0 (paper: "assume a₁ < c₁", Cases 1–4).
              obtain ⟨k, hkpos, hYkne, hak⟩ := ha
              sorry
            · -- For all k ≥ 1 with Y^(k) ≠ 0: a_k = c_k, so b_k < d_k (from hsigeq).
              push_neg at ha
              sorry
