import YoungDiagram.Sigma.Basic
import YoungDiagram.Variety.Mix

/-!
# Drop inequalities for `Mix (Lambda, Pi)`

This file develops the half-integer analogue of Pi's `cond_15_6` / `cond_15_7`
(see `YoungDiagram/Sigma/Basic.lean`) for chromosomes in `Mix (Lambda, Pi)`.

The strategy is the parity decomposition `X = X.oddPart + X.evenPart`:

* `X.oddPart ∈ Pi`, so the existing `Sigma.cond_15_6` / `Sigma.cond_15_7` apply.
* `X.evenPart ∈ Lambda` (all genes NonPolarized). For such chromosomes the sigma
  column has *equal components* and the per-level drop is *antitone* (the function
  `k ↦ σ(prime^[k] W)` is convex). Hence both the `cond_15_6`-style and the
  `cond_15_7`-style inequalities hold for the even part, and they are
  parity-symmetric (equal components), so they add cleanly in both `if Even k`
  branches.

Since `Sigma.sigma` is additive (`Sigma.sigma_linearity`), adding the two
inequalities componentwise yields the `Mix (Lambda, Pi)` drop inequalities.
-/

open Chromosome Finsupp

namespace MixLambdaPi

open Variety

/-! ### The Lambda (NonPolarized) part: equal components and drop antitonicity -/

/-- For `W ∈ Lambda`, the `k`-th sigma column has equal components. -/
lemma lambda_sigma_eq_components {W : Chromosome} (hW : W ∈ Lambda) (k : ℕ) :
    (Sigma.sigma W k).1 = (Sigma.sigma W k).2 := by
  have hmem : Chromosome.prime^[k] W ∈ Lambda := prime_mem_Lambda_iterate hW
  -- reuse the support-based proof from Case3 inlined here for publicness.
  simp only [Sigma.sigma]
  rw [signature_fst, signature_snd]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg_NP : g.type = .NonPolarized :=
    IsNonPolarized_def'.mp (mem_Lambda_iff.mp hmem) g hg
  have hg_sig : g.signature.1 = g.signature.2 := by
    rw [Gene.signature_of_nonPolarized hg_NP]
  simp [hg_sig]

/-- Scalar convexity of `j ↦ ((n - j : ℕ) : ℚ)`: the drop is antitone. -/
private lemma nat_sub_drop_antitone (n k : ℕ) :
    (((n - (k + 1) : ℕ) : ℚ) - ((n - (k + 2) : ℕ) : ℚ))
      ≤ (((n - k : ℕ) : ℚ) - ((n - (k + 1) : ℕ) : ℚ)) := by
  -- Reduce to a statement about naturals and discharge with omega.
  have h1 : (n - (k + 1)) + (n - (k + 1)) ≤ (n - k) + (n - (k + 2)) := by omega
  have h2 : (((n - (k + 1) : ℕ) : ℚ)) + ((n - (k + 1) : ℕ) : ℚ)
      ≤ ((n - k : ℕ) : ℚ) + ((n - (k + 2) : ℕ) : ℚ) := by
    exact_mod_cast h1
  linarith

/-- The sigma column of a single NonPolarized gene `single g b` is convex. -/
private lemma single_nonPolarized_sigma_convex {g : Gene} (hg : g.type = .NonPolarized)
    (b : ℕ) (k : ℕ) :
    Sigma.sigma (single g b) (k + 1) - Sigma.sigma (single g b) (k + 2) ≤
      Sigma.sigma (single g b) k - Sigma.sigma (single g b) (k + 1) := by
  -- `single g b = b • Gene.ofRank g.rank g.type`, and `prime^[j]` drops the rank.
  have key : ∀ j : ℕ, Sigma.sigma (single g b) j =
      ((b : ℚ) * ((g.rank - j : ℕ) : ℚ) / 2, (b : ℚ) * ((g.rank - j : ℕ) : ℚ) / 2) := by
    intro j
    simp only [Sigma.sigma, ← Gene.ofRank_eq_gene_smul, iterate_map_nsmul,
      hg, prime_iterate_ofRank, map_nsmul, signature_ofRank_nonPolarized,
      Prod.smul_mk]
    rw [Prod.mk.injEq]
    constructor <;> · rw [nsmul_eq_mul]; ring
  simp only [key]
  have hb : (0 : ℚ) ≤ (b : ℚ) := by positivity
  have hdrop := nat_sub_drop_antitone g.rank k
  rw [Prod.mk_sub_mk, Prod.mk_sub_mk, Prod.mk_le_mk]
  constructor <;>
  · rw [div_sub_div_same, div_sub_div_same, div_le_div_iff_of_pos_right (by norm_num : (0:ℚ) < 2),
      ← mul_sub, ← mul_sub]
    exact mul_le_mul_of_nonneg_left hdrop hb

/-- For `W ∈ Lambda`, the sigma column is convex: the drop from level `k+1` is at most
the drop from level `k`, componentwise.  Equivalently
`σ(W)_{k+1} - σ(W)_{k+2} ≤ σ(W)_k - σ(W)_{k+1}`. -/
lemma lambda_sigma_convex {W : Chromosome} (hW : W ∈ Lambda) (k : ℕ) :
    Sigma.sigma W (k + 1) - Sigma.sigma W (k + 2) ≤
      Sigma.sigma W k - Sigma.sigma W (k + 1) := by
  induction W using Finsupp.induction with
  | zero => simp [Sigma.sigma]
  | single_add g b f hg hb hf =>
    obtain ⟨hsingle, hf_mem⟩ := mem_Lambda_iff_add.1 hW
    have hg_NP : g.type = .NonPolarized :=
      (IsNonPolarized_single hb).1 (mem_Lambda_iff.1 hsingle)
    have hconv_single := single_nonPolarized_sigma_convex hg_NP b k
    have hconv_f := hf hf_mem
    simp only [Sigma.sigma_linearity]
    have := add_le_add hconv_single hconv_f
    -- rearrange `(s1 - s2) + (f1 - f2) ≤ ...` to match the goal
    calc (Sigma.sigma (single g b) (k + 1) + Sigma.sigma f (k + 1))
            - (Sigma.sigma (single g b) (k + 2) + Sigma.sigma f (k + 2))
          = (Sigma.sigma (single g b) (k + 1) - Sigma.sigma (single g b) (k + 2))
            + (Sigma.sigma f (k + 1) - Sigma.sigma f (k + 2)) := by abel
      _ ≤ (Sigma.sigma (single g b) k - Sigma.sigma (single g b) (k + 1))
            + (Sigma.sigma f k - Sigma.sigma f (k + 1)) := this
      _ = (Sigma.sigma (single g b) k + Sigma.sigma f k)
            - (Sigma.sigma (single g b) (k + 1) + Sigma.sigma f (k + 1)) := by abel

/-- The even-part (Lambda) drop inequality, in the exact scalar shape used by
`cond_15_6`/`cond_15_7`.  Because the Lambda part has equal sigma components, the same
inequality holds with the roles of `a` and `b` swapped on either side. -/
lemma lambda_drop_ineq {W : Chromosome} (hW : W ∈ Lambda) (k : ℕ) :
    (Sigma.sigma W (k + 1)).2 - (Sigma.sigma W (k + 2)).2 ≤
      (Sigma.sigma W k).1 - (Sigma.sigma W (k + 1)).1 := by
  have hconv := lambda_sigma_convex hW k
  have hle2 : (Sigma.sigma W (k + 1)).2 - (Sigma.sigma W (k + 2)).2 ≤
      (Sigma.sigma W k).2 - (Sigma.sigma W (k + 1)).2 := by
    have := (Prod.le_def.1 hconv).2
    simpa using this
  -- equal components let us swap `.2` for `.1` on the right.
  rw [lambda_sigma_eq_components hW k, lambda_sigma_eq_components hW (k + 1)]
  exact hle2

/-- The swapped form (with `a`/`b` roles exchanged): identical content, by symmetry. -/
lemma lambda_drop_ineq' {W : Chromosome} (hW : W ∈ Lambda) (k : ℕ) :
    (Sigma.sigma W (k + 1)).1 - (Sigma.sigma W (k + 2)).1 ≤
      (Sigma.sigma W k).2 - (Sigma.sigma W (k + 1)).2 := by
  have hconv := lambda_sigma_convex hW k
  have hle1 : (Sigma.sigma W (k + 1)).1 - (Sigma.sigma W (k + 2)).1 ≤
      (Sigma.sigma W k).1 - (Sigma.sigma W (k + 1)).1 := by
    have := (Prod.le_def.1 hconv).1
    simpa using this
  rw [← lambda_sigma_eq_components hW k, ← lambda_sigma_eq_components hW (k + 1)]
  exact hle1

/-! ### The `Mix (Lambda, Pi)` drop inequalities -/

open Sigma in
/-- (15.6) for `X ∈ Mix (Lambda, Pi)`: the half-integer analogue of `Sigma.cond_15_6`.

Here `a X k = (Sigma.sigma X k).1` and `b X k = (Sigma.sigma X k).2`. -/
lemma cond_15_6_Mix_Lambda_Pi {X : Chromosome} (hX : X ∈ Mix (Lambda, Pi)) (k : ℕ) :
    if Even k then
      (Sigma.sigma X (k + 1)).2 - (Sigma.sigma X (k + 2)).2 ≤
        (Sigma.sigma X k).1 - (Sigma.sigma X (k + 1)).1
    else
      (Sigma.sigma X (k + 1)).1 - (Sigma.sigma X (k + 2)).1 ≤
        (Sigma.sigma X k).2 - (Sigma.sigma X (k + 1)).2 := by
  obtain ⟨hEven, hOdd⟩ := mem_Mix_iff.1 hX
  -- abbreviations for the two parts
  set O := X.oddPart with hO
  set E := X.evenPart with hE
  have hdecomp : X = O + E := X.parity_decomposition
  -- sigma is additive along the parity decomposition
  have hsig : ∀ j, Sigma.sigma X j = Sigma.sigma O j + Sigma.sigma E j := by
    intro j; rw [hdecomp, Sigma.sigma_linearity]
  have hOcond := Sigma.cond_15_6 O k hOdd
  simp only [hsig, Prod.fst_add, Prod.snd_add]
  split_ifs with heven
  · -- Even k
    rw [if_pos heven] at hOcond
    -- odd part inequality + even part inequality (lambda_drop_ineq)
    have hEcond := lambda_drop_ineq hEven k
    -- `a O k - a O (k+1)` from cond_15_6, restated in terms of sigma fst/snd.
    have hO' : (Sigma.sigma O (k + 1)).2 - (Sigma.sigma O (k + 2)).2 ≤
        (Sigma.sigma O k).1 - (Sigma.sigma O (k + 1)).1 := hOcond
    -- combine
    have := add_le_add hO' hEcond
    -- rearrange into the additive-component goal
    have goal_eq :
        ((Sigma.sigma O (k + 1)).2 + (Sigma.sigma E (k + 1)).2) -
          ((Sigma.sigma O (k + 2)).2 + (Sigma.sigma E (k + 2)).2) =
        ((Sigma.sigma O (k + 1)).2 - (Sigma.sigma O (k + 2)).2) +
          ((Sigma.sigma E (k + 1)).2 - (Sigma.sigma E (k + 2)).2) := by ring
    have goal_eq2 :
        ((Sigma.sigma O k).1 + (Sigma.sigma E k).1) -
          ((Sigma.sigma O (k + 1)).1 + (Sigma.sigma E (k + 1)).1) =
        ((Sigma.sigma O k).1 - (Sigma.sigma O (k + 1)).1) +
          ((Sigma.sigma E k).1 - (Sigma.sigma E (k + 1)).1) := by ring
    rw [goal_eq, goal_eq2]
    exact this
  · -- Odd k
    rw [if_neg heven] at hOcond
    have hEcond := lambda_drop_ineq' hEven k
    have hO' : (Sigma.sigma O (k + 1)).1 - (Sigma.sigma O (k + 2)).1 ≤
        (Sigma.sigma O k).2 - (Sigma.sigma O (k + 1)).2 := hOcond
    have := add_le_add hO' hEcond
    have goal_eq :
        ((Sigma.sigma O (k + 1)).1 + (Sigma.sigma E (k + 1)).1) -
          ((Sigma.sigma O (k + 2)).1 + (Sigma.sigma E (k + 2)).1) =
        ((Sigma.sigma O (k + 1)).1 - (Sigma.sigma O (k + 2)).1) +
          ((Sigma.sigma E (k + 1)).1 - (Sigma.sigma E (k + 2)).1) := by ring
    have goal_eq2 :
        ((Sigma.sigma O k).2 + (Sigma.sigma E k).2) -
          ((Sigma.sigma O (k + 1)).2 + (Sigma.sigma E (k + 1)).2) =
        ((Sigma.sigma O k).2 - (Sigma.sigma O (k + 1)).2) +
          ((Sigma.sigma E k).2 - (Sigma.sigma E (k + 1)).2) := by ring
    rw [goal_eq, goal_eq2]
    exact this

open Sigma in
/-- (15.7) for `X ∈ Mix (Lambda, Pi)`: the half-integer analogue of `Sigma.cond_15_7`. -/
lemma cond_15_7_Mix_Lambda_Pi {X : Chromosome} (hX : X ∈ Mix (Lambda, Pi)) (k : ℕ) :
    if Even k then
      (Sigma.sigma X (k + 1)).1 - (Sigma.sigma X (k + 2)).1 ≤
        (Sigma.sigma X k).2 - (Sigma.sigma X (k + 1)).2
    else
      (Sigma.sigma X (k + 1)).2 - (Sigma.sigma X (k + 2)).2 ≤
        (Sigma.sigma X k).1 - (Sigma.sigma X (k + 1)).1 := by
  obtain ⟨hEven, hOdd⟩ := mem_Mix_iff.1 hX
  set O := X.oddPart with hO
  set E := X.evenPart with hE
  have hdecomp : X = O + E := X.parity_decomposition
  have hsig : ∀ j, Sigma.sigma X j = Sigma.sigma O j + Sigma.sigma E j := by
    intro j; rw [hdecomp, Sigma.sigma_linearity]
  have hOcond := Sigma.cond_15_7 O k hOdd
  simp only [hsig, Prod.fst_add, Prod.snd_add]
  split_ifs with heven
  · rw [if_pos heven] at hOcond
    have hEcond := lambda_drop_ineq' hEven k
    have hO' : (Sigma.sigma O (k + 1)).1 - (Sigma.sigma O (k + 2)).1 ≤
        (Sigma.sigma O k).2 - (Sigma.sigma O (k + 1)).2 := hOcond
    have := add_le_add hO' hEcond
    have goal_eq :
        ((Sigma.sigma O (k + 1)).1 + (Sigma.sigma E (k + 1)).1) -
          ((Sigma.sigma O (k + 2)).1 + (Sigma.sigma E (k + 2)).1) =
        ((Sigma.sigma O (k + 1)).1 - (Sigma.sigma O (k + 2)).1) +
          ((Sigma.sigma E (k + 1)).1 - (Sigma.sigma E (k + 2)).1) := by ring
    have goal_eq2 :
        ((Sigma.sigma O k).2 + (Sigma.sigma E k).2) -
          ((Sigma.sigma O (k + 1)).2 + (Sigma.sigma E (k + 1)).2) =
        ((Sigma.sigma O k).2 - (Sigma.sigma O (k + 1)).2) +
          ((Sigma.sigma E k).2 - (Sigma.sigma E (k + 1)).2) := by ring
    rw [goal_eq, goal_eq2]
    exact this
  · rw [if_neg heven] at hOcond
    have hEcond := lambda_drop_ineq hEven k
    have hO' : (Sigma.sigma O (k + 1)).2 - (Sigma.sigma O (k + 2)).2 ≤
        (Sigma.sigma O k).1 - (Sigma.sigma O (k + 1)).1 := hOcond
    have := add_le_add hO' hEcond
    have goal_eq :
        ((Sigma.sigma O (k + 1)).2 + (Sigma.sigma E (k + 1)).2) -
          ((Sigma.sigma O (k + 2)).2 + (Sigma.sigma E (k + 2)).2) =
        ((Sigma.sigma O (k + 1)).2 - (Sigma.sigma O (k + 2)).2) +
          ((Sigma.sigma E (k + 1)).2 - (Sigma.sigma E (k + 2)).2) := by ring
    have goal_eq2 :
        ((Sigma.sigma O k).1 + (Sigma.sigma E k).1) -
          ((Sigma.sigma O (k + 1)).1 + (Sigma.sigma E (k + 1)).1) =
        ((Sigma.sigma O k).1 - (Sigma.sigma O (k + 1)).1) +
          ((Sigma.sigma E k).1 - (Sigma.sigma E (k + 1)).1) := by ring
    rw [goal_eq, goal_eq2]
    exact this

end MixLambdaPi
