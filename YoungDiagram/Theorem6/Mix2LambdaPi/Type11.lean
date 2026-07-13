import YoungDiagram.Theorem6.Mix2LambdaPi.Type12

open Variety hiding prime prime_def
open Chromosome Sigma Pointwise

namespace Mix2LambdaPi

private lemma type11_pos_neg_signature_sum_fst (k : ℕ) :
    (Gene.ofRank k GeneType.Positive).signature.1 +
      (Gene.ofRank k GeneType.Negative).signature.1 = (k : ℚ) := by
  have h := signature_sum_ofRank_neg_eq_rank (k := k) (ε := GeneType.Positive)
  rw [GeneType.neg_positive] at h
  simpa using congr_arg Prod.fst h

private lemma type11_pos_neg_signature_sum_snd (k : ℕ) :
    (Gene.ofRank k GeneType.Positive).signature.2 +
      (Gene.ofRank k GeneType.Negative).signature.2 = (k : ℚ) := by
  have h := signature_sum_ofRank_neg_eq_rank (k := k) (ε := GeneType.Positive)
  rw [GeneType.neg_positive] at h
  simpa using congr_arg Prod.snd h

/-- The type11 target never exceeds the source by more than the diagonal
slack `(1,1)` in any sigma column. -/
private lemma type11_signature_le_add_diagonal
    {m n j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n) :
    signature (Chromosome.prime^[j] (Y11 h_le hε).1) ≤
      ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[j] (X11 h_le hε).1) := by
  simp only [X11_eq, Y11_eq, iterate_map_add, map_add, prime_iterate_ofRank]
  by_cases hj1 : j ≤ 2 * m + 1
  · have eq1 : 2 * m + 3 - j = 2 * m + 1 - j + 2 := by omega
    have eq2 : 2 * n + 4 - j = 2 * n + 3 - j + 1 := by omega
    rw [eq1, signature_ofRank_eq₂' (2 * m + 1 - j), eq2]
    have hPN1 := type11_pos_neg_signature_sum_fst (2 * n + 3 - j)
    have hPN2 := type11_pos_neg_signature_sum_snd (2 * n + 3 - j)
    refine ⟨?_, ?_⟩
    · simp only [signature_ofRank_nonPolarized, Prod.fst_add]
      push_cast at *
      linarith
    · simp only [signature_ofRank_nonPolarized, Prod.snd_add]
      push_cast at *
      linarith
  · by_cases hj2 : j ≤ 2 * n + 3
    · have eq1 : 2 * m + 3 - j = 0 ∨ 2 * m + 3 - j = 1 := by omega
      have eq2 : 2 * m + 1 - j = 0 := by omega
      have eq3 : 2 * n + 4 - j = 2 * n + 3 - j + 1 := by omega
      rw [eq2, Gene.ofRank_zero, map_zero, zero_add, eq3]
      have hPN1 := type11_pos_neg_signature_sum_fst (2 * n + 3 - j)
      have hPN2 := type11_pos_neg_signature_sum_snd (2 * n + 3 - j)
      rcases eq1 with heq | heq
      · rw [heq, Gene.ofRank_zero, map_zero, zero_add]
        refine ⟨?_, ?_⟩
        · simp only [signature_ofRank_nonPolarized, Prod.fst_add]
          push_cast at *
          linarith
        · simp only [signature_ofRank_nonPolarized, Prod.snd_add]
          push_cast at *
          linarith
      · rw [heq]
        have hsig_one_nn := signature_nonneg (Gene.ofRank 1 ε)
        have hhalf : (((2 * n + 3 - j : ℕ) : ℚ) + 1) / 2 +
            (((2 * n + 3 - j : ℕ) : ℚ) + 1) / 2 =
            ((2 * n + 3 - j : ℕ) : ℚ) + 1 := by ring
        refine ⟨?_, ?_⟩
        · simp only [signature_ofRank_nonPolarized, Prod.fst_add]
          push_cast at *
          have hnonneg : (0 : ℚ) ≤ (signature (Gene.ofRank 1 ε)).1 := by
            simpa using hsig_one_nn.1
          have hPN1' : (signature (Gene.ofRank 1 ε)).1 +
                (signature (Gene.ofRank (2 * n + 3 - j) GeneType.Positive)).1 +
                (signature (Gene.ofRank (2 * n + 3 - j) GeneType.Negative)).1 =
              (signature (Gene.ofRank 1 ε)).1 + ((2 * n + 3 - j : ℕ) : ℚ) := by
            linarith
          calc
            (((2 * n + 3 - j : ℕ) : ℚ) + 1) / 2 +
                (((2 * n + 3 - j : ℕ) : ℚ) + 1) / 2
                = ((2 * n + 3 - j : ℕ) : ℚ) + 1 := hhalf
            _ ≤ 1 + ((signature (Gene.ofRank 1 ε)).1 +
                  ((2 * n + 3 - j : ℕ) : ℚ)) := by
              ring_nf
              linarith
            _ = 1 + ((signature (Gene.ofRank 1 ε)).1 +
                (signature (Gene.ofRank (2 * n + 3 - j) GeneType.Positive)).1 +
                (signature (Gene.ofRank (2 * n + 3 - j) GeneType.Negative)).1) := by
              rw [hPN1']
        · simp only [signature_ofRank_nonPolarized, Prod.snd_add]
          push_cast at *
          have hnonneg : (0 : ℚ) ≤ (signature (Gene.ofRank 1 ε)).2 := by
            simpa using hsig_one_nn.2
          have hPN2' : (signature (Gene.ofRank 1 ε)).2 +
                (signature (Gene.ofRank (2 * n + 3 - j) GeneType.Positive)).2 +
                (signature (Gene.ofRank (2 * n + 3 - j) GeneType.Negative)).2 =
              (signature (Gene.ofRank 1 ε)).2 + ((2 * n + 3 - j : ℕ) : ℚ) := by
            linarith
          calc
            (((2 * n + 3 - j : ℕ) : ℚ) + 1) / 2 +
                (((2 * n + 3 - j : ℕ) : ℚ) + 1) / 2
                = ((2 * n + 3 - j : ℕ) : ℚ) + 1 := hhalf
            _ ≤ 1 + ((signature (Gene.ofRank 1 ε)).2 +
                  ((2 * n + 3 - j : ℕ) : ℚ)) := by
              ring_nf
              linarith
            _ = 1 + ((signature (Gene.ofRank 1 ε)).2 +
                (signature (Gene.ofRank (2 * n + 3 - j) GeneType.Positive)).2 +
                (signature (Gene.ofRank (2 * n + 3 - j) GeneType.Negative)).2) := by
              rw [hPN2']
    · have eq1 : 2 * m + 3 - j = 0 := by omega
      have eq2 : 2 * m + 1 - j = 0 := by omega
      have eq3 : 2 * n + 3 - j = 0 := by omega
      have eq4 : 2 * n + 4 - j = 0 ∨ 2 * n + 4 - j = 1 := by omega
      rw [eq1, eq2, eq3]
      simp only [Gene.ofRank_zero, map_zero, zero_add, add_zero]
      rcases eq4 with heq | heq
      · rw [heq, Gene.ofRank_zero, map_zero, zero_add]
        constructor <;> norm_num
      · rw [heq, signature_ofRank_nonPolarized, Prod.mk_add_mk]
        push_cast
        constructor <;> norm_num

private lemma type11_signature_eq_after
    {m n j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n)
    (hj : 2 * n + 3 < j) :
    signature (Chromosome.prime^[j] (Y11 h_le hε).1) =
      signature (Chromosome.prime^[j] (X11 h_le hε).1) := by
  simp only [X11_eq, Y11_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have h1 : 2 * m + 3 - j = 0 := by omega
  have h2 : 2 * m + 1 - j = 0 := by omega
  have h3 : 2 * n + 3 - j = 0 := by omega
  have h4 : 2 * n + 4 - j = 0 := by omega
  simp [h1, h2, h3, h4, Gene.ofRank_zero]

private lemma type11_signature_eq_before
    {m n j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n)
    (hj : j ≤ 2 * m + 1) :
    signature (Chromosome.prime^[j] (Y11 h_le hε).1) =
      signature (Chromosome.prime^[j] (X11 h_le hε).1) := by
  simp only [X11_eq, Y11_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have eq1 : 2 * m + 3 - j = 2 * m + 1 - j + 2 := by omega
  have eq2 : 2 * n + 4 - j = 2 * n + 3 - j + 1 := by omega
  rw [eq1, signature_ofRank_eq₂' (2 * m + 1 - j), eq2]
  have hPN1 := type11_pos_neg_signature_sum_fst (2 * n + 3 - j)
  have hPN2 := type11_pos_neg_signature_sum_snd (2 * n + 3 - j)
  ext <;> simp only [signature_ofRank_nonPolarized, Prod.fst_add, Prod.snd_add] <;>
    push_cast at * <;> linarith

set_option linter.flexible false in
/-- At the first active level of type11, the target exceeds the source only in
the component opposite to the shifted polarized gene. -/
private lemma type11_signature_at_pred
    {m n : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n) :
    signature (Chromosome.prime^[2 * m + 2] (Y11 h_le hε).1) =
      signature (Gene.ofRank 1 (-ε)) +
        signature (Chromosome.prime^[2 * m + 2] (X11 h_le hε).1) := by
  simp only [X11_eq, Y11_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have hεsrc : 2 * m + 3 - (2 * m + 2) = 1 := by omega
  have hεtgt : 2 * m + 1 - (2 * m + 2) = 0 := by omega
  have hsrcpair : 2 * n + 3 - (2 * m + 2) = 2 * n + 1 - 2 * m := by omega
  have htgtpair : 2 * n + 4 - (2 * m + 2) = 2 * n + 2 - 2 * m := by omega
  have hsucc : 2 * n + 2 - 2 * m = (2 * n + 1 - 2 * m) + 1 := by omega
  rw [hεsrc, hεtgt, hsrcpair, htgtpair, hsucc]
  simp only [Gene.ofRank_zero, map_zero, zero_add, signature_ofRank_nonPolarized]
  have hPN1 := type11_pos_neg_signature_sum_fst (2 * n + 1 - 2 * m)
  have hPN2 := type11_pos_neg_signature_sum_snd (2 * n + 1 - 2 * m)
  cases ε <;> simp [GeneType.neg_positive, GeneType.neg_negative,
    signature_ofRank_one_positive, signature_ofRank_one_negative] at hε ⊢ <;>
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> linarith

/-- Through the middle active interval of type11, the target exceeds the source
by exactly the diagonal slack `(1,1)`. -/
private lemma type11_signature_mid
    {m n j : ℕ} {ε : GeneType} {hε : ε ≠ .NonPolarized} (h_le : m ≤ n)
    (hjlo : 2 * m + 2 < j) (hjhi : j ≤ 2 * n + 3) :
    signature (Chromosome.prime^[j] (Y11 h_le hε).1) =
      ((1 : ℚ), (1 : ℚ)) +
        signature (Chromosome.prime^[j] (X11 h_le hε).1) := by
  simp only [X11_eq, Y11_eq, iterate_map_add, prime_iterate_ofRank, map_add]
  have hεsrc : 2 * m + 3 - j = 0 := by omega
  have hεtgt : 2 * m + 1 - j = 0 := by omega
  have hpair : 2 * n + 4 - j = (2 * n + 3 - j) + 1 := by omega
  rw [hεsrc, hεtgt, hpair]
  simp only [Gene.ofRank_zero, map_zero, zero_add, signature_ofRank_nonPolarized]
  have hPN1 := type11_pos_neg_signature_sum_fst (2 * n + 3 - j)
  have hPN2 := type11_pos_neg_signature_sum_snd (2 * n + 3 - j)
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;>
    push_cast at * <;> linarith

set_option maxHeartbeats 800000 in
-- The proof expands `le_iff_dominates` and two iterated-signature decompositions;
-- the resulting product-valued expressions are large but purely local.
/-- Dominance for a type11 target plus an arbitrary rest term, assuming the
source decomposition and the diagonal slack through the active type11 window. -/
lemma type11_target_add_rest_le_of_diagonal_gap
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1) (restval : Chromosome)
    (hXeq : (X11 h_le hε).1 + restval = X.1.1)
    (hgap_pred :
      signature (Gene.ofRank 1 (-ε)) +
          signature (Chromosome.prime^[2 * m + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * m + 2] Y.1.1))
    (hgap_mid : ∀ j, 2 * m + 2 < j → j ≤ 2 * n + 3 →
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) :
    (Y11 h_le hε).1 + restval ≤ Y.1.1 := by
  rw [le_iff_dominates]
  intro j
  rw [iterate_map_add, map_add]
  have hdecomp :
      signature (Chromosome.prime^[j] X.1.1) =
        signature (Chromosome.prime^[j] (X11 h_le hε).1) +
          signature (Chromosome.prime^[j] restval) := by
    conv_lhs => rw [← hXeq]
    rw [iterate_map_add, map_add]
  by_cases hj_before : j ≤ 2 * m + 1
  · rw [type11_signature_eq_before h_le hj_before, ← hdecomp]
    exact le_iff_dominates.mp hXY.le j
  · by_cases hj_pred : j = 2 * m + 2
    · subst j
      rw [type11_signature_at_pred h_le]
      calc
        signature (Gene.ofRank 1 (-ε)) +
              signature (Chromosome.prime^[2 * m + 2] (X11 h_le hε).1) +
            signature (Chromosome.prime^[2 * m + 2] restval)
            = signature (Gene.ofRank 1 (-ε)) +
              (signature (Chromosome.prime^[2 * m + 2] (X11 h_le hε).1) +
                signature (Chromosome.prime^[2 * m + 2] restval)) := by abel
        _ = signature (Gene.ofRank 1 (-ε)) +
              signature (Chromosome.prime^[2 * m + 2] X.1.1) := by rw [← hdecomp]
        _ ≤ signature (Chromosome.prime^[2 * m + 2] Y.1.1) := hgap_pred
    · by_cases hj : j ≤ 2 * n + 3
      · rw [type11_signature_mid h_le (by omega : 2 * m + 2 < j) hj]
        calc
          ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] (X11 h_le hε).1) +
              signature (Chromosome.prime^[j] restval)
              = ((1 : ℚ), (1 : ℚ)) +
                (signature (Chromosome.prime^[j] (X11 h_le hε).1) +
                  signature (Chromosome.prime^[j] restval)) := by abel
          _ = ((1 : ℚ), (1 : ℚ)) +
                signature (Chromosome.prime^[j] X.1.1) := by rw [← hdecomp]
          _ ≤ signature (Chromosome.prime^[j] Y.1.1) :=
            hgap_mid j (by omega) hj
      · have hj_after : 2 * n + 3 < j := by omega
        rw [type11_signature_eq_after h_le hj_after, ← hdecomp]
        exact le_iff_dominates.mp hXY.le j

/-- A thin theorem-level wrapper for type11.  The caller supplies the concrete
source decomposition and the dominance bound after replacing the source by the
type11 target. -/
lemma exists_mutation_le_type11_of_decomp
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N) (restval : Chromosome)
    (hXeq : (X11 h_le hε).1 + restval = X.1.1)
    (hrest : restval ∈ Mix (2 • Lambda, Pi))
    (hZle : (Y11 h_le hε).1 + restval ≤ Y.1.1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let rest : Mix (2 • Lambda, Pi) := ⟨restval, hrest⟩
  refine ⟨⟨(Y11 h_le hε).1 + restval,
      add_mem (Y11 h_le hε).2 hrest⟩, ?_, hZle⟩
  exact (Subtype.ext hXeq :
      (X11 h_le hε : Mix (2 • Lambda, Pi)) + rest = X.1) ▸
    Step.mk (X11 h_le hε) (Y11 h_le hε) rest
      (Primitive.type11 ε hε h_le)

/-- Concrete-gene wrapper for type11.  This packages the source decomposition
and rest membership; the caller still supplies the final dominance bound for
the type11 target plus the rest. -/
lemma exists_mutation_le_type11_of_genes
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N)
    (gε gpos gneg : Gene)
    (hgε : gε.type = ε)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgε_rank : gε.rank = 2 * m + 3)
    (hgpos_rank : gpos.rank = 2 * n + 3)
    (hrank : gpos.rank = gneg.rank)
    (hεcopy : 1 ≤ X.1.1 gε)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hne_ε_pos : gε ≠ gpos) (hne_ε_neg : gε ≠ gneg) (hne_pos_neg : gpos ≠ gneg)
    (hZle :
      (Y11 h_le hε).1 +
          (X.1.1 - Finsupp.single gε 1 -
            Finsupp.single gpos 1 - Finsupp.single gneg 1) ≤
        Y.1.1) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gε 1 -
      Finsupp.single gpos 1 - Finsupp.single gneg 1
  have hoddε : Odd gε.rank := by rw [hgε_rank]; exact ⟨m + 1, by ring⟩
  have hoddpos : Odd gpos.rank := by rw [hgpos_rank]; exact ⟨n + 1, by ring⟩
  have hoddneg : Odd gneg.rank := hrank ▸ hoddpos
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi
        (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hoddε) hoddpos)
      hoddneg
  have hgε_eq :
      Gene.ofRank (2 * m + 3) ε =
        (Finsupp.single gε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gε)
    rwa [hgε_rank, hgε] at h
  have hgpos_eq :
      Gene.ofRank (2 * n + 3) GeneType.Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hgpos_rank, hgpos] at h
  have hgneg_eq :
      Gene.ofRank (2 * n + 3) GeneType.Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hgneg, ← hrank, hgpos_rank] at h
  have hX11val :
      (X11 h_le hε).1 =
        Finsupp.single gε 1 + Finsupp.single gpos 1 +
          Finsupp.single gneg 1 := by
    rw [X11_eq, hgε_eq, hgpos_eq, hgneg_eq]
  have hXeq : (X11 h_le hε).1 + restval = X.1.1 := by
    rw [hX11val]
    exact Mix2LambdaSection17.single_triple_add_rest
      hεcopy hpos hneg hne_ε_pos hne_ε_neg hne_pos_neg
  exact exists_mutation_le_type11_of_decomp hε h_le X Y restval hXeq
    rest_mem hZle

set_option maxHeartbeats 800000 in
-- The wrapper constructs the concrete source decomposition and then invokes
-- the preceding dominance lemma; elaborating the concrete `Finsupp` rest term
-- needs a larger local heartbeat budget.
/-- Concrete-gene wrapper for type11 with the standard diagonal-gap profile.
The caller supplies the diagonal slack only through the active type11 window;
outside that window the source and target have identical iterated signatures. -/
lemma exists_mutation_le_type11_of_genes_with_diagonal_gap
    {N m n : ℕ} {ε : GeneType} (hε : ε ≠ .NonPolarized) (h_le : m ≤ n)
    (X Y : nMix2LambdaPi N) (hXY : X.1 < Y.1)
    (gε gpos gneg : Gene)
    (hgε : gε.type = ε)
    (hgpos : gpos.type = .Positive) (hgneg : gneg.type = .Negative)
    (hgε_rank : gε.rank = 2 * m + 3)
    (hgpos_rank : gpos.rank = 2 * n + 3)
    (hrank : gpos.rank = gneg.rank)
    (hεcopy : 1 ≤ X.1.1 gε)
    (hpos : 1 ≤ X.1.1 gpos) (hneg : 1 ≤ X.1.1 gneg)
    (hne_ε_pos : gε ≠ gpos) (hne_ε_neg : gε ≠ gneg) (hne_pos_neg : gpos ≠ gneg)
    (hgap_pred :
      signature (Gene.ofRank 1 (-ε)) +
          signature (Chromosome.prime^[2 * m + 2] X.1.1) ≤
        signature (Chromosome.prime^[2 * m + 2] Y.1.1))
    (hgap_mid : ∀ j, 2 * m + 2 < j → j ≤ 2 * n + 3 →
      ((1 : ℚ), (1 : ℚ)) +
          signature (Chromosome.prime^[j] X.1.1) ≤
        signature (Chromosome.prime^[j] Y.1.1)) :
    ∃ Z : Mix (2 • Lambda, Pi), Mix2LambdaPi.Step X.1 Z ∧ Z ≤ Y.1 := by
  let restval : Chromosome :=
    X.1.1 - Finsupp.single gε 1 -
      Finsupp.single gpos 1 - Finsupp.single gneg 1
  have hoddε : Odd gε.rank := by rw [hgε_rank]; exact ⟨m + 1, by ring⟩
  have hoddpos : Odd gpos.rank := by rw [hgpos_rank]; exact ⟨n + 1, by ring⟩
  have hoddneg : Odd gneg.rank := hrank ▸ hoddpos
  have rest_mem : restval ∈ Mix (2 • Lambda, Pi) :=
    sub_single_one_mem_Mix_2Lambda_Pi
      (sub_single_one_mem_Mix_2Lambda_Pi
        (sub_single_one_mem_Mix_2Lambda_Pi X.1.2 hoddε) hoddpos)
      hoddneg
  have hgε_eq :
      Gene.ofRank (2 * m + 3) ε =
        (Finsupp.single gε 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gε)
    rwa [hgε_rank, hgε] at h
  have hgpos_eq :
      Gene.ofRank (2 * n + 3) GeneType.Positive =
        (Finsupp.single gpos 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gpos)
    rwa [hgpos_rank, hgpos] at h
  have hgneg_eq :
      Gene.ofRank (2 * n + 3) GeneType.Negative =
        (Finsupp.single gneg 1 : Chromosome) := by
    have h := Gene.ofRank_eq_gene (g := gneg)
    rwa [hgneg, ← hrank, hgpos_rank] at h
  have hX11val :
      (X11 h_le hε).1 =
        Finsupp.single gε 1 + Finsupp.single gpos 1 +
          Finsupp.single gneg 1 := by
    rw [X11_eq, hgε_eq, hgpos_eq, hgneg_eq]
  have hXeq : (X11 h_le hε).1 + restval = X.1.1 := by
    rw [hX11val]
    exact Mix2LambdaSection17.single_triple_add_rest
      hεcopy hpos hneg hne_ε_pos hne_ε_neg hne_pos_neg
  have hZle : (Y11 h_le hε).1 + restval ≤ Y.1.1 :=
    type11_target_add_rest_le_of_diagonal_gap hε h_le X Y hXY
      restval hXeq hgap_pred hgap_mid
  exact exists_mutation_le_type11_of_genes hε h_le X Y
    gε gpos gneg hgε hgpos hgneg hgε_rank hgpos_rank hrank
    hεcopy hpos hneg hne_ε_pos hne_ε_neg hne_pos_neg hZle

end Mix2LambdaPi
