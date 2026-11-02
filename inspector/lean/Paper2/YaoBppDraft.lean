import Paper2.YaoMainDraft
import Paper2.A4Amplification
import Paper2.A4DocFix
import Paper2.A4Definitions

/-! Unit 5 segment Y14 (lane a-yao-owner-4): T32 `yao:bpp` (lock v12 Y:373-393) as a
class-level shell over the Y13 composition.

Lock: "Fix `u ≥ 0`. A bounded-error randomized polynomial-time algorithm estimating any of
`D_A^alt`, `D_B^alt`, `D_free^alt`, or `Y_free` within additive error `u` on every explicit total
Boolean matrix implies `NP ⊆ BPP`."  Proof (Y:382-392): a gap `g`, the midpoint test, median
amplification, a total failure below `1/3`.

Author decisions, all explicit here:
* D-A1 (reduction model): the DRAFT two-cell model of `Y4Main` (the T25 machine `yaoMain`); the
  estimator is the unit-4 DRAFT `RandomizedAlgorithm` (a parameter `E`, D-A1 option of A4-S1).
* D-Y3 (estimator format): the input is the R-Y3 DRAFT word `encodeInstance i`; the estimated
  quantity is one of the four measures (`YaoMeasure`) of the decoded table (`yaoTarget`); the
  numeric output decoder `decode : List Bool → Option ℝ` is a parameter.
* D-A4 (BPP): an arbitrary class predicate `C`; the two machine-level facts every option must
  supply are NAMED HYPOTHESES: reduction closure (`ClassLemmas.ReductionClosed C`) and the
  composition contract `DA4MidpointContract` (the midpoint procedure built from a polynomial
  estimator and the polynomial T25 machine, with error `≤ 1/3`, decides a language of `C`).
* D-A5 (Cook-Levin): `EncodedComplexity.NPHard G.L` for the D-A2 language of the record.
* AD-1: the DRAFT record `G : GLSourceDraft (gapParameter g)` (parameter).

Proof route (deviation from the lock's route, not from its statement): all four measures lie in
the window `[D_A - 2, D_A + 1]` (admitted `starter_abs_difference_le`, `free_starter_comparison`,
`receiver_integer_comparison`), so ONE midpoint test with budget `B + 1` and gap `g - 3`
(requiring `2u + 3 < g`) serves all four; the lock instead handles `D_B` by transposed printing
(no physical transpose printer exists) and uses `g > 2u + 2`.  Amplification is the admitted
147-run lower median to `99/100` (lock: to `511/512`); total error `1/512 + 1/100 < 1/3`.
The final step reuses the admitted `DocFix.np_subset_of_hard_mem` by exact name.

No ledger row is closed; no Yao endpoint completion claim. -/

noncomputable section

namespace Paper2.YaoBppDraft

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2 Paper2.FiniteLaw
open Paper2.Yao
open Paper2.YaoLookup
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoMaterialization
open Paper2.YaoSourceCodec
open Paper2.YaoFrame
open Paper2.YaoX05Draft
open Paper2.YaoMainDraft
open Paper2.YaoT26Draft
open Paper2.Unit4Shell.Definitions
open Paper2.Unit4Shell.Amplification

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- DRAFT (D-Y3): which of the four alternating measures is estimated. -/
inductive YaoMeasure
  | dA | dB | dFree | yFree

/-- DRAFT (D-Y3): the value of the measure on an encoded instance's table game. -/
def YaoMeasure.eval (m : YaoMeasure) (i : EncodedCommunication.Instance) : ℕ :=
  match m with
  | .dA => Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)
  | .dB => Dalt .bob (ProtocolVerifier.tableGame i.rows i.cols i.table)
  | .dFree => Dfree (ProtocolVerifier.tableGame i.rows i.cols i.table)
  | .yFree => Yfree (ProtocolVerifier.tableGame i.rows i.cols i.table)

/-- Every measure lies in `[D_A - 2, D_A + 1]` (admitted comparisons, exact names). -/
theorem measure_window (m : YaoMeasure) (i : EncodedCommunication.Instance) :
    Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ m.eval i + 2 ∧
      m.eval i ≤ Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) + 1 := by
  cases m with
  | dA => simp [YaoMeasure.eval]
  | dB =>
      have h := abs_le.mp (starter_abs_difference_le (ProtocolVerifier.tableGame i.rows i.cols i.table))
      simp only [YaoMeasure.eval]
      constructor <;> omega
  | dFree =>
      have h := free_starter_comparison (ProtocolVerifier.tableGame i.rows i.cols i.table)
      simp only [YaoMeasure.eval]
      constructor <;> omega
  | yFree =>
      have h := receiver_integer_comparison (ProtocolVerifier.tableGame i.rows i.cols i.table)
      simp only [YaoMeasure.eval]
      constructor <;> omega

/-- DRAFT (D-Y3): the estimated quantity on "every explicit total Boolean matrix": defined on
exactly the words that decode to an instance. -/
def yaoTarget (m : YaoMeasure) (w : List Bool) : Option ℕ :=
  (decodeInstance w).map m.eval

theorem reps_pos : 0 < reps := by decide

/-- The midpoint threshold read from the printed word: `threshold + 1 + k/2`. -/
def thr (w : List Bool) : ℕ := ((decodeInstance w).map (fun i => i.threshold)).getD 0

def midpoint (k : ℕ) (w : List Bool) : ℝ :=
  (thr w : ℝ) + 1 + (k : ℝ) / 2

/-- The numeric estimate of one estimator run (`0` on an undecodable output). -/
def estimate (E : RandomizedAlgorithm) (decode : List Bool → Option ℝ) (w : List Bool)
    (tape : Fin (E.tapeLength w) → Bool) : ℝ :=
  (decode (E.output w (List.ofFn tape))).getD 0

/-- Conditional acceptance probability of the midpoint test on a fixed printed word: `147`
independent estimator runs, lower median below the midpoint. -/
def acceptOnWord (E : RandomizedAlgorithm) (decode : List Bool → Option ℝ) (k : ℕ)
    (w : List Bool) : ℝ :=
  ((uniformTape (E.tapeLength w)).iid reps).prob (fun ts =>
    lowerMedian reps_pos (fun i => estimate E decode w (ts i)) < midpoint k w)

/-- Acceptance probability of the composed procedure (T25 machine tape `bits`, then the
midpoint test on the printed word): the `serializedTapeLaw`-average of `acceptOnWord`. -/
def acceptProb (g : ℕ) (G : GLSourceDraft (gapParameter g)) (E : RandomizedAlgorithm)
    (decode : List Bool → Option ℝ) (input : List Bool) : ℝ :=
  ∑ bits, (serializedTapeLaw (gapParameter g) (paddedEdgeBits (src G input).2.1) 10).weight bits *
    acceptOnWord E decode (g - 3) (mainWord G 10 input bits)

theorem avg_ge {α : Type*} [Fintype α] (ρ : FiniteLaw α) (q : α → ℝ) (a : ℝ)
    (h : ∀ b, a ≤ q b) : a ≤ ∑ b, ρ.weight b * q b := by
  calc a = ∑ b, ρ.weight b * a := by rw [← Finset.sum_mul, ρ.total, one_mul]
    _ ≤ ∑ b, ρ.weight b * q b :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h b) (ρ.nonneg b)

theorem avg_le {α : Type*} [Fintype α] (ρ : FiniteLaw α) (q : α → ℝ) (Good : α → Prop) (a : ℝ)
    (hq1 : ∀ b, q b ≤ 1) (hgood : ∀ b, Good b → q b ≤ a) (ha : 0 ≤ a) :
    ∑ b, ρ.weight b * q b ≤ a + ρ.prob (fun b => ¬ Good b) := by
  classical
  have hsplit : ∀ b, ρ.weight b * q b ≤ ρ.weight b * a + (if ¬ Good b then ρ.weight b else 0) := by
    intro b
    by_cases hb : Good b
    · simp only [hb, not_true_eq_false, if_false, add_zero]
      exact mul_le_mul_of_nonneg_left (hgood b hb) (ρ.nonneg b)
    · simp only [hb, not_false_eq_true, if_true]
      have := mul_le_mul_of_nonneg_left (hq1 b) (ρ.nonneg b)
      nlinarith [ρ.nonneg b]
  calc ∑ b, ρ.weight b * q b ≤ ∑ b, (ρ.weight b * a + (if ¬ Good b then ρ.weight b else 0)) :=
        Finset.sum_le_sum fun b _ => hsplit b
    _ = a + ρ.prob (fun b => ¬ Good b) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ρ.total, one_mul]
        unfold FiniteLaw.prob
        congr 1
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : Good b <;> simp [hb]

theorem avg_no {α : Type*} [Fintype α] (ρ : FiniteLaw α) (q : α → ℝ) (Good : α → Prop)
    (hq1 : ∀ b, q b ≤ 1) (hgood : ∀ b, Good b → q b ≤ 1 / 100)
    (hbad : ρ.prob (fun b => ¬ Good b) ≤ 1 / 512) :
    ∑ b, ρ.weight b * q b ≤ 1 / 512 + 1 / 100 := by
  have h := avg_le ρ q Good (1 / 100) hq1 hgood (by norm_num)
  linarith

/-- Complement bound consuming a majority guarantee: if `A` excludes `B` and
`B` has probability `≥ 99/100`, then `A` has probability `≤ 1/100`. -/
theorem prob_le_of_excl {α : Type*} [Fintype α] (μ : FiniteLaw α) (B A : α → Prop)
    (hB : 99 / 100 ≤ μ.prob B) (h : ∀ x, A x → ¬ B x) : μ.prob A ≤ 1 / 100 := by
  have hm := FiniteLaw.prob_mono μ (E := A) (F := fun x => ¬ B x) h
  rw [prob_not] at hm
  linarith

open Classical in
/-- Median above the midpoint from a majority of runs within `a` of a value `c ≥ B + k`
(generalises the admitted `median_midpoint_no`, which needs `c = B + k`). -/
theorem median_midpoint_no_ge {r : ℕ} (hr : 0 < r) (v : Fin r → ℝ) (a : ℝ) (c B k : ℕ)
    (hc : B + k ≤ c) (hk : 2 * a < k)
    (hmaj : r < 2 * Fintype.card {i : Fin r // |v i - c| ≤ a}) :
    (B : ℝ) + (k : ℝ) / 2 < lowerMedian hr v := by
  apply lt_lowerMedian_of_majority
  rw [Fintype.card_subtype] at hmaj
  refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have h := (abs_le.mp hi).1
  have hc' : ((B + k : ℕ) : ℝ) ≤ c := by exact_mod_cast hc
  push_cast at hc'
  linarith

/-- One word, YES side: if the target is `c ≤ threshold + 1` and the estimator is correct
within `u` with probability `≥ 2/3`, the midpoint test accepts with probability `≥ 99/100`. -/
theorem acceptOnWord_yes (E : RandomizedAlgorithm) (decode : List Bool → Option ℝ) (u : ℝ)
    (k : ℕ) (hk : 2 * u < k) (w : List Bool) (c : ℕ)
    (hc : c ≤ (thr w) + 1)
    (hE : 2 / 3 ≤ E.prob w (fun out => ∃ v, decode out = some v ∧ |v - c| ≤ u)) :
    99 / 100 ≤ acceptOnWord E decode k w := by
  classical
  have h := iid_majority_good_ge (uniformTape (E.tapeLength w))
    (fun tape => ∃ v, decode (E.output w (List.ofFn tape)) = some v ∧ |v - c| ≤ u) hE
  refine h.trans (FiniteLaw.prob_mono _ fun ts hts => ?_)
  rw [Fintype.card_subtype] at hts
  rw [lowerMedian_lt_iff]
  refine lt_of_lt_of_le hts (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨v, hv, hvu⟩ := hi
  have hest : estimate E decode w (ts i) = v := by simp [estimate, hv]
  rw [hest]
  have hc' : (c : ℝ) ≤ ((thr w : ℕ) : ℝ) + 1 := by
    exact_mod_cast hc
  have h1 := (abs_le.mp hvu).2
  unfold midpoint
  linarith

/-- One word, NO side: if the target is `c ≥ threshold + 1 + k`, the midpoint test accepts
with probability `≤ 1/100`. -/
theorem acceptOnWord_no (E : RandomizedAlgorithm) (decode : List Bool → Option ℝ) (u : ℝ)
    (k : ℕ) (hk : 2 * u < k) (w : List Bool) (c : ℕ)
    (hc : (thr w) + 1 + k ≤ c)
    (hE : 2 / 3 ≤ E.prob w (fun out => ∃ v, decode out = some v ∧ |v - c| ≤ u)) :
    acceptOnWord E decode k w ≤ 1 / 100 := by
  classical
  have h := iid_majority_good_ge (uniformTape (E.tapeLength w))
    (fun tape => ∃ v, decode (E.output w (List.ofFn tape)) = some v ∧ |v - c| ≤ u) hE
  unfold acceptOnWord
  refine prob_le_of_excl _ _ _ h fun ts hacc hmaj => ?_
  rw [Fintype.card_subtype] at hmaj
  have hgt : midpoint k w < lowerMedian reps_pos (fun i => estimate E decode w (ts i)) := by
    apply lt_lowerMedian_of_majority
    refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨v, hv, hvu⟩ := hi
    have hest : estimate E decode w (ts i) = v := by simp [estimate, hv]
    rw [hest]
    have hc' : ((thr w : ℕ) : ℝ) + 1 + k ≤ (c : ℝ) := by exact_mod_cast hc
    have h1 := (abs_le.mp hvu).1
    unfold midpoint
    linarith
  exact absurd hacc (not_lt.mpr hgt.le)

/-- **Error bounds of the composed midpoint procedure (probability core of T32).**  For the
DRAFT record `G` (T25 via `yao_main_draft`), a measure `m`, an estimator `E` of `yaoTarget m`
within additive error `u ≥ 0` (`E.Estimates`, D-Y3 decoder `decode`), and a gap `g` with
`2u + 3 < g`: members are accepted with probability `≥ 99/100`, non-members with probability
`≤ 1/512 + 1/100 < 1/3`. -/
theorem yao_midpoint_errors (g : ℕ) (G : GLSourceDraft (gapParameter g)) (m : YaoMeasure)
    (E : RandomizedAlgorithm) (decode : List Bool → Option ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hg : 2 * u + 3 < g) (hE : E.Estimates (yaoTarget m) decode u) (input : List Bool) :
    (input ∈ G.L → 99 / 100 ≤ acceptProb g G E decode input) ∧
      (input ∉ G.L → acceptProb g G E decode input ≤ 1 / 512 + 1 / 100) ∧
      ((1 / 512 : ℝ) + 1 / 100 < 1 / 3) := by
  have hg3 : 3 ≤ g := by
    have : (3 : ℝ) < g := by linarith
    exact_mod_cast this.le
  have hk : 2 * u < ((g - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hg3]; push_cast; linarith
  obtain ⟨C, d, hmain⟩ := yao_main_draft g G
  obtain ⟨_, hbits, hyes, hno⟩ := hmain input
  -- per tape: the decoded instance, its measure and the estimator guarantee
  have hword : ∀ bits : SerializedTape (gapParameter g) (paddedEdgeBits (src G input).2.1) 10,
      decodeInstance (mainWord G 10 input bits) =
        some (yaoInstanceDraft (gapParameter g) 10 (src G input) bits) :=
    fun bits => (hbits bits).2.2.1
  have hthr : ∀ bits : SerializedTape (gapParameter g) (paddedEdgeBits (src G input).2.1) 10,
      thr (mainWord G 10 input bits) =
        (yaoInstanceDraft (gapParameter g) 10 (src G input) bits).threshold := by
    intro bits; unfold thr; rw [hword bits]; rfl
  have hest : ∀ bits : SerializedTape (gapParameter g) (paddedEdgeBits (src G input).2.1) 10,
      2 / 3 ≤ E.prob (mainWord G 10 input bits) (fun out => ∃ v, decode out = some v ∧
        |v - (m.eval (yaoInstanceDraft (gapParameter g) 10 (src G input) bits) : ℕ)| ≤ u) := by
    intro bits
    exact hE _ _ (by simp [yaoTarget, hword bits])
  refine ⟨fun hmem => ?_, fun hnot => ?_, by norm_num⟩
  · apply avg_ge
    intro bits
    obtain ⟨i, hi, hDi⟩ := (hyes hmem bits).1
    rw [hword bits] at hi
    cases Option.some.inj hi
    have hw := (measure_window m (yaoInstanceDraft (gapParameter g) 10 (src G input) bits)).2
    exact acceptOnWord_yes E decode u (g - 3) hk _ _ (by rw [hthr bits]; omega) (hest bits)
  · have hbad : (serializedTapeLaw (gapParameter g) (paddedEdgeBits (src G input).2.1) 10).prob
        (fun bits => ¬ ∃ i, decodeInstance (mainWord G 10 input bits) = some i ∧
          i.threshold + g ≤ Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)) ≤
        1 / 512 := by
      rw [prob_not]; linarith [hno hnot]
    have hgood : ∀ bits : SerializedTape (gapParameter g) (paddedEdgeBits (src G input).2.1) 10,
        (∃ i, decodeInstance (mainWord G 10 input bits) = some i ∧
          i.threshold + g ≤ Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)) →
        acceptOnWord E decode (g - 3) (mainWord G 10 input bits) ≤ 1 / 100 := by
      intro bits hgood
      obtain ⟨i, hi, hDi⟩ := hgood
      rw [hword bits] at hi
      cases Option.some.inj hi
      have hw := (measure_window m (yaoInstanceDraft (gapParameter g) 10 (src G input) bits)).1
      exact acceptOnWord_no E decode u (g - 3) hk _ _ (by rw [hthr bits]; omega) (hest bits)
    exact avg_no _ _ _ (fun bits => FiniteLaw.prob_le_one _ _) hgood hbad

/-- **D-A4 composition contract (NAMED HYPOTHESIS, not proved).**  For the chosen class `C`
(the author's `BPP` option): if the estimator `E` is polynomial and the T25 machine of `G` is
polynomial (clock and random bits), then every language decided with two-sided error `≤ 1/3`
by the composed midpoint procedure (T25 tape; `147` independent runs of `E` on the printed
word; lower median; comparison with `threshold + 1 + (g-3)/2`) is in `C`.  This is the
machine-level obligation that the procedure is a bounded-error randomized polynomial-time
algorithm of the D-A4 model; every D-A4 option must discharge it for its own machines. -/
def DA4MidpointContract (C : BinaryLanguage → Prop) (g : ℕ) (G : GLSourceDraft (gapParameter g))
    (E : RandomizedAlgorithm) (decode : List Bool → Option ℝ) : Prop :=
  E.Polynomial →
  (∃ Cc d : ℕ, ∀ input : List Bool,
    sourceTime G input + frameClock 10 (src G input) + 1 ≤ Cc * (input.length + 1) ^ d ∧
    tapeBitCount (gapParameter g) (paddedEdgeBits (src G input).2.1) 10 ≤
      Cc * (input.length + 1) ^ d) →
  ∀ L : BinaryLanguage,
    (∀ input, (input ∈ L → 2 / 3 ≤ acceptProb g G E decode input) ∧
      (input ∉ L → acceptProb g G E decode input ≤ 1 / 3)) → C L

/-- **T32 `yao:bpp` (lock v12 Y:373-393), class-level shell.**  Fix `u ≥ 0` and a gap `g` with
`2u + 3 < g`.  For every class `C` closed under the banked reductions (D-A4 closure, named
hypothesis), every DRAFT record `G : GLSourceDraft (gapParameter g)` whose D-A2 language is
NP-hard in the banked sense (D-A5 Cook-Levin contract, hypothesis), every polynomial DRAFT
estimator `E` of any of the four measures within additive error `u` on every decodable
explicit matrix word (D-Y3 format), and the D-A4 composition contract: `NP ⊆ C`. -/
theorem yao_bpp_draft (C : BinaryLanguage → Prop)
    (hC : Paper2.Unit4Shell.ClassLemmas.ReductionClosed C)
    (u : ℝ) (hu : 0 ≤ u) (g : ℕ) (hg : 2 * u + 3 < g) (G : GLSourceDraft (gapParameter g))
    (hard : NPHard G.L) (m : YaoMeasure) (E : RandomizedAlgorithm)
    (decode : List Bool → Option ℝ) (hpoly : E.Polynomial)
    (hE : E.Estimates (yaoTarget m) decode u)
    (hDA4 : DA4MidpointContract C g G E decode) :
    ∀ L, InNP L → C L := by
  have ht : 1 ≤ gapParameter g := by have := (gapParameter_admissible g).1; omega
  obtain ⟨Cc, d, hpolyT⟩ := yao_main_poly G 10 ht
  have hmem : C G.L := hDA4 hpoly ⟨Cc, d, fun input => ⟨(hpolyT input).1, (hpolyT input).2.1⟩⟩
    G.L (fun input =>
      ⟨fun h => le_trans (by norm_num) ((yao_midpoint_errors g G m E decode u hu hg hE input).1 h),
       fun h => le_trans ((yao_midpoint_errors g G m E decode u hu hg hE input).2.1 h)
        (by norm_num)⟩)
  exact Paper2.Unit4Shell.DocFix.np_subset_of_hard_mem C hC hard hmem

/-- **T32 with the gap chosen from `u`** (the lock's "Fix `u ≥ 0`"): for a family of DRAFT
records `GF t` (one per `t`, AD-1) sharing one NP-hard D-A2 language `L3`, the gap
`g = ⌈2u⌉₊ + 4` is used. -/
theorem yao_bpp_family (C : BinaryLanguage → Prop)
    (hC : Paper2.Unit4Shell.ClassLemmas.ReductionClosed C)
    (u : ℝ) (hu : 0 ≤ u) (GF : (t : ℕ) → GLSourceDraft t) (L3 : BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3) (hard : NPHard L3) (m : YaoMeasure) (E : RandomizedAlgorithm)
    (decode : List Bool → Option ℝ) (hpoly : E.Polynomial)
    (hE : E.Estimates (yaoTarget m) decode u)
    (hDA4 : ∀ g, DA4MidpointContract C g (GF (gapParameter g)) E decode) :
    ∀ L, InNP L → C L := by
  have hg : 2 * u + 3 < ((⌈2 * u⌉₊ + 4 : ℕ) : ℝ) := by
    have := Nat.le_ceil (2 * u)
    push_cast; linarith
  exact yao_bpp_draft C hC u hu (⌈2 * u⌉₊ + 4) hg (GF (gapParameter (⌈2 * u⌉₊ + 4)))
    (by rw [hL]; exact hard) m E decode hpoly hE (hDA4 _)

end Paper2.YaoBppDraft

end

#print axioms Paper2.YaoBppDraft.measure_window
#print axioms Paper2.YaoBppDraft.avg_ge
#print axioms Paper2.YaoBppDraft.avg_le
#print axioms Paper2.YaoBppDraft.median_midpoint_no_ge
#print axioms Paper2.YaoBppDraft.acceptOnWord_yes
#print axioms Paper2.YaoBppDraft.acceptOnWord_no
#print axioms Paper2.YaoBppDraft.yao_midpoint_errors
#print axioms Paper2.YaoBppDraft.yao_bpp_draft
#print axioms Paper2.YaoBppDraft.yao_bpp_family
