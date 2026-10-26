import CurrentAdditive.V39ActualYaoEndpoint
import CurrentAdditive.V39MinimalInstance

/-! Exact canonical-table consumer for the minimal source interface. The
original approved full source record instantiates this interface at the same
arity. No strengthened small-set epsilon is assumed. The numerical law is
only at each selected table's requested midpoint and actual random outputs. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39MinimalActualEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.V39ActualYaoEndpoint
open CurrentAdditive.YaoMinimalSource
open CurrentAdditive.V38Encoded (edgeBits)
open CurrentAdditive.SmallBias
open Paper2 Paper2.Yao Paper2.YaoBppDraft

abbrev selectedInstance {t : ℕ} (G : SourceInput t) (input : List Bool) : Instance :=
  V39SourceRenderer.sourceInstance (selectedSource G input)

def matrixWord {t : ℕ} (G : SourceInput t) (input : List Bool) : List Bool :=
  let i := selectedInstance G input
  AModel.matrixWord i.rows i.cols i.table

def midpointNumerator {t : ℕ} (G : SourceInput t) (input : List Bool) : ℕ :=
  2 * (selectedInstance G input).threshold + (2 * t - 8)

def sourceWord {t : ℕ} (G : SourceInput t) (input : List Bool) : List Bool :=
  natField (midpointNumerator G input) ++ matrixWord G input

theorem selectedInstance_gap {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t) (input : List Bool) :
    (input ∈ G.L → Dalt .alice (ProtocolVerifier.tableGame
      (selectedInstance G input).rows (selectedInstance G input).cols
      (selectedInstance G input).table) ≤ (selectedInstance G input).threshold) ∧
    (input ∉ G.L → (selectedInstance G input).threshold + (2 * t - 8) ≤
      Dalt .alice (ProtocolVerifier.tableGame
        (selectedInstance G input).rows (selectedInstance G input).cols
        (selectedInstance G input).table)) := by
  have h := YaoMinimalSource.selectedInstance_costs G input ht
  have hB := (V39SourceRenderer.sourceInstance_dimensions (selectedSource G input)).2.2
  constructor
  · intro hx
    rw [hB]
    exact h.1 hx
  · intro hx
    have hh : (selectedInstance G input).threshold + 2 * t - 8 ≤
        Dalt .alice (ProtocolVerifier.tableGame
          (selectedInstance G input).rows (selectedInstance G input).cols
          (selectedInstance G input).table) := by
      simpa only [hB] using h.2 hx
    omega

theorem table_le_matrixWord {t : ℕ} (G : SourceInput t) (input : List Bool) :
    (selectedInstance G input).rows * (selectedInstance G input).cols ≤
      (matrixWord G input).length := by
  have hv := YaoMinimalSource.selectedInstance_valid G input
  have htable : (selectedInstance G input).table.length =
      (selectedInstance G input).rows * (selectedInstance G input).cols := hv.2.2
  simp only [matrixWord, AModel.matrixWord, List.length_append]
  omega

/-- The selected half-integer threshold has polynomial binary length in
the table entry count, as required by the manuscript comparison model. -/
theorem midpoint_header_length {t : ℕ} (G : SourceInput t) (input : List Bool) :
    (natField (midpointNumerator G input)).length ≤
      (20 * t + 100) * ((selectedInstance G input).rows *
        (selectedInstance G input).cols + 1) := by
  let src := selectedSource G input
  let i := selectedInstance G input
  let b := edgeBits src.2.1
  let T := i.rows * i.cols
  have hn : 1 ≤ src.1 := selectedSource_nonempty G input
  have hd := V39SourceRenderer.sourceInstance_dimensions src
  have hp : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by decide)
  have ha : 1 ≤ 2 ^ (t - 1) := Nat.one_le_pow _ _ (by decide)
  have hp' : 2 ^ b ≤ (2 ^ b) ^ (2 ^ (t - 1)) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hp ha
  have hr : b ≤ i.rows := by
    have hb : b ≤ 2 ^ b := Nat.le_of_lt Nat.lt_two_pow_self
    have hm := Nat.mul_le_mul_right ((2 ^ b) ^ (2 ^ (t - 1))) hn
    have hrows : i.rows = src.1 * (2 ^ b) ^ (2 ^ (t - 1)) := hd.1
    rw [hrows]
    omega
  have hv := YaoMinimalSource.selectedInstance_valid G input
  have hc : 1 ≤ i.cols := hv.2.1
  have hrow : i.rows ≤ T := by
    have h := Nat.mul_le_mul_left i.rows hc
    simpa [T] using h
  have hbT : b ≤ T := hr.trans hrow
  have hB : i.threshold = 2 * b + 4 * t + 2 := hd.2.2
  have hm : midpointNumerator G input ≤ 4 * T + 10 * t + 4 := by
    change 2 * i.threshold + (2 * t - 8) ≤ _
    rw [hB]
    omega
  have hbits := UnaryBinaryEncoding.bits_length_le (midpointNumerator G input)
  have hfield : (natField (midpointNumerator G input)).length ≤
      2 * midpointNumerator G input + 1 := by
    simp only [natField, field_length]
    omega
  calc
    _ ≤ 2 * midpointNumerator G input + 1 := hfield
    _ ≤ 8 * T + 20 * t + 9 := by omega
    _ ≤ (20 * t + 100) * (T + 1) := by nlinarith [Nat.zero_le (t * T)]

theorem sourceWord_polytime_of_encoded {t : ℕ} (G : SourceInput t)
    (hk : 0 < 2 * t - 8)
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input))) :
    BitMachine.Polytime (sourceWord G) := by
  have h := header_from_encoded_polytime (selectedInstance G)
    (YaoMinimalSource.selectedInstance_valid G) hencoded (2 * t - 8) hk
  simpa only [sourceWord, midpointNumerator, matrixWord, HeaderWordRun.headeredWord,
    HeaderWordRun.matrix, AFront.Projection.matrixWord, AModel.matrixWord] using h

def sourceDecider {t : ℕ} (G : SourceInput t) {μ : YaoMeasure} {u : ℝ}
    (E : ValidYaoEstimator μ u) (hp : BitMachine.Polytime (sourceWord G)) :
    SelectedTape.Algorithm := SelectedTape.pullback (sourceWord G) hp E.algorithm.classifier

theorem sourceDecider_decides {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    {μ : YaoMeasure} {u : ℝ} (E : ValidYaoEstimator μ u) (hu : 0 ≤ u)
    (hgap : 2 * (u + 2) < ((2 * t - 8 : ℕ) : ℝ))
    (hp : BitMachine.Polytime (sourceWord G))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord G input) (midpointNumerator G input)) :
    (sourceDecider G E hp).Decides G.L (1 / 3) := by
  intro input
  have h := E.matrix_law hu (selectedInstance G input)
    (YaoMinimalSource.selectedInstance_valid G input)
    (selectedInstance G input).threshold (2 * t - 8) hgap (hcompare input)
  have hg := selectedInstance_gap G ht input
  constructor
  · intro hx
    have hh := h.1 (hg.1 hx)
    change 99 / 100 < E.algorithm.classifier.prob (sourceWord G input) (· = [true]) at hh
    rw [sourceDecider, SelectedTape.pullback_prob]
    linarith
  · intro hx
    have hh := h.2 (hg.2 hx)
    change E.algorithm.classifier.prob (sourceWord G input) (· = [true]) < 1 / 100 at hh
    rw [sourceDecider, SelectedTape.pullback_prob]
    linarith

#print axioms selectedInstance_gap
#print axioms table_le_matrixWord
#print axioms midpoint_header_length
#print axioms sourceWord_polytime_of_encoded
#print axioms sourceDecider_decides

end CurrentAdditive.V39MinimalActualEndpoint
