import CurrentAdditive.V39HalfMidpoint
import CurrentAdditive.V39HalfDeterministic
import CurrentAdditive.V39SourceRenderer
import CurrentAdditive.SmallBiasHeaderPhysical

/-!
Consumer of the source team's exact executable renderer. The source and
the whole physical encoded-table printer remain distinct. The existing
checked fixed-gap header machine discharges the midpoint-header adapter;
only the physical printer of encodeInstance(selectedInstance G input)
remains a construction premise of the class endpoint below.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39YaoEndpointJoin

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V38Source CurrentAdditive.V38Encoded
open CurrentAdditive.V39HalfMidpoint
open CurrentAdditive.SmallBias
open Paper2 Paper2.Yao Paper2.YaoBppDraft

abbrev selectedInstance {t : ℕ} (G : GLSourceInput t) (input : List Bool) : Instance :=
  V39SourceRenderer.sourceInstance (selectedSource G input)

theorem selectedInstance_gap {t : ℕ} (G : GLSourceInput t)
    (ht : 4 ≤ t) (input : List Bool) :
    (input ∈ G.L → Dalt .alice (ProtocolVerifier.tableGame
      (selectedInstance G input).rows (selectedInstance G input).cols
      (selectedInstance G input).table) ≤ (selectedInstance G input).threshold) ∧
    (input ∉ G.L → (selectedInstance G input).threshold + (2 * t - 8) ≤
      Dalt .alice (ProtocolVerifier.tableGame
        (selectedInstance G input).rows (selectedInstance G input).cols
        (selectedInstance G input).table)) := by
  have h := V39SourceRenderer.selectedInstance_costs G input ht
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
    have h8 : 8 ≤ 2 * t := by omega
    omega

def sourceWord {t : ℕ} (G : GLSourceInput t) (input : List Bool) : List Bool :=
  let i := selectedInstance G input
  natField (2 * i.threshold + (2 * t - 8)) ++ AModel.matrixWord i.rows i.cols i.table

/-- The source compiler is already physical. Once the all-input renderer
is supplied, ordinary machine composition yields exactly the needed
encoded table, without an extra semantic equality assumption. -/
theorem source_encoded_polytime_of_renderer {t : ℕ} (G : GLSourceInput t)
    (hrender : BitMachine.Polytime (V39SourceRenderer.render t)) :
    BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input)) := by
  have h := BitMachineComposition.polytime_comp
    (V39SourceCompiler.sourceCode_polytime G) hrender
  simpa only [Function.comp_def, V39SourceRenderer.render_sourceCode] using h

/-- Physical split, swap, fixed-offset arithmetic, pair map and concatenation
from the actual encoded table. Its clock charges every transfer. This
discharges the header join; it does not assert the table printer premise. -/
theorem sourceWord_polytime_of_encoded {t : ℕ} (G : GLSourceInput t)
    (hk : 0 < 2 * t - 8)
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input))) :
    BitMachine.Polytime (sourceWord G) := by
  have h := header_from_encoded_polytime (selectedInstance G)
    (V39SourceRenderer.selectedInstance_valid G) hencoded (2 * t - 8) hk
  simpa only [sourceWord, HeaderWordRun.headeredWord, HeaderWordRun.matrix,
    AFront.Projection.matrixWord, AModel.matrixWord] using h

theorem sourceWord_law {t : ℕ} (G : GLSourceInput t) (ht : 4 ≤ t)
    {μ : YaoMeasure} {u : ℝ} (E : HalfEstimator μ u) (hu : 0 ≤ u)
    (hgap : 2 * (u + 2) < ((2 * t - 8 : ℕ) : ℝ)) (input : List Bool) :
    (input ∈ G.L → 99 / 100 ≤ E.classifier.prob (sourceWord G input) (· = [true])) ∧
    (input ∉ G.L → E.classifier.prob (sourceWord G input) (· = [true]) ≤ 1 / 100) := by
  have h := fixed_midpoint_law E hu (selectedInstance G input)
    (V39SourceRenderer.selectedInstance_valid G input)
    (selectedInstance G input).threshold (2 * t - 8) hgap
  have hg := selectedInstance_gap G ht input
  exact ⟨fun hx => h.1 (hg.1 hx), fun hx => h.2 (hg.2 hx)⟩

def sourceDecider {t : ℕ} (G : GLSourceInput t)
    {μ : YaoMeasure} {u : ℝ} (E : HalfEstimator μ u)
    (hprint : BitMachine.Polytime (sourceWord G)) : SelectedTape.Algorithm :=
  SelectedTape.pullback (sourceWord G) hprint E.classifier

theorem sourceDecider_decides {t : ℕ} (G : GLSourceInput t) (ht : 4 ≤ t)
    {μ : YaoMeasure} {u : ℝ} (E : HalfEstimator μ u) (hu : 0 ≤ u)
    (hgap : 2 * (u + 2) < ((2 * t - 8 : ℕ) : ℝ))
    (hprint : BitMachine.Polytime (sourceWord G)) :
    (sourceDecider G E hprint).Decides G.L (1 / 3) := by
  intro input
  have h := sourceWord_law G ht E hu hgap input
  constructor
  · intro hx
    have hh := h.1 hx
    rw [sourceDecider, SelectedTape.pullback_prob]
    linarith
  · intro hx
    have hh := h.2 hx
    rw [sourceDecider, SelectedTape.pullback_prob]
    linarith

/-- Conditional only on the source-theorem interface, its NP hardness,
the allowed estimator, and the physical printer for the exact table word.
The proof has no assumed table-gap or midpoint-header correctness field. -/
theorem conditional_np_subset_bpp {t : ℕ} (G : GLSourceInput t) (ht : 4 ≤ t)
    (hard : NPHard G.L) {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (hu : 0 ≤ u)
    (hgap : 2 * (u + 2) < ((2 * t - 8 : ℕ) : ℝ))
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input))) :
    ∀ L, InNP L → SelectedTape.InBPP L := by
  have hk : 0 < 2 * t - 8 := by
    have h : (0 : ℝ) < ((2 * t - 8 : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  let hp := sourceWord_polytime_of_encoded G hk hencoded
  exact SelectedTape.np_subset_inBPP hard
    ⟨sourceDecider G E hp, sourceDecider_decides G ht E hu hgap hp⟩

theorem conditional_p_equals_np {t : ℕ} (G : GLSourceInput t) (ht : 4 ≤ t)
    (hard : NPHard G.L) {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (hu : 0 ≤ u) (hz : E.estimator.cR = 0)
    (hgap : 2 * (u + 2) < ((2 * t - 8 : ℕ) : ℝ))
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input))) :
    PEqualsNP := by
  have hk : 0 < 2 * t - 8 := by
    have h : (0 : ℝ) < ((2 * t - 8 : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  let hp := sourceWord_polytime_of_encoded G hk hencoded
  have hmem : ComplexityReductionClosure.InP G.L :=
    V39HalfDeterministic.inP_of_decides E hz (sourceWord G) hp G.L
      (sourceDecider_decides G ht E hu hgap hp)
  exact p_equals_np_of_np_subset_p
    (ComplexityReductionClosure.npHard_inP_implies_np_subset_p hard hmem)

/-- A fixed integer k>2(u+2), followed by the manuscript's exact
t=ceil(k/2)+4 choice. The source and printer degrees may depend on u. -/
def estimatorRequestedGap (u : ℝ) : ℕ := ⌈2 * u⌉₊ + 5
def estimatorParameter (u : ℝ) : ℕ := v37GapParameter (estimatorRequestedGap u)

theorem estimatorParameter_valid (u : ℝ) : 4 ≤ estimatorParameter u :=
  v37GapParameter_ge_four _

theorem estimatorParameter_gap (u : ℝ) :
    2 * (u + 2) < ((2 * estimatorParameter u - 8 : ℕ) : ℝ) := by
  have hc := Nat.le_ceil (2 * u)
  have hg := v37GapParameter_gap (estimatorRequestedGap u)
  have hgR : (estimatorRequestedGap u : ℝ) ≤
      ((2 * estimatorParameter u - 8 : ℕ) : ℝ) := by exact_mod_cast hg
  dsimp [estimatorRequestedGap] at hgR
  push_cast at hgR
  linarith

theorem conditional_np_subset_bpp_fixed_error (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceInput (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (E : HalfEstimator μ u)
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input))) :
    ∀ L, InNP L → SelectedTape.InBPP L :=
  conditional_np_subset_bpp G (estimatorParameter_valid u) hard E hu
    (estimatorParameter_gap u) hencoded

theorem conditional_p_equals_np_fixed_error (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceInput (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (E : HalfEstimator μ u) (hz : E.estimator.cR = 0)
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input))) :
    PEqualsNP :=
  conditional_p_equals_np G (estimatorParameter_valid u) hard E hu hz
    (estimatorParameter_gap u) hencoded

/-- The deterministic statement on an ordinary all-input polynomial
bit-machine estimator, with arbitrary permitted numerical outputs. -/
theorem deterministic_p_equals_np_fixed_error (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceInput (estimatorParameter u)) (hard : NPHard G.L)
    (est : List Bool → List Bool) (hpoly : BitMachine.Polytime est)
    (value : List Bool → ℝ) (R : HalfComparator value) (μ : YaoMeasure)
    (hacc : ∀ w c, AModel.targetYao μ w = some c → |value (est w) - (c : ℝ)| ≤ u)
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input))) :
    PEqualsNP :=
  conditional_p_equals_np_fixed_error u hu G hard
    (V39HalfDeterministic.ofDeterministic est hpoly value R μ u hacc)
    (V39HalfDeterministic.ofDeterministic_zero est hpoly value R μ u hacc) hencoded

#print axioms selectedInstance_gap
#print axioms source_encoded_polytime_of_renderer
#print axioms sourceWord_polytime_of_encoded
#print axioms sourceWord_law
#print axioms sourceDecider_decides
#print axioms conditional_np_subset_bpp
#print axioms conditional_p_equals_np
#print axioms estimatorParameter_gap
#print axioms conditional_np_subset_bpp_fixed_error
#print axioms conditional_p_equals_np_fixed_error
#print axioms deterministic_p_equals_np_fixed_error

end CurrentAdditive.V39YaoEndpointJoin
