import CurrentV43.RandomizedArithmetic
import CurrentAdditive.V42RandomizedRoutedLaw
import CurrentAdditive.V42RandomizedSourceTests

/-! Concrete source and independent estimator law at the new rational-power
schedule. This reuses the actual checked graph, rounded sampler, printed
matrix, extracted permitted estimator and physical rational comparison. -/
namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42PublicSchedule V39ActualOutputMajority V39PermittedNumericalExtraction
open V42RandomizedETHEndpoint
open CurrentAdditive.V43RandomizedRate
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def sourceAccepts (K : ℕ) (Φ : ValidFormula) (ht : SourceTests D B Φ)
    (E : ActualEstimator)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices K)
      (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices K))
    (t : Fin (V42JointEstimatorLaw.classifierLength E
      (Nat.clog 2 (t10Graph D B Φ).vertices) K) → Bool) : Prop :=
  letI : NeZero (t10Graph D B Φ).vertices := ⟨(t10_vertices_pos D B Φ).ne'⟩
  E.classifier.output (V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
    K (V38Schedule.fullConstant (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
    (V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
    (V38Schedule.sourceZeta (sourceGap D B)) ht bits) (List.ofFn t) = [true]

def sourceLaw (K : ℕ) (E : ActualEstimator) (Φ : ValidFormula) :=
  V42JointEstimatorLaw.independentLaw
    (RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices K)
      (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices K))
    E (Nat.clog 2 (t10Graph D B Φ).vertices) K

/-- The actual table and classifier have total error at most 3/100 under
the rational-power schedule. No source-gap or output-clock conclusion is
assumed. They follow from the selected named source reductions and the
estimator's ordinary square-table accuracy. -/
theorem source_law_all_large (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1) (A : PermittedEstimator)
    (cs T₀ : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hcβ : 8*c < (a:ℝ)/(b:ℝ))
    (hA : GrowingSquareAccuracy A c T₀) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      ∀ ht : SourceTests D B Φ,
      (EncodedCNF.Satisfiable Φ.val →
        (99:ℝ)/100 ≤ (sourceLaw D B (iterations a b Φ.val.variables) (extractedEstimator A) Φ).prob
          (fun z => sourceAccepts D B (iterations a b Φ.val.variables) Φ ht (extractedEstimator A) z.1 z.2)) ∧
      (¬EncodedCNF.Satisfiable Φ.val →
        (sourceLaw D B (iterations a b Φ.val.variables) (extractedEstimator A) Φ).prob
          (fun z => sourceAccepts D B (iterations a b Φ.val.variables) Φ ht (extractedEstimator A) z.1 z.2) ≤ (3:ℝ)/100) := by
  obtain ⟨Ng,hg⟩ := gap_exceeds_twice_error a b B.degreeBound (D.sizeExponent+2)
    ha hb hβ1 B.degreeBound_pos c hc0 hcβ
  obtain ⟨Nt,ht⟩ := entries_eventually_ge a b (max 4 T₀) ha hb
  refine ⟨max 1 (max Ng (max Nt (max (V42SourceGeometry.originalCutoff D B cs)
    (B.degreeBound*V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound)))),
    le_max_left _ _,?_⟩
  intro Φ hsp hN htst
  have hNg : Ng ≤ Φ.val.variables := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNt : Nt ≤ Φ.val.variables := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNc : V42SourceGeometry.originalCutoff D B cs ≤ Φ.val.variables :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hNf : B.degreeBound*V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound ≤ Φ.val.variables :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  obtain ⟨facts,_,hsize⟩ := V42SourceGeometry.source_all_large D B cs Φ hsp hNc
  have hTall := ht Φ.val.variables hNt (Nat.clog 2 (t10Graph D B Φ).vertices)
  have hT : T₀ ≤ sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices) (iterations a b Φ.val.variables) :=
    (le_max_right _ _).trans hTall
  have h4 : 4 ≤ sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices) (iterations a b Φ.val.variables) :=
    (le_max_left _ _).trans hTall
  have hu := growingError_nonnegative c hc0 _ h4
  have hgap := hg Φ.val.variables hNg (t10Graph D B Φ).vertices facts.vertices_pos
    facts.original_degree_bound hsize
  have hgap' : 2*growingError c (sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices)
      (iterations a b Φ.val.variables)) < (iterations a b Φ.val.variables:ℝ) := by
    simpa only [growingError,mul_div_assoc,mul_assoc] using hgap
  letI : NeZero (t10Graph D B Φ).vertices := ⟨facts.vertices_pos.ne'⟩
  let E := extractedEstimator A
  let L := Nat.clog 2 (t10Graph D B Φ).vertices
  let K := iterations a b Φ.val.variables
  let cc := V38Schedule.fullConstant (sourceGap D B) B.degreeBound
    (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
  let δv := V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
    (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
  let ζ := V38Schedule.sourceZeta (sourceGap D B)
  let f := V42RawRequestPacket.matrix (t10Graph D B Φ) (t10Graph_valid D B Φ) K cc δv ζ htst
  let μ := RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices K)
    (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices K)
  have haccurate := extracted_accuracy A c T₀ L K hA hT
  have hlarge : V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound ≤
      (t10Graph D B Φ).vertices := facts.vertices_floor _ hNf
  have hs := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  constructor
  · intro hy
    obtain ⟨colour,proper⟩ := hs.2.2.2.2.2.1 hy
    have hproper : ∀ e, colour (LiteralEdgeEncoder.edge (t10Graph D B Φ)
        (t10Graph_valid D B Φ) e false) ≠ colour (LiteralEdgeEncoder.edge (t10Graph D B Φ)
        (t10Graph_valid D B Φ) e true) := by
      rw [V39SourceGeometry.physical_edge_eq]
      exact proper
    exact V42JointEstimatorLaw.yes_product μ E L K f _ hu hgap'
      (fun bits => extractedEstimator_comparison A L K (f bits))
      (fun bits => haccurate (f bits))
      (fun bits => V42PrintedGraphGap.every_tape_yes (t10Graph D B Φ) (t10Graph_valid D B Φ)
        K cc δv ζ htst colour hproper bits)
  · intro hn
    have hgood := V42PrintedGraphGap.no_probability (t10Graph D B Φ) (t10Graph_valid D B Φ)
      K cc δv ζ htst B.degreeBound B.degreeBound_pos facts.degree (sourceGap D B)
      (source_gap_pos D B) facts.vertex_edge_bound facts.edge_degree_bound hlarge (by
        rw [V39SourceGeometry.physical_edge_eq]
        exact hs.2.2.2.2.2.2 hn)
    exact V42JointEstimatorLaw.no_product μ E L K f _ hu hgap'
      (fun bits => extractedEstimator_comparison A L K (f bits))
      (fun bits => haccurate (f bits)) hgood

/-- A single fixed physical router handles malformed inputs and finite
small formulas. On every promised sparse formula it preserves satisfiability,
so the same source law is correct at every input size. -/
theorem routed_source_correctness (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1) (A : PermittedEstimator)
    (cs T₀ : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hcβ : 8*c < (a:ℝ)/(b:ℝ))
    (hA : GrowingSquareAccuracy A c T₀) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ V42SourceGeometry.originalCutoff D B (cs+2) ≤ N₀ ∧
      ∀ cutoff, N₀ ≤ cutoff → ∀ hcutoff : 1 ≤ cutoff, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables →
      let ρ := routedSource cs cutoff hcutoff (EncodedCNF.encode Φ.val)
      ∀ ht : SourceTests D B ρ,
      (EncodedCNF.encode Φ.val ∈ EncodedCNF.Language →
        (99:ℝ)/100 ≤ (sourceLaw D B (iterations a b ρ.val.variables) (extractedEstimator A) ρ).prob
          (fun z => sourceAccepts D B (iterations a b ρ.val.variables) ρ ht (extractedEstimator A) z.1 z.2)) ∧
      (EncodedCNF.encode Φ.val ∉ EncodedCNF.Language →
        (sourceLaw D B (iterations a b ρ.val.variables) (extractedEstimator A) ρ).prob
          (fun z => sourceAccepts D B (iterations a b ρ.val.variables) ρ ht (extractedEstimator A) z.1 z.2) ≤ (3:ℝ)/100) := by
  obtain ⟨Ns,hNs,hS⟩ := source_law_all_large D B a b ha hb hβ1 A (cs+2) T₀ c hc0 hcβ hA
  refine ⟨max Ns (V42SourceGeometry.originalCutoff D B (cs+2)),
    hNs.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro cutoff hcut hcutoff Φ hsp
  dsimp only
  let ρ := routedSource cs cutoff hcutoff (EncodedCNF.encode Φ.val)
  intro ht
  have hvars : Ns ≤ ρ.val.variables :=
    ((le_max_left _ _).trans hcut).trans (AEth4.routed4_variables (cs+2) cutoff _)
  have h := hS ρ (routedSource_sparse cs cutoff hcutoff _) hvars ht
  have hsp' : Φ.val.clauses.length ≤ (cs+2)*Φ.val.variables :=
    hsp.trans (Nat.mul_le_mul_right _ (by omega))
  have hlang : EncodedCNF.Satisfiable ρ.val ↔ EncodedCNF.encode Φ.val ∈ EncodedCNF.Language :=
    AEth4.routed4_sat_iff (cs+2) hcutoff Φ.val Φ.property hsp'
  exact ⟨fun hy => h.1 (hlang.2 hy),fun hn => h.2 (fun hy => hn (hlang.1 hy))⟩

#print axioms source_law_all_large
#print axioms routed_source_correctness
end
end CurrentV43.RandomizedRate
