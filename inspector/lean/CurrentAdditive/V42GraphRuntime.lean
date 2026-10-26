import CurrentAdditive.V42RuntimePrefix
import CurrentAdditive.V42SourceWidths
import CurrentAdditive.V40PipelineRuntime
import CurrentAdditive.V40GraphConstructorInputBounds

/-! The actual v42 deterministic generated constructor and its machine clock.
The machine is fixed before the graph and round count. The final endpoint
prints the square padding of the same seven-call graphRun; there are no
prepared states, desired outputs, resource certificates or run premises. -/
namespace CurrentAdditive.V42GraphRuntime
open Paper2 EthInapproximability.CurrentPaper V42Schedule
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536

def amplification (k₀ : ℕ) := V40PipelineRuntime.amplification
  (V42RuntimePrefix.machine k₀) StoredMatrixEnvelopeStep.machine 2 1
  (V42RuntimePrefix.baseCoefficient k₀) (V42RuntimePrefix.degree k₀)
  StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree
def exponent (k₀ : ℕ) (T : BitMachine.Machine) (ct dt : ℕ) :=
  V40PipelineRuntime.exponentCoefficient (V42RuntimePrefix.machine k₀) StoredMatrixEnvelopeStep.machine T 2 1
    (V42RuntimePrefix.baseCoefficient k₀) (V42RuntimePrefix.degree k₀)
    StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree ct dt
def pipeline (k₀ : ℕ) (T : BitMachine.Machine) :=
  V40PipelineRuntime.pipeline (V42RuntimePrefix.machine k₀) StoredMatrixEnvelopeStep.machine T
def machine (k₀ : ℕ) := pipeline k₀ V40StoredEnvelope.machine
def squareExponent (k₀ : ℕ) := exponent k₀ V40StoredEnvelope.machine V40StoredEnvelope.coefficient V40StoredEnvelope.degree

theorem amplification_ge (k₀ : ℕ) : 2^64 ≤ amplification k₀ :=
  V40PipelineRuntime.amplification_ge _ _ _ _ _ _ _ _
theorem amplification_power (k₀ : ℕ) : ∃ a, amplification k₀=2^a :=
  ⟨V40PipelineRuntime.amplificationLog _ _ 2 1
    (V42RuntimePrefix.baseCoefficient k₀) (V42RuntimePrefix.degree k₀)
    StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree,rfl⟩

theorem outputs_with_tail (k₀ : ℕ) (T : BitMachine.Machine) (ct dt : ℕ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ)
    (hk : 2 ≤ V42RuntimePrefix.selected k₀ g) (hn : 0<g.vertices)
    (hq : q₂ (V42RuntimePrefix.selected k₀ g) (4*V42RuntimePrefix.selected k₀ g)=
      LiteralEdgeEncoder.Width (s (V42RuntimePrefix.selected k₀ g)) g.edges.length
        (V42RuntimePacket.repetition (V42RuntimePrefix.selected k₀ g) g.edges.length))
    (Y : List Bool)
    (hT : T.OutputsWithin (V42RuntimeWords.word g hg (V42RuntimePrefix.selected k₀ g) K hk hn hq K) Y
      (ct*((V42RuntimeWords.word g hg (V42RuntimePrefix.selected k₀ g) K hk hn hq K).length+1)^dt)) :
    (pipeline k₀ T).OutputsWithin (V42RuntimePrefix.input (EncodedGraph.encode g) K) Y
      ((V42RuntimePrefix.base k₀ g)^(exponent k₀ T ct dt*(amplification k₀)^K)) ∧
    Y.length ≤ (V42RuntimePrefix.base k₀ g)^(exponent k₀ T ct dt*(amplification k₀)^K) := by
  have hb : 2 ≤ V42RuntimePrefix.base k₀ g := by unfold V42RuntimePrefix.base;omega
  have hx : (V42RuntimePrefix.input (EncodedGraph.encode g) K).length≤
      2*(V42RuntimePrefix.base k₀ g+K+1)^1 := by
    rw [pow_one]
    have h := V42RuntimePrefix.input_length (EncodedGraph.encode g) K
    unfold V42RuntimePrefix.base
    omega
  exact V40PipelineRuntime.outputs (V42RuntimePrefix.machine k₀) StoredMatrixEnvelopeStep.machine T
    2 1 (V42RuntimePrefix.baseCoefficient k₀) (V42RuntimePrefix.degree k₀)
    StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree ct dt
    (V42RuntimePrefix.base k₀ g) K (V42RuntimePrefix.input (EncodedGraph.encode g) K)
    (V42RuntimeWords.word g hg (V42RuntimePrefix.selected k₀ g) K hk hn hq) Y hb hx
    (V42RuntimePrefix.outputs_base k₀ g hg K hk hn hq)
    (V42RuntimeWords.round_outputs g hg (V42RuntimePrefix.selected k₀ g) K hk hn hq) hT

theorem square_outputs (k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ)
    (hk : 2 ≤ V42RuntimePrefix.selected k₀ g) (hn : 0<g.vertices)
    (hq : q₂ (V42RuntimePrefix.selected k₀ g) (4*V42RuntimePrefix.selected k₀ g)=
      LiteralEdgeEncoder.Width (s (V42RuntimePrefix.selected k₀ g)) g.edges.length
        (V42RuntimePacket.repetition (V42RuntimePrefix.selected k₀ g) g.edges.length)) :
    let Y := (V42RuntimeWords.run g hg (V42RuntimePrefix.selected k₀ g) hk hn hq K).squareWord
    (machine k₀).OutputsWithin (V42RuntimePrefix.input (EncodedGraph.encode g) K) Y
      ((V42RuntimePrefix.base k₀ g)^(squareExponent k₀*(amplification k₀)^K)) ∧
    Y.length ≤ (V42RuntimePrefix.base k₀ g)^(squareExponent k₀*(amplification k₀)^K) := by
  exact outputs_with_tail k₀ V40StoredEnvelope.machine V40StoredEnvelope.coefficient V40StoredEnvelope.degree
    g hg K hk hn hq _ (V40StoredEnvelope.outputs (4*V42RuntimePrefix.selected k₀ g) K
      (V42RuntimeWords.context g hg (V42RuntimePrefix.selected k₀ g) hk hn hq)
      (V42RuntimeWords.run g hg (V42RuntimePrefix.selected k₀ g) hk hn hq K))

theorem selected_ge_two (k₀ : ℕ) (hk₀ : 2≤k₀) (g : EncodedGraph.Graph) :
    2 ≤ V42RuntimePrefix.selected k₀ g :=
  hk₀.trans (V42PublicCutoff.generatedExponent_spec g.vertices k₀).1

theorem selected_width (Δ k₀ : ℕ) (g : EncodedGraph.Graph)
    (hdegree : 2*g.edges.length≤Δ*g.vertices) (hcut : 2*Δ≤k₀) :
    q₂ (V42RuntimePrefix.selected k₀ g) (4*V42RuntimePrefix.selected k₀ g)=
      LiteralEdgeEncoder.Width (s (V42RuntimePrefix.selected k₀ g)) g.edges.length
        (V42RuntimePacket.repetition (V42RuntimePrefix.selected k₀ g) g.edges.length) := by
  let k:=V42RuntimePrefix.selected k₀ g
  have hn : g.vertices≤2^(4*k) := by
    simpa only [V42PublicSchedule.generatedN_exact] using
      (V42PublicCutoff.generatedExponent_spec g.vertices k₀).2
  have hk : 2*Δ≤k := hcut.trans (V42PublicCutoff.generatedExponent_spec g.vertices k₀).1
  have hw:=source_width Δ g.vertices g.edges.length k (4*k) hn hdegree hk
  change q₂ k (4*k)=EdgeSource.sourceQ0 (Fin (4*s k)) (Fin g.edges.length)*
    V42RuntimePacket.repetition k g.edges.length
  rw [EdgeSource.sourceQ0_literal]
  simpa only [Fintype.card_fin,V42RuntimePacket.repetition,sourceQ0,V42Schedule.repetition,
    V38Schedule.pow2Ceil,SourcePadding.powTwoCeil] using repetition_exact k (4*k) g.edges.length hw

def publicRun (Δ k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hk₀ : 2≤k₀) (hn : 0<g.vertices) (hdegree : 2*g.edges.length≤Δ*g.vertices) (hcut : 2*Δ≤k₀) (K : ℕ) :=
  V42RuntimeWords.run g hg (V42RuntimePrefix.selected k₀ g) (selected_ge_two k₀ hk₀ g) hn
    (selected_width Δ k₀ g hdegree hcut) K

theorem public_outputs (Δ k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hk₀ : 2≤k₀) (hn : 0<g.vertices) (hdegree : 2*g.edges.length≤Δ*g.vertices) (hcut : 2*Δ≤k₀) (K : ℕ) :
    (machine k₀).OutputsWithin (V42RuntimePrefix.input (EncodedGraph.encode g) K)
      (publicRun Δ k₀ g hg hk₀ hn hdegree hcut K).squareWord
      ((V42RuntimePrefix.base k₀ g)^(squareExponent k₀*(amplification k₀)^K)) ∧
    (publicRun Δ k₀ g hg hk₀ hn hdegree hcut K).squareWord.length≤
      (V42RuntimePrefix.base k₀ g)^(squareExponent k₀*(amplification k₀)^K) :=
  square_outputs k₀ g hg K (selected_ge_two k₀ hk₀ g) hn (selected_width Δ k₀ g hdegree hcut)

def sourceCoefficient (k₀ : ℕ) := 16*(2^(4*k₀)+1)+3

theorem base_le_source (k₀ : ℕ) (g : EncodedGraph.Graph) :
    V42RuntimePrefix.base k₀ g ≤ sourceCoefficient k₀*((EncodedGraph.encode g).length+1) := by
  have hg:=EncodedGraph.encode_length_lower g
  have hp:=(V42PublicCutoff.generated_padding g.vertices k₀).2
  rw [V42PublicSchedule.generatedN_exact,V42PublicSchedule.generatedN_exact] at hp
  have hm : max g.vertices (2^(4*k₀))≤g.vertices+2^(4*k₀) :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hN : V42RuntimePrefix.N k₀ g≤16*(g.vertices+2^(4*k₀)) := by
    unfold V42RuntimePrefix.N V42RuntimePrefix.selected
    exact hp.le.trans (Nat.mul_le_mul_left 16 hm)
  unfold V42RuntimePrefix.base sourceCoefficient
  nlinarith only [hN,hg,Nat.zero_le ((2^(4*k₀))*(EncodedGraph.encode g).length)]

def sourceExponent (k₀ : ℕ) := (sourceCoefficient k₀+1)*squareExponent k₀

theorem power_source_bound (k₀ : ℕ) (g : EncodedGraph.Graph) (e : ℕ) :
    (V42RuntimePrefix.base k₀ g)^e≤
      ((EncodedGraph.encode g).length+1)^((sourceCoefficient k₀+1)*e) := by
  have hg:=EncodedGraph.encode_length_lower g
  have hB : 2≤(EncodedGraph.encode g).length+1 := by omega
  have hc : sourceCoefficient k₀≤((EncodedGraph.encode g).length+1)^sourceCoefficient k₀ :=
    (V39UniformResource.self_le_two_pow _).trans (Nat.pow_le_pow_left hB _)
  have hbase : V42RuntimePrefix.base k₀ g≤((EncodedGraph.encode g).length+1)^(sourceCoefficient k₀+1) := by
    calc
      _ ≤ sourceCoefficient k₀*((EncodedGraph.encode g).length+1) := base_le_source k₀ g
      _ ≤ ((EncodedGraph.encode g).length+1)^sourceCoefficient k₀*((EncodedGraph.encode g).length+1) :=
        Nat.mul_le_mul_right _ hc
      _ = _ := (pow_succ _ _).symm
  exact (Nat.pow_le_pow_left hbase e).trans_eq (pow_mul _ _ _).symm

/-- A single fixed amplification works before all source graphs and round
counts. Both the actual output length and the entire machine time are
polynomial in the original graph word for each fixed number of rounds. -/
theorem public_source_bound (Δ k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hk₀ : 2≤k₀) (hn : 0<g.vertices) (hdegree : 2*g.edges.length≤Δ*g.vertices) (hcut : 2*Δ≤k₀) (K : ℕ) :
    (machine k₀).OutputsWithin (V42RuntimePrefix.input (EncodedGraph.encode g) K)
      (publicRun Δ k₀ g hg hk₀ hn hdegree hcut K).squareWord
      (((EncodedGraph.encode g).length+1)^(sourceExponent k₀*(amplification k₀)^K)) ∧
    (publicRun Δ k₀ g hg hk₀ hn hdegree hcut K).squareWord.length≤
      ((EncodedGraph.encode g).length+1)^(sourceExponent k₀*(amplification k₀)^K) := by
  have h:=public_outputs Δ k₀ g hg hk₀ hn hdegree hcut K
  have hb:=power_source_bound k₀ g (squareExponent k₀*(amplification k₀)^K)
  rw [show (sourceCoefficient k₀+1)*(squareExponent k₀*(amplification k₀)^K)=
    sourceExponent k₀*(amplification k₀)^K by unfold sourceExponent;ring] at hb
  exact ⟨BitMachine.outputsWithin_mono _ h.1 hb,h.2.trans hb⟩

#print axioms amplification_ge
#print axioms selected_width
#print axioms public_outputs
#print axioms public_source_bound
end
end CurrentAdditive.V42GraphRuntime
