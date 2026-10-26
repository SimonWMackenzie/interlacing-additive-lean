import CurrentAdditive.V40ActivityTableBounds
import CurrentAdditive.V40IndexedLawPolynomial

/-! The complete source-context constructor consumes the actual post-search
twelve-field packet. It computes the canonical item law and every activity
cell, retaining all original fields and appending exactly those two tables.
Its program and polynomial are fixed before the graph and public parameters. -/
namespace CurrentAdditive.V40SourceContextWriter
noncomputable section
open Paper2 EthInapproximability.CurrentPaper BitMachineBankCodec
open D22PacketPrimitives V40SourceLocal V40SourceClockBounds V39GeneratedConstruction V38Schedule
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
abbrev P:=V40SourceLocal.Producer

def lawCoefficient:=Classical.choose V40IndexedLawPolynomial.outputs_polynomial
def lawDegree:=Classical.choose (Classical.choose_spec V40IndexedLawPolynomial.outputs_polynomial)
theorem law_bound (s n : Nat) (hs : 4 ≤ s) (hn : 0<n) :
    V40IndexedLawLoop.machine.OutputsWithin (V40IndexedLawLoop.input s n)
      (StoredWeightedState.lawBytes (LiteralEdgeEncoder.indexedItemLaw s n hs hn))
      (lawCoefficient*((V40IndexedLawLoop.input s n).length+1)^lawDegree) :=
  Classical.choose_spec (Classical.choose_spec V40IndexedLawPolynomial.outputs_polynomial) s n hs hn
def lawQuery : P:=finiteRun V40IndexedLawLoop.machine lawCoefficient lawDegree
def activityQuery : P:=finiteRun V40ActivityTable.machine V40ActivityTable.coefficient V40ActivityTable.degree
def lawInput : P:=serialise ![project (1:Fin 12),project (7:Fin 12),project (11:Fin 12)]
def activityInput : P:=serialise ![project (0:Fin 12),project (2:Fin 12),project (7:Fin 12),
  project (10:Fin 12),project (1:Fin 12),project (6:Fin 12),project (11:Fin 12)]
def law : P:=V40SourceLocal.compose lawInput lawQuery
def activity : P:=V40SourceLocal.compose activityInput activityQuery
def fields : Fin 14 → P:=![project (0:Fin 12),project (1:Fin 12),project (2:Fin 12),project (3:Fin 12),
  project (4:Fin 12),project (5:Fin 12),project (6:Fin 12),project (7:Fin 12),project (8:Fin 12),
  project (9:Fin 12),project (10:Fin 12),project (11:Fin 12),law,activity]
def producer : P:=serialise fields
def machine:=producer.machine

def input (g : EncodedGraph.Graph) (L K : Nat):=
  D22PostSearchPacket.output (EncodedGraph.encode g) g.vertices g.edges.length L K
def lawBytes (g : EncodedGraph.Graph) (L : Nat) (hn : 0<g.vertices) (hs : 4 ≤ generatedS L):=
  StoredWeightedState.lawBytes (LiteralEdgeEncoder.indexedItemLaw (generatedS L) g.vertices hs hn)
def activityBytes (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) [NeZero (generatedS L)]
    (hs : 4 ≤ generatedS L)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length (publicRepetition L g.edges.length)):=
  StoredStepContext.activityWords (graphActivity (by omega : 3 ≤ generatedS L) hq (LiteralEdgeEncoder.edge g hg))
def output (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat) [NeZero (generatedS L)]
    (hn : 0<g.vertices) (hs : 4 ≤ generatedS L)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length (publicRepetition L g.edges.length)):=
  D22PostSearchPacket.withSource (EncodedGraph.encode g) g.vertices g.edges.length L K
    (lawBytes g L hn hs) (activityBytes g hg L hs hq)

theorem lawInput_result (g : EncodedGraph.Graph) (L K : Nat) :
    lawInput.result (input g L K)=V40IndexedLawLoop.input (generatedS L) g.vertices := by
  rw [lawInput,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k <;> simp [project,input,D22PostSearchPacket.output,D22PostSearchPacket.words,
    D22PostSearchPacket.ni,V40IndexedLawLoop.input,V40IndexedLawLoop.count,BankFieldProjection.result_encode]
theorem activityInput_result (g : EncodedGraph.Graph) (L K : Nat) :
    activityInput.result (input g L K)=V40ActivityTable.input g (generatedS L)
      (publicRepetition L g.edges.length) (generatedQ₂ L) := by
  rw [activityInput,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k <;> simp [project,input,D22PostSearchPacket.output,D22PostSearchPacket.words,
    D22PostSearchPacket.ni,V40ActivityTable.input,V40ActivityTable.count,V40ActivityRow.count,
    BankFieldProjection.result_encode]
theorem law_result (g : EncodedGraph.Graph) (L K : Nat) (hn : 0<g.vertices) (hs : 4 ≤ generatedS L) :
    law.result (input g L K)=lawBytes g L hn hs := by
  change lawQuery.result (lawInput.result (input g L K))=_
  rw [lawInput_result]
  exact (BitMachine.outputsWithin_at_bound V40IndexedLawLoop.machine (law_bound _ _ hs hn)).2
theorem activity_result (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat) [NeZero (generatedS L)]
    (hn : 0<g.vertices) (hs : 4 ≤ generatedS L)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length (publicRepetition L g.edges.length)) :
    activity.result (input g L K)=activityBytes g hg L hs hq := by
  change activityQuery.result (activityInput.result (input g L K))=_
  rw [activityInput_result]
  exact (BitMachine.outputsWithin_at_bound V40ActivityTable.machine
    (V40ActivityTable.outputs_polynomial g hg hn (by omega) hq)).2

theorem result (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat) [NeZero (generatedS L)]
    (hn : 0<g.vertices) (hs : 4 ≤ generatedS L)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length (publicRepetition L g.edges.length)) :
    producer.result (input g L K)=output g hg L K hn hs hq := by
  rw [producer,serialise_result]
  apply congrArg encode
  funext k
  fin_cases k
  all_goals first
    | solve | simp [fields,project,input,output,D22PostSearchPacket.output,D22PostSearchPacket.words,
        D22PostSearchPacket.withSource,D22PostSearchPacket.withSourceWords,BankFieldProjection.result_encode]
    | skip
  · exact law_result g L K hn hs
  · exact activity_result g hg L K hn hs hq

theorem local_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat) [NeZero (generatedS L)]
    (hn : 0<g.vertices) (hs : 4 ≤ generatedS L)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length (publicRepetition L g.edges.length)) :
    producer.machine.OutputsWithin (input g L K) (producer.result (input g L K)) (producer.clock (input g L K)) := by
  have hl : law.machine.OutputsWithin (input g L K) (law.result (input g L K)) (law.clock (input g L K)) := by
    apply compose_outputs
    · apply serialise_outputs
      intro k
      fin_cases k <;> exact project_outputs _ _
    · rw [lawInput_result]
      have h:=law_bound (generatedS L) g.vertices hs hn
      have he:lawQuery.result (V40IndexedLawLoop.input (generatedS L) g.vertices)=lawBytes g L hn hs:=
        (BitMachine.outputsWithin_at_bound V40IndexedLawLoop.machine h).2
      rw [he]
      exact h
  have ha : activity.machine.OutputsWithin (input g L K) (activity.result (input g L K)) (activity.clock (input g L K)) := by
    apply compose_outputs
    · apply serialise_outputs
      intro k
      fin_cases k <;> exact project_outputs _ _
    · rw [activityInput_result]
      have h:=V40ActivityTable.outputs_polynomial g hg hn (by omega) hq
      have he:activityQuery.result (V40ActivityTable.input g (generatedS L)
          (publicRepetition L g.edges.length) (generatedQ₂ L))=activityBytes g hg L hs hq:=
        (BitMachine.outputsWithin_at_bound V40ActivityTable.machine h).2
      rw [he]
      exact h
  apply serialise_outputs
  intro k
  fin_cases k
  all_goals first | exact project_outputs _ _ | skip
  · exact hl
  · exact ha

theorem producer_polynomial : HasPolynomialEnvelope producer := by
  have hl : HasPolynomialEnvelope law:=compose_polynomial (by
    apply serialise_polynomial
    intro k
    fin_cases k <;> exact project_polynomial _)
      (finite_run_polynomial V40IndexedLawLoop.machine lawCoefficient lawDegree)
  have ha : HasPolynomialEnvelope activity:=compose_polynomial (by
    apply serialise_polynomial
    intro k
    fin_cases k <;> exact project_polynomial _)
      (finite_run_polynomial V40ActivityTable.machine V40ActivityTable.coefficient V40ActivityTable.degree)
  apply serialise_polynomial
  intro k
  fin_cases k
  all_goals first | exact project_polynomial _ | skip
  · exact hl
  · exact ha
def coefficient:=Classical.choose producer_polynomial
def degree:=Classical.choose (Classical.choose_spec producer_polynomial)
theorem envelope : Envelope producer coefficient degree:=
  Classical.choose_spec (Classical.choose_spec producer_polynomial)

/-- Closed ordinary source-context production. No activity/law advice,
prepared state, run, output-size cap, or supplied per-cell program occurs. -/
theorem outputs (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat) [NeZero (generatedS L)]
    (hn : 0<g.vertices) (hs : 4 ≤ generatedS L)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length (publicRepetition L g.edges.length)) :
    machine.OutputsWithin (input g L K) (output g hg L K hn hs hq)
      (coefficient*((input g L K).length+1)^degree) := by
  have h:=local_outputs g hg L K hn hs hq
  rw [result g hg L K hn hs hq] at h
  apply BitMachine.outputsWithin_mono machine h
  have he:=envelope (input g L K)
  omega
theorem outputs_polynomial (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat) [NeZero (generatedS L)]
    (hn : 0<g.vertices) (hs : 4 ≤ generatedS L)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length (publicRepetition L g.edges.length)) :
    machine.OutputsWithin (input g L K) (output g hg L K hn hs hq)
      (coefficient*((input g L K).length+1)^degree) := outputs g hg L K hn hs hq

#print axioms outputs
end
end CurrentAdditive.V40SourceContextWriter
