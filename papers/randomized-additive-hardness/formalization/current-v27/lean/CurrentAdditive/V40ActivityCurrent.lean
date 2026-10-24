import CurrentAdditive.V40ActivityTable

/-! The two physical enumeration orders are the current source's literal
numbered item and coordinate orders. Inactive cells print s. -/
namespace CurrentAdditive.V40ActivityCurrent
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V39GeneratedConstruction
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem row_entries {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (V40ActivityRow.count s g.vertices)) :
    V40ActivityRow.entries g s r i.val q2=List.ofFn (fun a : Fin q2=>
      (StoredStepContext.activityValue (graphActivity hs hq (LiteralEdgeEncoder.edge g hg)) i a).bits) := by
  apply List.ext_getElem
  · simp [V40ActivityRow.entries]
  · intro a ha hb
    simp only [V40ActivityRow.entries,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    have h:=V40SourceCell.result g hg hn hs i (Fin.cast hq ⟨a,by simpa using hb⟩)
    simpa [V40SourceCell.value,StoredStepContext.activityValue,graphActivity] using h

theorem row_packet {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (V40ActivityRow.count s g.vertices)) :
    V40ActivityRow.packet g s r q2 i.val=SourceListEncoding.encode (List.ofFn (fun a : Fin q2=>
      (StoredStepContext.activityValue (graphActivity hs hq (LiteralEdgeEncoder.edge g hg)) i a).bits)) := by
  rw [V40ActivityRow.packet,row_entries g hg hn hs hq i]

theorem packet {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r) :
    V40ActivityTable.packet g s r q2=
      StoredStepContext.activityWords (graphActivity hs hq (LiteralEdgeEncoder.edge g hg)) := by
  unfold V40ActivityTable.packet StoredStepContext.activityWords
  apply congrArg SourceListEncoding.encode
  apply List.ext_getElem
  · simp [V40ActivityTable.entries,V40ActivityTable.count,V40ActivityRow.count]
  · intro i hi hj
    simp only [V40ActivityTable.entries,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact row_packet g hg hn hs hq ⟨i,by simpa [V40ActivityTable.count,V40ActivityRow.count] using hj⟩

theorem outputs {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r) :
    V40ActivityTable.machine.OutputsWithin (V40ActivityTable.input g s r q2)
      (StoredStepContext.activityWords (graphActivity hs hq (LiteralEdgeEncoder.edge g hg)))
      (V40ActivityTable.clock g s r q2) := by
  rw [←packet g hg hn hs hq]
  exact V40ActivityTable.outputs g hg hn hs hq

#print axioms outputs
end
end CurrentAdditive.V40ActivityCurrent
