import EthInapproximability.CurrentPaper.WeightedRawWordsLevel0

/-! # S3: the edge word from the literal graph bytes

A charged copy of master `Gw` goes to the private parser input of the `graph`
region, a guard bit is pushed, and the production `GraphCountBridge.program`
(embedded, writer cells in the same private region, all empty) parses it.
`GraphCountBridge.same_graph_run` gives the unary edge count
`Fintype.card E`, which is copied into consumer word 5 and master `E`; the
parser residue (unary vertices, count, endpoint stream) is cleared with its
exact lengths. The consumer's own parser cells are not used. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

def graphSlots : GraphCountBridge.Stack ↪ Global :=
  ⟨fun k => aux (.graph k), by intro a b h; simpa [aux] using h⟩

def graphProgram := fun l => stackStmt graphSlots (GraphCountBridge.program l)

def gIn : GraphCountBridge.Stack := .inl (.inl 0)
def gV : GraphCountBridge.Stack := .inl (.inr 0)
def gE : GraphCountBridge.Stack := .inl (.inr 1)
def gS : GraphCountBridge.Stack := .inl (.inr 4)

def noWriter : GraphCountBridge.WriterStack → List Bool := fun _ => []

theorem graph_start_stk (g : EncodedGraph.Graph) (k : GraphCountBridge.Stack) :
    (GraphCountBridge.start g noWriter).stk k =
      if k = gIn then true :: EncodedGraph.encode g else [] := by
  unfold GraphCountBridge.start
  unfold stackCfg
  dsimp only
  rcases k with p | j
  · rw [show (Sum.inl p : GraphCountBridge.Stack) = GraphCountBridge.parserSlots p from rfl,
      bank_at]
    rcases p with i | i <;> fin_cases i <;>
      simp [SourceNormalizationMachineDecode.guardedStart, SourceNormalizationMachineDecode.cfg,
        SourceNormalizationMachineField.Data.stacks, gIn, GraphCountBridge.parserSlots]
  · rw [bank_outside _ _ _ _ (by rintro ⟨p, hp⟩; cases hp)]
    simp [gIn, noWriter]

theorem graph_finish_stk (g : EncodedGraph.Graph) (k : GraphCountBridge.Stack) :
    (GraphCountBridge.finish g noWriter).stk k =
      if k = gV then List.replicate g.vertices true
      else if k = gE then List.replicate g.edges.length true
      else if k = gS then SourceNormalizationMachineDecode.endpointStream g else [] := by
  unfold GraphCountBridge.finish
  unfold stackCfg
  dsimp only
  rcases k with p | j
  · rw [show (Sum.inl p : GraphCountBridge.Stack) = GraphCountBridge.parserSlots p from rfl,
      bank_at]
    rcases p with i | i <;> fin_cases i <;>
      simp [SourceNormalizationMachineDecode.cfg,
        SourceNormalizationMachineField.Data.stacks, gV, gE, gS, GraphCountBridge.parserSlots]
  · rw [bank_outside _ _ _ _ (by rintro ⟨p, hp⟩; cases hp)]
    simp [gV, gE, gS, noWriter]

def graphCells : Fin 3 → Global
  | 0 => aux (.graph gV)
  | 1 => aux (.graph gE)
  | 2 => aux (.graph gS)

theorem graphCells_injective : Function.Injective graphCells := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [graphCells, gV, gE, gS]

def gCopyIn := copyProg (aux .Gw) (aux (.graph gIn)) (by simp) (by simp) (by simp)
def gCopy5 := copyProg (aux (.graph gE)) (rawCell 5) (aux_ne_rawCell 5 _) (by simp)
  (rawCell_ne_aux 5 _)
def gCopyE := copyProg (aux (.graph gE)) (aux .E) (by simp [gE]) (by simp) (by simp)

abbrev GCtrl := SourceNormalizationMachineDecode.Control
def gStartCtrl : GCtrl := (SourceNormalizationMachineField.initialControl, .count, none)
def gDoneCtrl : GCtrl := SourceNormalizationMachineDecode.doneControl true

def e4 := BitMachineRawSequence.program gCopyE (clearProgram graphCells) 0 none ((), none)
def e3 := BitMachineRawSequence.program gCopy5 e4
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, ((), none))
def e2 := BitMachineRawSequence.program graphProgram e3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) gStartCtrl
  (none, (none, ((), none)))
def e1 := BitMachineRawSequence.program (SourceClauseFixedUnary.program (aux (.graph gIn)) 1) e2
  (BitMachineRawSequence.leftLabel (.inr .gate)) () (gStartCtrl, (none, (none, ((), none))))
/-- The S3 program. -/
def edgesProgram := BitMachineRawSequence.program gCopyIn e1
  (BitMachineRawSequence.leftLabel 0) none ((), (gStartCtrl, (none, (none, ((), none)))))

abbrev EdgesCtrlT := BitMachineRawSequence.Control (Option Bool)
  (BitMachineRawSequence.Control Unit (BitMachineRawSequence.Control GCtrl
    (BitMachineRawSequence.Control (Option Bool)
      (BitMachineRawSequence.Control (Option Bool) (Unit × Option Bool)))))
def edgesCtrl : EdgesCtrlT := (none, ((), (gStartCtrl, (none, (none, ((), none))))))

def edgesBound (g : EncodedGraph.Graph) : ℕ :=
  (2 * (EncodedGraph.encode g).length + 2) + 2 +
    101 * ((EncodedGraph.encode g).length + 1)^3 +
    (2 * g.edges.length + 2) + (2 * g.edges.length + 2) +
    ((g.vertices + g.edges.length + (SourceNormalizationMachineDecode.endpointStream g).length)
      + 3 + 2) + 5

def afterEdges (X0 : Global → List Bool) (e : ℕ) : Global → List Bool :=
  Function.update (Function.update X0 (rawCell 5) (List.replicate e true))
    (aux .E) (List.replicate e true)

theorem edges_run {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (X0 : Global → List Bool)
    (hGw : X0 (aux .Gw) = EncodedGraph.encode (EncodedETHSource.serializeGraph G))
    (hgr : ∀ k, X0 (aux (.graph k)) = []) (h5 : X0 (rawCell 5) = [])
    (hE : X0 (aux .E) = []) (hcs : X0 (aux .cs) = []) :
    ∃ t ≤ edgesBound (EncodedETHSource.serializeGraph G),
      ((advance edgesProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), edgesCtrl, X0⟩ :
          TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, edgesCtrl, afterEdges X0 (Fintype.card E)⟩ := by
  set g := EncodedETHSource.serializeGraph G with hg
  set w := EncodedGraph.encode g with hw
  -- 1. copy Gw into the private parser input
  have s1 := copy_word (aux .Gw) (aux (.graph gIn)) (by simp) (by simp) (by simp) X0
    (hgr gIn) hcs
  rw [hGw] at s1
  -- 2. guard bit
  have s2 := push_unary (aux (.graph gIn)) (Function.update X0 (aux (.graph gIn)) w) 1
  rw [Function.update_self, Function.update_idem] at s2
  set X2 := Function.update X0 (aux (.graph gIn)) (List.replicate 1 true ++ w) with hX2
  -- 3. embedded GraphCountBridge run
  obtain ⟨t3, ht3, hr3, hcnt, _⟩ := GraphCountBridge.same_graph_run G noWriter
  have s3 := region_run graphSlots GraphCountBridge.program _ _ t3 hr3 X2
    (by
      intro k
      rw [graph_start_stk]
      by_cases hk : k = gIn
      · subst hk; simp [hX2, graphSlots, hw, hg]
      · simp [hk, hX2, graphSlots, hgr])
  set X3 := bank graphSlots X2 (GraphCountBridge.finish g noWriter).stk with hX3
  have hX3E : X3 (aux (.graph gE)) = List.replicate (Fintype.card E) true := by
    rw [hX3, show aux (.graph gE) = graphSlots gE from rfl, bank_at]
    exact hcnt
  have hX3out : ∀ j, (¬ ∃ k, graphSlots k = j) → X3 j = X2 j :=
    fun j hj => bank_outside _ _ _ j hj
  have notg : ∀ a : Aux, (∀ k, a ≠ .graph k) → ¬ ∃ k, graphSlots k = aux a := by
    rintro a ha ⟨k, hk⟩
    exact ha k (Sum.inr.inj hk).symm
  have hX35 : X3 (rawCell 5) = [] := by
    rw [hX3out _ (by rintro ⟨k, hk⟩; exact rawCell_ne_aux 5 _ hk.symm)]
    simp [hX2, h5]
  have hX3cs : X3 (aux .cs) = [] := by
    rw [hX3out _ (notg _ (by intro k; simp))]
    simp [hX2, hcs]
  have hX3Ecell : X3 (aux .E) = [] := by
    rw [hX3out _ (notg _ (by intro k; simp))]
    simp [hX2, hE]
  -- 4, 5. copy the count out twice
  have s4 := copy_word (aux (.graph gE)) (rawCell 5) (aux_ne_rawCell 5 _) (by simp)
    (rawCell_ne_aux 5 _) X3 hX35 hX3cs
  rw [hX3E] at s4
  simp only [List.length_replicate] at s4
  set X4 := Function.update X3 (rawCell 5) (List.replicate (Fintype.card E) true) with hX4
  have s5 := copy_word (aux (.graph gE)) (aux .E) (by simp [gE]) (by simp) (by simp) X4
    (by simp [hX4, hX3Ecell]) (by simp [hX4, hX3cs])
  have hX4E : X4 (aux (.graph gE)) = List.replicate (Fintype.card E) true := by
    simp [hX4, hX3E]
  rw [hX4E] at s5
  simp only [List.length_replicate] at s5
  set X5 := Function.update X4 (aux .E) (List.replicate (Fintype.card E) true) with hX5
  -- 6. exact-length clear of the parser residue
  have s6 := clear_run graphCells graphCells_injective X5
  have hsum : (∑ i, (X5 (graphCells i)).length) =
      g.vertices + g.edges.length + (SourceNormalizationMachineDecode.endpointStream g).length := by
    have hv : X5 (graphCells 0) = List.replicate g.vertices true := by
      simp only [hX5, hX4, graphCells]
      rw [Function.update_of_ne (by simp), Function.update_of_ne (aux_ne_rawCell 5 _), hX3,
        show aux (.graph gV) = graphSlots gV from rfl, bank_at, graph_finish_stk]
      simp
    have he : X5 (graphCells 1) = List.replicate g.edges.length true := by
      simp only [hX5, hX4, graphCells]
      rw [Function.update_of_ne (by simp), Function.update_of_ne (aux_ne_rawCell 5 _), hX3,
        show aux (.graph gE) = graphSlots gE from rfl, bank_at, graph_finish_stk]
      simp [gV, gE]
    have hs : X5 (graphCells 2) = SourceNormalizationMachineDecode.endpointStream g := by
      simp only [hX5, hX4, graphCells]
      rw [Function.update_of_ne (by simp), Function.update_of_ne (aux_ne_rawCell 5 _), hX3,
        show aux (.graph gS) = graphSlots gS from rfl, bank_at, graph_finish_stk]
      simp [gV, gE, gS]
    rw [Fin.sum_univ_three, hv, he, hs]
    simp
  have hfin : BitMachineClearBank.cleared graphCells X5 = afterEdges X0 (Fintype.card E) := by
    have nE : ∀ i, graphCells i ≠ aux .E := fun i => by fin_cases i <;> simp [graphCells]
    have n5 : ∀ i, graphCells i ≠ rawCell 5 := fun i => by
      fin_cases i <;> exact aux_ne_rawCell 5 _
    rw [hX5, cleared_update_comm _ _ _ _ nE, hX4, cleared_update_comm _ _ _ _ n5]
    unfold afterEdges
    congr 2
    funext j
    unfold BitMachineClearBank.cleared
    by_cases hr : ∃ k, graphSlots k = j
    · obtain ⟨k, rfl⟩ := hr
      have hr0 : X0 (graphSlots k) = [] := hgr k
      rw [hr0]
      split_ifs with hc
      · rfl
      · rw [hX3, bank_at, graph_finish_stk]
        have h1 : k ≠ gV := fun h => hc ⟨0, by rw [h]; rfl⟩
        have h2 : k ≠ gE := fun h => hc ⟨1, by rw [h]; rfl⟩
        have h3 : k ≠ gS := fun h => hc ⟨2, by rw [h]; rfl⟩
        rw [if_neg h1, if_neg h2, if_neg h3]
    · have hnc : ¬ ∃ i, graphCells i = j := by
        rintro ⟨i, rfl⟩
        fin_cases i
        · exact hr ⟨gV, rfl⟩
        · exact hr ⟨gE, rfl⟩
        · exact hr ⟨gS, rfl⟩
      rw [if_neg hnc, hX3out _ hr, hX2, Function.update_of_ne]
      rintro rfl
      exact hr ⟨gIn, rfl⟩
  rw [hfin] at s6
  -- compose
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs gCopyE (clearProgram graphCells)
    BitMachineCopy.Label.scan 0 none none ((), none) ((), none) X4 X5
    (afterEdges X0 (Fintype.card E)) _ _ s5 s6
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs gCopy5 e4
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, ((), none)) (none, ((), none)) X3 X4 (afterEdges X0 (Fintype.card E))
    _ _ s4 r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs graphProgram e3
    (.inr .gate) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    gStartCtrl gDoneCtrl (none, (none, ((), none))) (none, (none, ((), none)))
    X2 X3 (afterEdges X0 (Fintype.card E)) t3 _ s3 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (aux (.graph gIn)) 1) e2
    0 (BitMachineRawSequence.leftLabel (.inr .gate)) () ()
    (gStartCtrl, (none, (none, ((), none)))) (gStartCtrl, (none, (none, ((), none))))
    (Function.update X0 (aux (.graph gIn)) w) X2 (afterEdges X0 (Fintype.card E)) _ _ s2 r2
  obtain ⟨u0, hu0, r0⟩ := BitMachineRawSequence.runs gCopyIn e1
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel 0) none none
    ((), (gStartCtrl, (none, (none, ((), none)))))
    ((), (gStartCtrl, (none, (none, ((), none)))))
    X0 (Function.update X0 (aux (.graph gIn)) w) (afterEdges X0 (Fintype.card E)) _ _ s1 r1
  refine ⟨u0, ?_, r0⟩
  rw [hsum] at hu4
  have hcardE : g.edges.length = Fintype.card E := EncodedETHSource.serializeGraph_edges G
  have ht3' : t3 ≤ 101 * (w.length + 1)^3 := by rw [hw, hg]; exact ht3
  unfold edgesBound
  rw [hcardE]
  rw [← hw]
  omega

#print axioms edges_run

end
end EthInapproximability.CurrentPaper.WeightedRawWords
