import EthInapproximability.CurrentPaper.WeightedRawWordsLevel0K

/-! Lane owner:b-weighted-level-3, unit 2, segment 1 (2c-ii), first piece:
a physical `|VG|` word retained from a GraphCountBridge run.

The frozen raw-words S3 (`WeightedRawWordsEdges.edges_run`) runs the embedded
production `GraphCountBridge.program` and CLEARS its unary vertex-count
output. The raw-words modules are frozen, so this successor stage does not
modify them. It is appended AFTER the frozen fixed program
`rawWordsKProgram M c` (whose exit bank retains the master graph word `Gw`):
a charged copy of `Gw` into the private parser input of the (empty) `graph`
region, a guard bit, the production `GraphCountBridge.program` (via
`GraphCountBridge.same_graph_run`, reused by name), a charged copy of the
vertex-count cell into the retained cell `vCell = aux (.w 7)` (a word-scratch
cell no raw-words stage uses), and an exact-length clear of the parser
residue. The parse is a second, charged run of the same production parser on
the same bytes (redundant work, not an inserted value).

The retained word is `unary (serializeGraph G).vertices = unary |VG|`
(production `EncodedETHSource.serializeGraph_vertices`, `rfl`). -/

namespace EthInapproximability.CurrentPaper.WeightedVertexWord

open Turing BitMachineEncoding BitMachineStackEmbedding WeightedRawWords

noncomputable section

/-- The retained vertex-count cell. -/
def vCell : Global := aux (.w 7)

def gCopyV := copyProg (aux (.graph gV)) vCell (by simp [vCell]) (by simp) (by simp [vCell])

def v3 := BitMachineRawSequence.program gCopyV (clearProgram graphCells) 0 none ((), none)
def v2 := BitMachineRawSequence.program graphProgram v3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) gStartCtrl (none, ((), none))
def v1 := BitMachineRawSequence.program (SourceClauseFixedUnary.program (aux (.graph gIn)) 1) v2
  (BitMachineRawSequence.leftLabel (.inr .gate)) () (gStartCtrl, (none, ((), none)))
/-- The vertex-word program. -/
def vertexProgram := BitMachineRawSequence.program gCopyIn v1
  (BitMachineRawSequence.leftLabel 0) none ((), (gStartCtrl, (none, ((), none))))

abbrev VertexCtrlT := BitMachineRawSequence.Control (Option Bool)
  (BitMachineRawSequence.Control Unit (BitMachineRawSequence.Control GCtrl
    (BitMachineRawSequence.Control (Option Bool) (Unit × Option Bool))))
def vertexCtrl : VertexCtrlT := (none, ((), (gStartCtrl, (none, ((), none)))))

def vertexBound (g : EncodedGraph.Graph) : ℕ :=
  (2 * (EncodedGraph.encode g).length + 2) + 2 +
    101 * ((EncodedGraph.encode g).length + 1)^3 +
    (2 * g.vertices + 2) +
    ((g.vertices + g.edges.length + (SourceNormalizationMachineDecode.endpointStream g).length)
      + 3 + 2) + 4

theorem vertex_run {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (X0 : Global → List Bool)
    (hGw : X0 (aux .Gw) = EncodedGraph.encode (EncodedETHSource.serializeGraph G))
    (hgr : ∀ k, X0 (aux (.graph k)) = []) (hv : X0 vCell = [])
    (hcs : X0 (aux .cs) = []) :
    ∃ t ≤ vertexBound (EncodedETHSource.serializeGraph G),
      ((advance vertexProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), vertexCtrl, X0⟩ :
          TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, vertexCtrl, Function.update X0 vCell (List.replicate (Fintype.card V) true)⟩ := by
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
  -- 3. embedded GraphCountBridge run (production, reused by name)
  obtain ⟨t3, ht3, hr3, _, _⟩ := GraphCountBridge.same_graph_run G noWriter
  have s3 := region_run graphSlots GraphCountBridge.program _ _ t3 hr3 X2
    (by
      intro k
      rw [graph_start_stk]
      by_cases hk : k = gIn
      · subst hk; simp [hX2, graphSlots, hw, hg]
      · simp [hk, hX2, graphSlots, hgr])
  set X3 := bank graphSlots X2 (GraphCountBridge.finish g noWriter).stk with hX3
  have hX3V : X3 (aux (.graph gV)) = List.replicate (Fintype.card V) true := by
    rw [hX3, show aux (.graph gV) = graphSlots gV from rfl, bank_at, graph_finish_stk]
    simp [hg]
  have hX3out : ∀ j, (¬ ∃ k, graphSlots k = j) → X3 j = X2 j :=
    fun j hj => bank_outside _ _ _ j hj
  have notg : ∀ a : Aux, (∀ k, a ≠ .graph k) → ¬ ∃ k, graphSlots k = aux a := by
    rintro a ha ⟨k, hk⟩
    exact ha k (Sum.inr.inj hk).symm
  have hX3cs : X3 (aux .cs) = [] := by
    rw [hX3out _ (notg _ (by intro k; simp))]
    simp [hX2, hcs]
  have hX3v : X3 vCell = [] := by
    rw [vCell, hX3out _ (notg _ (by intro k; simp)), hX2, Function.update_of_ne (by simp)]
    exact hv
  -- 4. copy the vertex count out to the retained cell
  have s4 := copy_word (aux (.graph gV)) vCell (by simp [vCell]) (by simp) (by simp [vCell])
    X3 hX3v hX3cs
  rw [hX3V] at s4
  simp only [List.length_replicate] at s4
  set X4 := Function.update X3 vCell (List.replicate (Fintype.card V) true) with hX4
  -- 5. exact-length clear of the parser residue
  have s5 := clear_run graphCells graphCells_injective X4
  have hsum : (∑ i, (X4 (graphCells i)).length) =
      g.vertices + g.edges.length + (SourceNormalizationMachineDecode.endpointStream g).length := by
    have hv0 : X4 (graphCells 0) = List.replicate g.vertices true := by
      simp only [hX4, graphCells, vCell]
      rw [Function.update_of_ne (by simp), hX3,
        show aux (.graph gV) = graphSlots gV from rfl, bank_at, graph_finish_stk]
      simp
    have he : X4 (graphCells 1) = List.replicate g.edges.length true := by
      simp only [hX4, graphCells, vCell]
      rw [Function.update_of_ne (by simp), hX3,
        show aux (.graph gE) = graphSlots gE from rfl, bank_at, graph_finish_stk]
      simp [gV, gE]
    have hs : X4 (graphCells 2) = SourceNormalizationMachineDecode.endpointStream g := by
      simp only [hX4, graphCells, vCell]
      rw [Function.update_of_ne (by simp), hX3,
        show aux (.graph gS) = graphSlots gS from rfl, bank_at, graph_finish_stk]
      simp [gV, gE, gS]
    rw [Fin.sum_univ_three, hv0, he, hs]
    simp
  have hfin : BitMachineClearBank.cleared graphCells X4 =
      Function.update X0 vCell (List.replicate (Fintype.card V) true) := by
    have nV : ∀ i, graphCells i ≠ vCell := fun i => by
      fin_cases i <;> simp [graphCells, vCell]
    rw [hX4, cleared_update_comm _ _ _ _ nV]
    congr 1
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
  rw [hfin] at s5
  -- compose (four charged handoffs)
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs gCopyV (clearProgram graphCells)
    BitMachineCopy.Label.scan 0 none none ((), none) ((), none) X3 X4
    (Function.update X0 vCell (List.replicate (Fintype.card V) true)) _ _ s4 s5
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs graphProgram v3
    (.inr .gate) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    gStartCtrl gDoneCtrl (none, ((), none)) (none, ((), none))
    X2 X3 (Function.update X0 vCell (List.replicate (Fintype.card V) true)) t3 _ s3 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (aux (.graph gIn)) 1) v2
    0 (BitMachineRawSequence.leftLabel (.inr .gate)) () ()
    (gStartCtrl, (none, ((), none))) (gStartCtrl, (none, ((), none)))
    (Function.update X0 (aux (.graph gIn)) w) X2
    (Function.update X0 vCell (List.replicate (Fintype.card V) true)) _ _ s2 r2
  obtain ⟨u0, hu0, r0⟩ := BitMachineRawSequence.runs gCopyIn v1
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel 0) none none
    ((), (gStartCtrl, (none, ((), none))))
    ((), (gStartCtrl, (none, ((), none))))
    X0 (Function.update X0 (aux (.graph gIn)) w)
    (Function.update X0 vCell (List.replicate (Fintype.card V) true)) _ _ s1 r1
  refine ⟨u0, ?_, r0⟩
  rw [hsum] at hu3
  have hcardV : g.vertices = Fintype.card V := EncodedETHSource.serializeGraph_vertices G
  have ht3' : t3 ≤ 101 * (w.length + 1)^3 := by rw [hw, hg]; exact ht3
  unfold vertexBound
  rw [hcardV]
  rw [hcardV] at hu3
  rw [← hw]
  omega

#print axioms vertex_run

section Composite

variable (M : BitMachine.Machine)

/-- ONE fixed program: the frozen raw-words program with the k fuel, one
charged handoff, then the vertex-word stage. -/
def rawWordsKVProgram (c : ℕ) :=
  BitMachineRawSequence.program (rawWordsKProgram M c) vertexProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M))) vertexCtrl

/-- The level-0 master region with the k fuel and the retained vertex word. -/
def masterBankKV (M : BitMachine.Machine) (n : ℕ) (w : List Bool) (c b y e v : ℕ) :
    Aux → List Bool :=
  Function.update
    (Function.update (masterBank n w c b y e) Aux.K (List.replicate (kValue M n) true))
    (Aux.w 7) (List.replicate v true)

def rawWordsKVBound (n c : ℕ) (g : EncodedGraph.Graph) : ℕ :=
  rawWordsKBound M n c (EncodedGraph.encode g).length g + vertexBound g + 1

/-- Headline of the first piece: the same fixed start as the frozen
`level0_handoff_k`, the same consumer region, and the master region with
`K = unary k` AND `w 7 = unary |VG|`. -/
theorem level0_handoff_kv {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    ∃ t ≤ rawWordsKVBound M n c (EncodedETHSource.serializeGraph G),
      ((advance (rawWordsKVProgram M c))^[t])
        ⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.inl (.scan 0)))),
          ((none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M))), vertexCtrl),
          startBank (SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))⟩ =
        ⟨none, ((none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M))), vertexCtrl),
          Sum.elim
            (WeightedRawRowsSource.initialBank
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0)
              (EncodedETHSource.serializeGraph G) noW)
            (masterBankKV M n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c
              (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
              (Fintype.card E) (Fintype.card V))⟩ := by
  set w := EncodedGraph.encode (EncodedETHSource.serializeGraph G) with hw
  set b := EffectiveIteration.sourceDepth n with hb
  set X := Sum.elim
    (WeightedRawRowsSource.initialBank
      (EffectiveIteration.runParameters G c b (Iteration.seedState b) 0)
      (EncodedETHSource.serializeGraph G) noW)
    (Function.update (masterBank n w c b (Iteration.seedState b).budget (Fintype.card E))
      Aux.K (List.replicate (kValue M n) true)) with hX
  obtain ⟨t1, ht1, h1⟩ := level0_handoff_k M G n c
  have mK : ∀ a : Aux, a ≠ Aux.K → X (aux a) =
      masterBank n w c b (Iteration.seedState b).budget (Fintype.card E) a := by
    intro a ha
    show Function.update (masterBank n w c b (Iteration.seedState b).budget (Fintype.card E))
      Aux.K (List.replicate (kValue M n) true) a = _
    rw [Function.update_of_ne ha]
  obtain ⟨t2, ht2, h2⟩ := vertex_run G X
    (by rw [mK _ (by decide)]; simp only [masterBank, Function.update_apply]; simp; try exact hw)
    (by intro k; rw [mK _ (by simp)]; simp only [masterBank, Function.update_apply]; simp)
    (by rw [vCell, mK _ (by simp)]; simp only [masterBank, Function.update_apply]; simp)
    (by rw [mK _ (by decide)]; simp only [masterBank, Function.update_apply]; simp)
  have hfin : Function.update X vCell (List.replicate (Fintype.card V) true) =
      Sum.elim
        (WeightedRawRowsSource.initialBank
          (EffectiveIteration.runParameters G c b (Iteration.seedState b) 0)
          (EncodedETHSource.serializeGraph G) noW)
        (masterBankKV M n w c b (Iteration.seedState b).budget (Fintype.card E)
          (Fintype.card V)) := by
    rw [hX, vCell, aux, Sum.update_elim_inr]
    rfl
  rw [hfin] at h2
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs (rawWordsKProgram M c) vertexProgram
    (BitMachineRawSequence.leftLabel (.inl (.scan 0)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M)))
    (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M)))
    vertexCtrl vertexCtrl
    (startBank (SourceOriginalBranchPackets.packet n w)) X _ t1 t2 h1 h2
  refine ⟨t, ?_, h⟩
  unfold rawWordsKVBound
  omega

#print axioms level0_handoff_kv

end Composite

end
end EthInapproximability.CurrentPaper.WeightedVertexWord
