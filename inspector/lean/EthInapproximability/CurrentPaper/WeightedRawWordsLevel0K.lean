import EthInapproximability.CurrentPaper.WeightedRawWordsKFuel

/-! # S4 with S5 composed: the level-0 handoff including the k fuel

One fixed program: S1 (guarded) ; S2 ; S3 ; S4 tail ; S5 (`kProgram M`).
Its exit bank is the admitted consumer start bank of the level-0 same-object
input together with the master region `N, Gw, C, B, Y = y₀, E, K = unary k`,
`k = SlowClock.repetitions (CutoffBitMachine.clock M) n`. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

variable (M : BitMachine.Machine)

def afterS1KProgram :=
  BitMachineRawSequence.program afterS1Program (kProgram M)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (level0Ctrl, (edgesCtrl, tailCtrl)) (kCtrl M)

/-- The fixed level-0 raw-word program with the k fuel. -/
def rawWordsKProgram (c : ℕ) :=
  unpackProgram c (afterS1KProgram M)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel edgeStartLabel))))
    ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M)

theorem exitBank_kready {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    KReady (exitBank G n c) n where
  hN := by simp [exitBank, tailBank, afterEdges, level0Bank, costFinal, afterDepth, afterUnpack,
    afterParse, aux_ne_pIn]
  hnat := by
    intro r i
    simp [exitBank, tailBank, afterEdges, level0Bank, costFinal, afterDepth, afterUnpack,
      afterParse, aux_ne_pIn]
  hK := by simp [exitBank, tailBank, afterEdges, level0Bank, costFinal, afterDepth, afterUnpack,
    afterParse, aux_ne_pIn]
  hcs := by simp [exitBank, tailBank, afterEdges, level0Bank, costFinal, afterDepth, afterUnpack,
    afterParse, aux_ne_pIn]

def rawWordsKBound (n c N : ℕ) (g : EncodedGraph.Graph) : ℕ :=
  (7 * ((SourceOriginalBranchPackets.packet n (EncodedGraph.encode g)).length + 1) + 1) +
    ((c + 1) + ((level0Bound n + (edgesBound g + ((2 * c + 2) + ((2 * N + 2) + 2 + 1) + 1) + 1)
      + 1) + kBound M n + 1) + 1) + 1

theorem level0_handoff_k {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    ∃ t ≤ rawWordsKBound M n c (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length
        (EncodedETHSource.serializeGraph G),
      ((advance (rawWordsKProgram M c))^[t])
        (unpackStart c (SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
          ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M)) =
        ⟨none, (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M))),
          Sum.elim
            (WeightedRawRowsSource.initialBank
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0)
              (EncodedETHSource.serializeGraph G) noW)
            (Function.update
              (masterBank n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c
                (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
                (Fintype.card E))
              Aux.K (List.replicate (kValue M n) true))⟩ := by
  set w := EncodedGraph.encode (EncodedETHSource.serializeGraph G) with hw
  obtain ⟨t1, ht1, h1⟩ := level0_run n w c
  obtain ⟨t2, ht2, h2⟩ := edges_run G (level0Bank n w c)
    (by simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse, hw])
    (by intro k; simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
  obtain ⟨t3, ht3, h3⟩ := tail_run (afterEdges (level0Bank n w c) (Fintype.card E)) w c
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse,
      pInCell, rawCell, cons, aux, pInCons, pInWB, WeightedActualSizeSuffix.scaleKey])
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
  obtain ⟨t4, ht4, h4⟩ := k_run M n (exitBank G n c) (exitBank_kready G n c)
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs edgesProgram tailProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    edgesCtrl edgesCtrl tailCtrl tailCtrl (level0Bank n w c)
    (afterEdges (level0Bank n w c) (Fintype.card E)) (exitBank G n c) t2 t3 h2 h3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs level0Program
    (BitMachineRawSequence.program edgesProgram tailProgram
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) edgesCtrl tailCtrl)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel edgeStartLabel))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    level0Ctrl level0Ctrl (edgesCtrl, tailCtrl) (edgesCtrl, tailCtrl)
    (afterUnpack n w c) (level0Bank n w c) (exitBank G n c) t1 u2 h1 r2
  obtain ⟨u0, hu0, r0⟩ := BitMachineRawSequence.runs afterS1Program (kProgram M)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel edgeStartLabel)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (level0Ctrl, (edgesCtrl, tailCtrl)) (level0Ctrl, (edgesCtrl, tailCtrl)) (kCtrl M) (kCtrl M)
    (afterUnpack n w c) (exitBank G n c)
    (Function.update (exitBank G n c) (aux .K) (List.replicate (kValue M n) true)) u1 t4 r1 h4
  obtain ⟨t, ht, h⟩ := unpack_valid n w c (afterS1KProgram M)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel edgeStartLabel))))
    ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M) ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M)
    _ u0 r0
  refine ⟨t, ?_, ?_⟩
  · unfold rawWordsKBound
    rw [← hw]
    omega
  · rw [exitBank_eq, aux, Sum.update_elim_inr] at h
    exact h

#print axioms exitBank_kready
#print axioms level0_handoff_k

end
end EthInapproximability.CurrentPaper.WeightedRawWords
