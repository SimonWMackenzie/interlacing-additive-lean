import EthInapproximability.CurrentPaper.WeightedRawWordsEdges

/-! # S4a: the admitted consumer start bank, cell by cell

`WeightedRawRowsSource.initialBank i g (fun _ => [])` is proved equal to an
explicit update chain on the empty bank: the six raw words of `i` and the
guarded graph code `true :: EncodedGraph.encode g` in the consumer's own
parser input cell. Every other consumer cell is empty. This is bookkeeping
about the admitted definition, not a machine. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

abbrev WB := WeightedBinsGraphQ.Stack

def rawWB (j : Fin 6) : WB :=
  WeightedBinsGraphQ.binSlots (WeightedBinsGeneric.paramSlots
    (ETHBinsJoinedScratch.scaleEmbed (ETHScaleActualComplete.oldEmbed (ETHScaleGlobalLog.raw j))))

def pInGQ : WeightedGraphQJoined.Stack :=
  WeightedGraphQJoined.parserWriterSlots (GraphVertexPreludeJoin.parserSlots (.inl 0))

def pInWB : WB := .inr pInGQ

/-- The consumer's parser input cell. -/
def pInCons : Cons := .inl (.inl (.inl pInWB))
def consRaw (j : Fin 6) : Cons := .inl (.inl (.inl (rawWB j)))

theorem consRaw_eq (j : Fin 6) : cons (consRaw j) = rawCell j := rfl

def pInCell : Global := cons pInCons

theorem bank_empty {K J : Type*} [DecidableEq K] [DecidableEq J] (ι : K ↪ J) :
    bank ι (fun _ => []) (fun _ => []) = fun _ => [] := by
  funext j
  by_cases h : ∃ k, ι k = j
  · obtain ⟨k, rfl⟩ := h
    rw [bank_at]
  · rw [bank_outside _ _ _ _ h]

theorem sum_elim_empty {A B : Type*} :
    (Sum.elim (fun _ : A => ([] : List Bool)) (fun _ : B => [])) = fun _ => [] := by
  funext j
  cases j <;> rfl

abbrev W6 (i : Parameters.Input) := ETHParameterScaleMachineInput.words i

theorem initial_chain (i : Parameters.Input) :
    ETHScaleGlobalLog.initial i =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (fun _ => [])
          (ETHScaleGlobalLog.raw 1) (W6 i 1)) (ETHScaleGlobalLog.raw 2) (W6 i 2))
          (ETHScaleGlobalLog.raw 4) (W6 i 4)) (ETHScaleGlobalLog.raw 3) (W6 i 3))
          (ETHScaleGlobalLog.raw 5) (W6 i 5)) (ETHScaleGlobalLog.raw 0) (W6 i 0) := by
  funext s
  rcases s with k | r
  · fin_cases k <;> simp [ETHScaleGlobalLog.initial, ETHScaleGlobalLog.raw]
  · simp [ETHScaleGlobalLog.initial, ETHScaleGlobalLog.raw]

theorem guarded_stk (input : List Bool) :
    (SourceNormalizationMachineDecode.guardedStart input).stk =
      Function.update (fun _ => []) (.inl 0) input := by
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [SourceNormalizationMachineDecode.guardedStart, SourceNormalizationMachineDecode.cfg,
      SourceNormalizationMachineField.Data.stacks]

def noW : Fin 64 → List Bool := fun _ => []

theorem base_eq (g : EncodedGraph.Graph) :
    WeightedBinsGraphQ.base g noW =
      Function.update (fun _ => []) pInWB (true :: EncodedGraph.encode g) := by
  have h1 : (Sum.elim (fun _ => []) noW : GraphVertexPreludeJoin.Stack → List Bool) =
      fun _ => [] := by
    funext j; cases j <;> rfl
  have hp : (GraphVertexPreludeJoin.parserStart g noW).stk =
      Function.update (fun _ => []) (GraphVertexPreludeJoin.parserSlots (.inl 0))
        (true :: EncodedGraph.encode g) := by
    unfold GraphVertexPreludeJoin.parserStart
    unfold stackCfg
    dsimp only
    rw [guarded_stk, h1, bank_update, bank_empty]
  unfold WeightedBinsGraphQ.base WeightedGraphQJoined.initialBank WeightedGraphQJoined.lift
  rw [hp, bank_update, bank_empty]
  rw [← Sum.update_elim_inr, sum_elim_empty]
  rfl

theorem wb_chain (i : Parameters.Input) (g : EncodedGraph.Graph) :
    WeightedBinsGraphQ.initialBank i g noW =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update
          (Function.update (fun _ => []) pInWB (true :: EncodedGraph.encode g))
          (rawWB 1) (W6 i 1)) (rawWB 2) (W6 i 2))
          (rawWB 4) (W6 i 4)) (rawWB 3) (W6 i 3))
          (rawWB 5) (W6 i 5)) (rawWB 0) (W6 i 0) := by
  have hf : WeightedBinsGeneric.foreignBank noW = fun _ => [] := by
    funext j; cases j <;> rfl
  have hbase : bank WeightedBinsGraphQ.binSlots (WeightedBinsGraphQ.base g noW)
      (fun _ => []) = WeightedBinsGraphQ.base g noW := by
    apply bank_eq_self
    intro k
    rw [base_eq]
    rcases k with p | k
    · simp [WeightedBinsGraphQ.binSlots, pInWB]
    · simp [WeightedBinsGraphQ.binSlots, pInWB, pInGQ, WeightedGraphQJoined.writer,
        WeightedGraphQJoined.parserWriterSlots, QProduct.parserWriterSlots,
        GraphVertexPreludeJoin.parserSlots]
  unfold WeightedBinsGraphQ.initialBank WeightedBinsGeneric.initialBank
    ETHBinsJoinedScratch.initialBank ETHScaleActualComplete.initialBank
  rw [initial_chain, hf]
  simp only [bank_update, bank_empty]
  rw [hbase, base_eq]
  rfl

/-- The admitted consumer start bank with an empty writer. -/
theorem consumer_chain (i : Parameters.Input) (g : EncodedGraph.Graph) :
    WeightedRawRowsSource.initialBank i g noW =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update
          (Function.update (fun _ => []) pInCons (true :: EncodedGraph.encode g))
          (consRaw 1) (W6 i 1)) (consRaw 2) (W6 i 2))
          (consRaw 4) (W6 i 4)) (consRaw 3) (W6 i 3))
          (consRaw 5) (W6 i 5)) (consRaw 0) (W6 i 0) := by
  unfold WeightedRawRowsSource.initialBank WeightedScalarComplete.initialBank
    WeightedActualSizeSuffix.initialBank WeightedMTPrefix.initialBank
    WeightedPrefixAT.initialBank WeightedScaleDerivedFromBins.initialBank
  rw [wb_chain]
  simp only [← Sum.update_elim_inl, sum_elim_empty]
  rfl

#print axioms consumer_chain

end
end EthInapproximability.CurrentPaper.WeightedRawWords
