import EthInapproximability.CurrentPaper.WeightedScaleDerivedFromBins
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! One raw-six and one exact graph-code input through bins, graph counts,
order, same-graph q₂, firstExponent, and balanceOrder. -/

namespace EthInapproximability.CurrentPaper.WeightedPrefixAT

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := WeightedScaleDerivedFromBins.Stack
def prefixSlots := WeightedScaleDerivedFromBins.upstreamSlots
def writer := WeightedScaleDerivedFromBins.writer
def initialBank (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) : Stack → List Bool :=
  WeightedScaleDerivedFromBins.initialBank
    (WeightedBinsGraphQ.initialBank i g W)
def finalBank (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) : Stack → List Bool :=
  WeightedScaleDerivedFromBins.finalBank
    (WeightedBinsGraphQ.afterGraph i g W F Q) i
def prefixProgram := fun l => stackStmt prefixSlots
  (WeightedBinsGraphQ.program l)
def program := BitMachineRawSequence.program prefixProgram
  WeightedScaleDerivedFromBins.program
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      WeightedScaleDerivedFromBins.aStart))
  WeightedBinsGraphQ.initialControl
  WeightedScaleDerivedFromBins.initialControl
def initialControl :=
  (WeightedBinsGraphQ.initialControl,
    WeightedScaleDerivedFromBins.initialControl)
def bound (i : Parameters.Input) (g : EncodedGraph.Graph)
    (e : ℕ) : ℕ :=
  WeightedBinsGraphQ.bound i g e +
  WeightedScaleDerivedFromBins.bound i + 1

theorem source_run {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (i : Parameters.Input)
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : Fin 64 → List Bool)
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let g := EncodedETHSource.serializeGraph G
    ∃ u ≤ bound i g (Fintype.card E),
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
      ∃ Q : WeightedGraphQJoined.Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                BinsWriterAssembly.binStart))),
            initialControl,initialBank i g W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,finalBank i g W F Q⟩ ∧
        (finalBank i g W F Q) (writer 54) =
          List.replicate (Parameters.firstExponent i) true ∧
        (finalBank i g W F Q)
            (WeightedScaleDerivedFromBins.balance 1) =
          List.replicate (Parameters.balanceOrder i) true ∧
        (finalBank i g W F Q) (writer 56) =
          List.replicate
            (ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)) true ∧
        (finalBank i g W F Q) (writer 17) = W 17 ∧
        (finalBank i g W F Q) (writer 57) = W 57 := by
  let g := EncodedETHSource.serializeGraph G
  let S0 := WeightedBinsGraphQ.initialBank i g W
  obtain ⟨up,hup,v,F,Q,hprefix,hq,h54pre,h17pre,h57pre,hscale,hparam⟩ :=
    WeightedBinsGraphQ.source_run i G W h28 h61
      h7 h8 h9 h10 h11 h12 h13 h14 h15 h18
      h54 h55 h56 h57 h58 h60
  let S := WeightedBinsGraphQ.afterGraph i g W F Q
  have hs : S (.inl (.inl (.inr ScaleFinalScratch.answerKey))) =
      List.replicate (Parameters.scale i) true := by
    exact (hparam (.inl (.inr ScaleFinalScratch.answerKey))).trans hscale
  obtain ⟨ua,hua,ha,ha54,ht,hwriter⟩ :=
    WeightedScaleDerivedFromBins.run S i hs h54pre
  have hLift :
      ((advance prefixProgram)^[up])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)),
          WeightedBinsGraphQ.initialControl,initialBank i g W⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,WeightedBinsGraphQ.initialControl,
          WeightedScaleDerivedFromBins.initialBank S⟩ := by
    have he := BitMachineStackRun.run prefixSlots
      (initialBank i g W) WeightedBinsGraphQ.program
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)),
        WeightedBinsGraphQ.initialControl,S0⟩ :
        TM2.Cfg (fun _ : WeightedBinsGraphQ.Stack => Bool) _ _) up
    rw [hprefix] at he
    have hi : bank prefixSlots (initialBank i g W) S0 =
        initialBank i g W := by
      apply bank_eq_self
      intro j
      rfl
    have ho : bank prefixSlots (initialBank i g W) S =
        WeightedScaleDerivedFromBins.initialBank S := by
      funext j
      cases j with
      | inl j => exact bank_at prefixSlots _ _ j
      | inr j =>
          rw [bank_outside]
          · rfl
          · rintro ⟨k,h⟩; cases h
    simpa only [prefixProgram,stackCfg,hi,ho,S0,S,g]
      using he
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    prefixProgram WeightedScaleDerivedFromBins.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        WeightedScaleDerivedFromBins.aStart))
    WeightedBinsGraphQ.initialControl WeightedBinsGraphQ.initialControl
    WeightedScaleDerivedFromBins.initialControl
    WeightedScaleDerivedFromBins.initialControl
    (initialBank i g W)
    (WeightedScaleDerivedFromBins.initialBank S)
    (finalBank i g W F Q)
    up ua hLift (by simpa only [finalBank] using ha)
  refine ⟨u,?_,v,F,Q,?_,ha54,ht,?_,?_,?_⟩
  · change u ≤ WeightedBinsGraphQ.bound i g (Fintype.card E) +
      WeightedScaleDerivedFromBins.bound i + 1
    have hup' : up ≤ WeightedBinsGraphQ.bound i g (Fintype.card E) := by
      simpa only [g] using hup
    omega
  · simpa only [program,initialControl] using hr
  · exact (hwriter 56 (by decide)).trans hq
  · exact (hwriter 17 (by decide)).trans h17pre
  · exact (hwriter 57 (by decide)).trans h57pre

#print axioms source_run

end
end EthInapproximability.CurrentPaper.WeightedPrefixAT
