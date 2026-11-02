import EthInapproximability.CurrentPaper.WeightedBinsGraphFrame
import EthInapproximability.CurrentPaper.WeightedPrefixAT

/-! Preserve the same-run actual bins/column input frame through the frozen
first-exponent and balance-order arithmetic. -/

namespace EthInapproximability.CurrentPaper.WeightedPrefixFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
open WeightedPrefixAT
noncomputable section

theorem source_run_framed {V E : Type*} [Fintype V] [DecidableEq V]
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
    ∃ u ≤ WeightedPrefixAT.bound i g (Fintype.card E),
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
      ∃ Q : WeightedGraphQJoined.Stack → List Bool,
        ((advance WeightedPrefixAT.program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                BinsWriterAssembly.binStart))),
            WeightedPrefixAT.initialControl,
            WeightedPrefixAT.initialBank i g W⟩ :
            TM2.Cfg (fun _ : WeightedPrefixAT.Stack => Bool) _ _) =
          ⟨none,WeightedPrefixAT.initialControl,
            WeightedPrefixAT.finalBank i g W F Q⟩ ∧
        (WeightedPrefixAT.finalBank i g W F Q)
          (WeightedPrefixAT.writer 54) =
            List.replicate (Parameters.firstExponent i) true ∧
        (WeightedPrefixAT.finalBank i g W F Q)
          (WeightedScaleDerivedFromBins.balance 1) =
            List.replicate (Parameters.balanceOrder i) true ∧
        (WeightedPrefixAT.finalBank i g W F Q)
          (WeightedPrefixAT.writer 56) =
            List.replicate
              (ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)) true ∧
        (WeightedPrefixAT.finalBank i g W F Q)
          (WeightedPrefixAT.writer 17) = W 17 ∧
        (WeightedPrefixAT.finalBank i g W F Q)
          (WeightedPrefixAT.writer 57) = W 57 ∧
        (WeightedPrefixAT.finalBank i g W F Q)
          (WeightedPrefixAT.writer 28) =
            List.replicate (Parameters.bins i) true ∧
        (WeightedPrefixAT.finalBank i g W F Q)
          (WeightedPrefixAT.writer 27) = W 27 := by
  let g := EncodedETHSource.serializeGraph G
  let S0 := WeightedBinsGraphQ.initialBank i g W
  obtain ⟨up,hup,v,F,Q,hprefix,hq,h54pre,h17pre,h57pre,h28pre,h27pre,
      hscale,hparam⟩ :=
    WeightedBinsGraphFrame.source_run_framed i G W h28 h61
      h7 h8 h9 h10 h11 h12 h13 h14 h15 h18
      h54 h55 h56 h57 h58 h60
  let S := WeightedBinsGraphQ.afterGraph i g W F Q
  have hs : S (.inl (.inl (.inr ScaleFinalScratch.answerKey))) =
      List.replicate (Parameters.scale i) true := by
    exact (hparam (.inl (.inr ScaleFinalScratch.answerKey))).trans hscale
  obtain ⟨ua,hua,ha,ha54,ht,hwriter⟩ :=
    WeightedScaleDerivedFromBins.run S i hs h54pre
  have hLift :
      ((advance WeightedPrefixAT.prefixProgram)^[up])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)),
          WeightedBinsGraphQ.initialControl,
          WeightedPrefixAT.initialBank i g W⟩ :
          TM2.Cfg (fun _ : WeightedPrefixAT.Stack => Bool) _ _) =
        ⟨none,WeightedBinsGraphQ.initialControl,
          WeightedScaleDerivedFromBins.initialBank S⟩ := by
    have he := BitMachineStackRun.run WeightedPrefixAT.prefixSlots
      (WeightedPrefixAT.initialBank i g W) WeightedBinsGraphQ.program
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)),
        WeightedBinsGraphQ.initialControl,S0⟩ :
        TM2.Cfg (fun _ : WeightedBinsGraphQ.Stack => Bool) _ _) up
    rw [hprefix] at he
    have hi : bank WeightedPrefixAT.prefixSlots
        (WeightedPrefixAT.initialBank i g W) S0 =
        WeightedPrefixAT.initialBank i g W := by
      apply bank_eq_self
      intro j
      rfl
    have ho : bank WeightedPrefixAT.prefixSlots
        (WeightedPrefixAT.initialBank i g W) S =
        WeightedScaleDerivedFromBins.initialBank S := by
      funext j
      cases j with
      | inl j => exact bank_at WeightedPrefixAT.prefixSlots _ _ j
      | inr j =>
          rw [bank_outside]
          · rfl
          · rintro ⟨k,h⟩; cases h
    simpa only [WeightedPrefixAT.prefixProgram,stackCfg,hi,ho,S0,S,g]
      using he
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    WeightedPrefixAT.prefixProgram WeightedScaleDerivedFromBins.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        WeightedScaleDerivedFromBins.aStart))
    WeightedBinsGraphQ.initialControl WeightedBinsGraphQ.initialControl
    WeightedScaleDerivedFromBins.initialControl
    WeightedScaleDerivedFromBins.initialControl
    (WeightedPrefixAT.initialBank i g W)
    (WeightedScaleDerivedFromBins.initialBank S)
    (WeightedPrefixAT.finalBank i g W F Q)
    up ua hLift (by simpa only [WeightedPrefixAT.finalBank] using ha)
  refine ⟨u,?_,v,F,Q,?_,ha54,ht,?_,?_,?_,?_,?_⟩
  · change u ≤ WeightedBinsGraphQ.bound i g (Fintype.card E) +
      WeightedScaleDerivedFromBins.bound i + 1
    have hup' : up ≤ WeightedBinsGraphQ.bound i g (Fintype.card E) := by
      simpa only [g] using hup
    omega
  · simpa only [WeightedPrefixAT.program,
      WeightedPrefixAT.initialControl] using hr
  · exact (hwriter 56 (by decide)).trans hq
  · exact (hwriter 17 (by decide)).trans h17pre
  · exact (hwriter 57 (by decide)).trans h57pre
  · exact (hwriter 28 (by decide)).trans h28pre
  · exact (hwriter 27 (by decide)).trans h27pre

#print axioms source_run_framed

end
end EthInapproximability.CurrentPaper.WeightedPrefixFrame
