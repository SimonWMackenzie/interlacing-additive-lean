import EthInapproximability.CurrentPaper.WeightedPrefixFrame
import EthInapproximability.CurrentPaper.WeightedScalarComplete

/-! The original single-controller weighted scalar run with the physically
produced bin and incoming-column words retained in its endpoint. -/

namespace EthInapproximability.CurrentPaper.WeightedScalarFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
open WeightedScalarComplete
noncomputable section

theorem source_run_framed {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (i : Parameters.Input)
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : Fin 64 → List Bool) (rx : ℕ)
    (hrx : W 17 = List.replicate rx true)
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let g := EncodedETHSource.serializeGraph G
    let q := ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)
    ∃ u ≤ WeightedScalarComplete.bound i g (Fintype.card E) rx q,
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
      ∃ Q : WeightedGraphQJoined.Stack → List Bool,
      ∃ P : ChosenPrimeRaw.Stack → List Bool,
        ((advance WeightedScalarComplete.program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  BinsWriterAssembly.binStart)))),
            WeightedScalarComplete.initialControl,
            WeightedScalarComplete.initialBank i g W⟩ :
            TM2.Cfg (fun _ : WeightedScalarComplete.Stack => Bool) _ _) =
          ⟨none,WeightedScalarComplete.initialControl,
            WeightedScalarComplete.finalBank i g W F Q P rx q⟩ ∧
        (WeightedScalarComplete.finalBank i g W F Q P rx q)
          (WeightedScalarComplete.writer 54) =
          List.replicate (Parameters.firstExponent i) true ∧
        (WeightedScalarComplete.finalBank i g W F Q P rx q)
          (WeightedScalarComplete.writer 56) = List.replicate q true ∧
        (WeightedScalarComplete.finalBank i g W F Q P rx q)
          (WeightedScalarComplete.writer 57) =
          List.replicate
            (PrimeSampler.size q (Parameters.balanceOrder i)
              (Construction.qOne (Parameters.firstExponent i) * rx)) true ∧
        (WeightedScalarComplete.finalBank i g W F Q P rx q)
          (WeightedScalarComplete.writer 17) =
          List.replicate rx true ∧
        (WeightedScalarComplete.finalBank i g W F Q P rx q)
          (WeightedScalarComplete.writer 28) =
          List.replicate (Parameters.bins i) true ∧
        (WeightedScalarComplete.finalBank i g W F Q P rx q)
          (WeightedScalarComplete.writer 27) = W 27 := by
  let g := EncodedETHSource.serializeGraph G
  let q := ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)
  obtain ⟨up,hup,v,F,Q,hprefix,ha,ht,hq,h17,h57pre,h28pre,h27pre⟩ :=
    WeightedPrefixFrame.source_run_framed i G W h28 h61
      h7 h8 h9 h10 h11 h12 h13 h14 h15 h18
      h54 h55 h56 h57 h58 h60
  let S := WeightedPrefixAT.finalBank i g W F Q
  have hrxS : S (WeightedPrefixAT.writer 17) =
      List.replicate rx true := h17.trans hrx
  have h57S : S (WeightedPrefixAT.writer 57) = [] :=
    h57pre.trans h57
  obtain ⟨uz,huz,P,hsize,hwriter⟩ :=
    WeightedActualSizeSuffix.run S
      (Parameters.firstExponent i) rx q (Parameters.balanceOrder i)
      ha hrxS hq ht h57S
  have hLift :
      ((advance WeightedScalarComplete.prefixProgram)^[up])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart))),
          WeightedPrefixAT.initialControl,
          WeightedScalarComplete.initialBank i g W⟩ :
          TM2.Cfg (fun _ : WeightedScalarComplete.Stack => Bool) _ _) =
        ⟨none,WeightedPrefixAT.initialControl,
          WeightedScalarComplete.afterPrefix i g W F Q⟩ := by
    have he := BitMachineStackRun.run WeightedScalarComplete.prefixSlots
      (WeightedScalarComplete.initialBank i g W)
      WeightedPrefixAT.program
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart))),
        WeightedPrefixAT.initialControl,
        WeightedPrefixAT.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedPrefixAT.Stack => Bool) _ _) up
    rw [hprefix] at he
    have hi : bank WeightedScalarComplete.prefixSlots
        (WeightedScalarComplete.initialBank i g W)
        (WeightedPrefixAT.initialBank i g W) =
        WeightedScalarComplete.initialBank i g W := by
      apply bank_eq_self
      intro j
      rfl
    have ho : bank WeightedScalarComplete.prefixSlots
        (WeightedScalarComplete.initialBank i g W)
        (WeightedPrefixAT.finalBank i g W F Q) =
        WeightedScalarComplete.afterPrefix i g W F Q := by
      funext j
      cases j with
      | inl j =>
          cases j with
          | inl j => exact bank_at WeightedScalarComplete.prefixSlots _ _ j
          | inr j =>
              rw [bank_outside]
              · rfl
              · rintro ⟨k,h⟩; cases h
      | inr j =>
          rw [bank_outside]
          · rfl
          · rintro ⟨k,h⟩; cases h
    simpa only [WeightedScalarComplete.prefixProgram,stackCfg,hi,ho,g]
      using he
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    WeightedScalarComplete.prefixProgram WeightedActualSizeSuffix.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (Sum.inr false)))))))
    WeightedPrefixAT.initialControl WeightedPrefixAT.initialControl
    WeightedActualSizeSuffix.initialControl
    WeightedActualSizeSuffix.initialControl
    (WeightedScalarComplete.initialBank i g W)
    (WeightedScalarComplete.afterPrefix i g W F Q)
    (WeightedScalarComplete.finalBank i g W F Q P rx q)
    up uz hLift (by simpa only [WeightedScalarComplete.finalBank,S]
      using hsize)
  refine ⟨u,?_,v,F,Q,P,?_,?_,?_,?_,?_,?_,?_⟩
  · change u ≤ WeightedPrefixAT.bound i g (Fintype.card E) +
      WeightedActualSizeSuffix.bound (Parameters.firstExponent i) rx q
        (Parameters.balanceOrder i) + 1
    have hup' : up ≤ WeightedPrefixAT.bound i g (Fintype.card E) := by
      simpa only [g] using hup
    omega
  · simpa only [WeightedScalarComplete.program,
      WeightedScalarComplete.initialControl] using hr
  · have hw := hwriter 54
    simpa [Function.update_of_ne (by decide : (54 : Fin 64) ≠ 57)]
      using hw.trans ha
  · have hw := hwriter 56
    simpa [Function.update_of_ne (by decide : (56 : Fin 64) ≠ 57)]
      using hw.trans hq
  · have hw := hwriter 57
    simpa using hw
  · have hw := hwriter 17
    simpa [Function.update_of_ne (by decide : (17 : Fin 64) ≠ 57)]
      using hw.trans hrxS
  · have hw := hwriter 28
    simpa [Function.update_of_ne (by decide : (28 : Fin 64) ≠ 57)]
      using hw.trans h28pre
  · have hw := hwriter 27
    simpa [Function.update_of_ne (by decide : (27 : Fin 64) ≠ 57)]
      using hw.trans h27pre

#print axioms source_run_framed

end
end EthInapproximability.CurrentPaper.WeightedScalarFrame
