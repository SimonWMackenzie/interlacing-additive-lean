import EthInapproximability.CurrentPaper.WeightedScalarFrame
import EthInapproximability.CurrentPaper.WeightedScalarFromRawRows

/-! Physical raw row-count copy followed by the same framed scalar run. -/

namespace EthInapproximability.CurrentPaper.WeightedRawRowsFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

theorem source_run_framed {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (i : Parameters.Input)
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : Fin 64 → List Bool)
    (h17 : W 17 = []) (h62 : W 62 = [])
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let g := EncodedETHSource.serializeGraph G
    let q := ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)
    let W' := Function.update W 17 (List.replicate i.rows true)
    ∃ u ≤ WeightedScalarFromRawRows.bound i g (Fintype.card E) q,
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
      ∃ Q : WeightedGraphQJoined.Stack → List Bool,
      ∃ P : ChosenPrimeRaw.Stack → List Bool,
        ((advance WeightedScalarFromRawRows.program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
            WeightedScalarFromRawRows.initialControl,
            WeightedScalarFromRawRows.initialBank i g W⟩ :
            TM2.Cfg (fun _ : WeightedScalarFromRawRows.Stack => Bool) _ _) =
          ⟨none,WeightedScalarFromRawRows.initialControl,
            WeightedScalarComplete.finalBank i g W' F Q P i.rows q⟩ ∧
        (WeightedScalarComplete.finalBank i g W' F Q P i.rows q)
          (WeightedScalarComplete.writer 17) =
            List.replicate i.rows true ∧
        (WeightedScalarComplete.finalBank i g W' F Q P i.rows q)
          (WeightedScalarComplete.writer 54) =
            List.replicate (Parameters.firstExponent i) true ∧
        (WeightedScalarComplete.finalBank i g W' F Q P i.rows q)
          (WeightedScalarComplete.writer 56) = List.replicate q true ∧
        (WeightedScalarComplete.finalBank i g W' F Q P i.rows q)
          (WeightedScalarComplete.writer 57) =
            List.replicate
              (PrimeSampler.size q (Parameters.balanceOrder i)
                (Construction.qOne (Parameters.firstExponent i) * i.rows)) true ∧
        (WeightedScalarComplete.finalBank i g W' F Q P i.rows q)
          (WeightedScalarComplete.writer 28) =
            List.replicate (Parameters.bins i) true ∧
        (WeightedScalarComplete.finalBank i g W' F Q P i.rows q)
          (WeightedScalarComplete.writer 27) = W 27 := by
  let g := EncodedETHSource.serializeGraph G
  let q := ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)
  let W' := Function.update W 17 (List.replicate i.rows true)
  have hw17 : W' 17 = List.replicate i.rows true := by
    simp [W']
  have hother (k : Fin 64) (hk : k ≠ 17) : W' k = W k := by
    simp [W',Function.update_of_ne hk]
  have hcopy := WeightedRawRowsSource.copy_run i g W h17 h62
  have hbank : WeightedRawRowsSource.finalBank i g W =
      WeightedScalarComplete.initialBank i g W' := by
    simpa only [WeightedRawRowsSource.finalBank,
      WeightedRawRowsSource.initialBank,W'] using
      (WeightedRawRowsSource.initial_update_writer i g W
        (List.replicate i.rows true)).symm
  obtain ⟨us,hus,v,F,Q,P,hs,ha,hq,hL,hrx,hbin,hcol⟩ :=
    WeightedScalarFrame.source_run_framed i G W' i.rows hw17
      ((hother 28 (by decide)).trans h28)
      ((hother 61 (by decide)).trans h61)
      ((hother 7 (by decide)).trans h7)
      ((hother 8 (by decide)).trans h8)
      ((hother 9 (by decide)).trans h9)
      ((hother 10 (by decide)).trans h10)
      ((hother 11 (by decide)).trans h11)
      ((hother 12 (by decide)).trans h12)
      ((hother 13 (by decide)).trans h13)
      ((hother 14 (by decide)).trans h14)
      ((hother 15 (by decide)).trans h15)
      ((hother 18 (by decide)).trans h18)
      ((hother 54 (by decide)).trans h54)
      ((hother 55 (by decide)).trans h55)
      ((hother 56 (by decide)).trans h56)
      ((hother 57 (by decide)).trans h57)
      ((hother 58 (by decide)).trans h58)
      ((hother 60 (by decide)).trans h60)
  have hscalar : ((advance WeightedScalarComplete.program)^[us])
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              BinsWriterAssembly.binStart)))),
        WeightedScalarComplete.initialControl,
        WeightedRawRowsSource.finalBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedRawRowsSource.Stack => Bool) _ _) =
      ⟨none,WeightedScalarComplete.initialControl,
        WeightedScalarComplete.finalBank i g W' F Q P i.rows q⟩ := by
    simpa only [hbank,g,q] using hs
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    WeightedRawRowsSource.program WeightedScalarComplete.program
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            BinsWriterAssembly.binStart))))
    (none : Option Bool) (none : Option Bool)
    WeightedScalarComplete.initialControl WeightedScalarComplete.initialControl
    (WeightedRawRowsSource.initialBank i g W)
    (WeightedRawRowsSource.finalBank i g W)
    (WeightedScalarComplete.finalBank i g W' F Q P i.rows q)
    (2*i.rows+2) us hcopy hscalar
  refine ⟨u,?_,v,F,Q,P,?_,?_,?_,?_,?_,?_,?_⟩
  · change u ≤ (2*i.rows+2) +
      WeightedScalarComplete.bound i g (Fintype.card E) i.rows q + 1
    have hus' : us ≤ WeightedScalarComplete.bound i g
        (Fintype.card E) i.rows q := by simpa only [g,q] using hus
    omega
  · simpa only [WeightedScalarFromRawRows.program,
      WeightedScalarFromRawRows.initialControl,
      WeightedScalarFromRawRows.initialBank,W',g,q] using hr
  · simpa only [W',g,q] using hrx
  · simpa only [W',g,q] using ha
  · simpa only [W',g,q] using hq
  · simpa only [W',g,q] using hL
  · simpa only [W',g,q] using hbin
  · simpa only [W',g,q] using hcol.trans (hother 27 (by decide))

#print axioms source_run_framed

end
end EthInapproximability.CurrentPaper.WeightedRawRowsFrame
