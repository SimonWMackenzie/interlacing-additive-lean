import EthInapproximability.CurrentPaper.WeightedRawRowsFrame
import EthInapproximability.CurrentPaper.WeightedScalarFromRawDimensions

/-! Same fixed raw-column, raw-row, scalar controller as the frozen dimension
checkpoint, now exposing the source-faithful bins and cy writer cells. -/

namespace EthInapproximability.CurrentPaper.WeightedRawDimensionsFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

theorem source_run_framed {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (i : Parameters.Input)
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : Fin 64 → List Bool)
    (h17 : W 17 = []) (h62 : W 62 = [])
    (h27 : W 27 = []) (h63 : W 63 = [])
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let g := EncodedETHSource.serializeGraph G
    let q := ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)
    let W' := Function.update W 27 (List.replicate i.columns true)
    let W'' := Function.update W' 17 (List.replicate i.rows true)
    ∃ u ≤ WeightedScalarFromRawDimensions.bound i g (Fintype.card E) q,
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
      ∃ Q : WeightedGraphQJoined.Stack → List Bool,
      ∃ P : ChosenPrimeRaw.Stack → List Bool,
        ((advance WeightedScalarFromRawDimensions.program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
            WeightedScalarFromRawDimensions.initialControl,
            WeightedScalarFromRawDimensions.initialBank i g W⟩ :
            TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _) =
          ⟨none,WeightedScalarFromRawDimensions.initialControl,
            WeightedScalarComplete.finalBank i g W'' F Q P i.rows q⟩ ∧
        (WeightedScalarComplete.finalBank i g W'' F Q P i.rows q)
          (WeightedScalarComplete.writer 17) =
            List.replicate i.rows true ∧
        (WeightedScalarComplete.finalBank i g W'' F Q P i.rows q)
          (WeightedScalarComplete.writer 27) =
            List.replicate i.columns true ∧
        (WeightedScalarComplete.finalBank i g W'' F Q P i.rows q)
          (WeightedScalarComplete.writer 28) =
            List.replicate (Parameters.bins i) true ∧
        (WeightedScalarComplete.finalBank i g W'' F Q P i.rows q)
          (WeightedScalarComplete.writer 54) =
            List.replicate (Parameters.firstExponent i) true ∧
        (WeightedScalarComplete.finalBank i g W'' F Q P i.rows q)
          (WeightedScalarComplete.writer 56) = List.replicate q true ∧
        (WeightedScalarComplete.finalBank i g W'' F Q P i.rows q)
          (WeightedScalarComplete.writer 57) =
            List.replicate
              (PrimeSampler.size q (Parameters.balanceOrder i)
                (Construction.qOne (Parameters.firstExponent i) * i.rows)) true := by
  let g := EncodedETHSource.serializeGraph G
  let q := ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)
  let W' := Function.update W 27 (List.replicate i.columns true)
  let W'' := Function.update W' 17 (List.replicate i.rows true)
  have hother (k : Fin 64) (hk : k ≠ 27) : W' k = W k := by
    simp [W',Function.update_of_ne hk]
  have hcopy := WeightedRawColumnsSource.copy_run i g W h27 h63
  have hbank : WeightedRawColumnsSource.finalBank i g W =
      WeightedScalarFromRawRows.initialBank i g W' := by
    simpa only [WeightedRawColumnsSource.finalBank,
      WeightedScalarFromRawRows.initialBank,W'] using
      (WeightedRawColumnsSource.initial_update_writer i g W
        (List.replicate i.columns true)).symm
  obtain ⟨us,hus,v,F,Q,P,hs,hrx,ha,hq,hL,hbin,hcol⟩ :=
    WeightedRawRowsFrame.source_run_framed i G W'
      ((hother 17 (by decide)).trans h17)
      ((hother 62 (by decide)).trans h62)
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
  have hscalar : ((advance WeightedScalarFromRawRows.program)^[us])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawRows.initialControl,
        WeightedRawColumnsSource.finalBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedRawColumnsSource.Stack => Bool) _ _) =
      ⟨none,WeightedScalarFromRawRows.initialControl,
        WeightedScalarComplete.finalBank i g W'' F Q P i.rows q⟩ := by
    simpa only [hbank,W'',g,q] using hs
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    WeightedRawColumnsSource.program WeightedScalarFromRawRows.program
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none : Option Bool) (none : Option Bool)
    WeightedScalarFromRawRows.initialControl
    WeightedScalarFromRawRows.initialControl
    (WeightedRawColumnsSource.initialBank i g W)
    (WeightedRawColumnsSource.finalBank i g W)
    (WeightedScalarComplete.finalBank i g W'' F Q P i.rows q)
    (2*i.columns+2) us hcopy hscalar
  refine ⟨u,?_,v,F,Q,P,?_,?_,?_,?_,?_,?_,?_⟩
  · change u ≤ (2*i.columns+2) +
      WeightedScalarFromRawRows.bound i g (Fintype.card E) q + 1
    have hus' : us ≤ WeightedScalarFromRawRows.bound i g
        (Fintype.card E) q := by simpa only [g,q] using hus
    omega
  · simpa only [WeightedScalarFromRawDimensions.program,
      WeightedScalarFromRawDimensions.initialControl,
      WeightedScalarFromRawDimensions.initialBank,W',W'',g,q] using hr
  · simpa only [W',W'',g,q] using hrx
  · simpa only [W',W'',g,q] using hcol
  · simpa only [W',W'',g,q] using hbin
  · simpa only [W',W'',g,q] using ha
  · simpa only [W',W'',g,q] using hq
  · simpa only [W',W'',g,q] using hL

#print axioms source_run_framed

end
end EthInapproximability.CurrentPaper.WeightedRawDimensionsFrame
