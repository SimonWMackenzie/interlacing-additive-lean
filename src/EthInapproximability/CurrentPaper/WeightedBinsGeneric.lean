import EthInapproximability.CurrentPaper.BinsWriterAssembly

/-! The actual raw-six scale/bin producer installs bins at writer28 while
preserving an otherwise arbitrary weighted writer. The frozen later column
staging is deliberately not entered here: graph/order must run first. -/

namespace EthInapproximability.CurrentPaper.WeightedBinsGeneric

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := BinsWriterAssembly.Stack
def paramSlots := BinsWriterAssembly.paramSlots
def writer (k : Fin 64) : Stack := .inr k
def foreignBank (W : Fin 64 → List Bool) : Stack → List Bool :=
  Sum.elim (fun _ => []) W
def initialBank (i : Parameters.Input) (W : Fin 64 → List Bool) :
    Stack → List Bool :=
  bank paramSlots (foreignBank W) (ETHBinsJoinedScratch.initialBank i)
def afterBins (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool) : Stack → List Bool :=
  bank paramSlots (foreignBank W) F
def finalBank (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool) (i : Parameters.Input) :
    Stack → List Bool :=
  Function.update (afterBins W F) (writer 28)
    (List.replicate (Parameters.bins i) true)
def program := BitMachineRawSequence.program
  BinsWriterAssembly.binProgram BinsWriterAssembly.copyProgram
  BitMachineCopy.Label.scan BinsWriterAssembly.binControl
  (none : Option Bool)
def initialControl := (BinsWriterAssembly.binControl,(none : Option Bool))
def bound (i : Parameters.Input) : ℕ :=
  ETHBinsJoinedScratch.totalBound i + (2*Parameters.bins i+2)+1

theorem run (i : Parameters.Input) (W : Fin 64 → List Bool)
    (h28 : W 28 = []) (h61 : W 61 = []) :
    ∃ u ≤ bound i,
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            BinsWriterAssembly.binStart),initialControl,initialBank i W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,finalBank W F i⟩ ∧
        F (.inr ETHBinsSourcePreservingScratch.outputKey) =
          List.replicate (Parameters.bins i) true ∧
        F (.inl (.inr ScaleFinalScratch.answerKey)) =
          List.replicate (Parameters.scale i) true ∧
        (∀ k : Fin 64,
          finalBank W F i (writer k) =
            Function.update W 28
              (List.replicate (Parameters.bins i) true) k) := by
  obtain ⟨ub,hub,v,F,hb,hbin,hscale,_⟩ :=
    ETHBinsJoinedScratch.actual_bins_run i
  let S := afterBins W F
  have hBin :
      ((advance BinsWriterAssembly.binProgram)^[ub])
        (⟨some BinsWriterAssembly.binStart,
          BinsWriterAssembly.binControl,initialBank i W⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,(ETHBinsJoinedScratch.scaleControl,(none,v)),S⟩ := by
    have he := BitMachineStackRun.run paramSlots (foreignBank W)
      ETHBinsJoinedScratch.program
      (⟨some BinsWriterAssembly.binStart,
        BinsWriterAssembly.binControl,
        ETHBinsJoinedScratch.initialBank i⟩ :
        TM2.Cfg (fun _ : ETHBinsJoinedScratch.Stack => Bool) _ _) ub
    have hb0 :
        ((advance ETHBinsJoinedScratch.program)^[ub])
          (⟨some BinsWriterAssembly.binStart,
            BinsWriterAssembly.binControl,
            ETHBinsJoinedScratch.initialBank i⟩ :
              TM2.Cfg (fun _ : ETHBinsJoinedScratch.Stack => Bool) _ _) =
          ⟨none,(ETHBinsJoinedScratch.scaleControl,(none,v)),F⟩ := by
      simpa only [BinsWriterAssembly.binStart,
        BinsWriterAssembly.binControl] using hb
    rw [hb0] at he
    simpa only [BinsWriterAssembly.binProgram,initialBank,afterBins,S,
      stackCfg] using he
  have hs : S (BinsWriterAssembly.copySlots 0) =
      List.replicate (Parameters.bins i) true := by
    change bank paramSlots (foreignBank W) F
      (paramSlots (.inr ETHBinsSourcePreservingScratch.outputKey)) = _
    rw [bank_at]
    exact hbin
  have hd : S (BinsWriterAssembly.copySlots 1) = [] := by
    have hout : ¬ ∃ j : ETHBinsJoinedScratch.Stack,
        paramSlots j = BinsWriterAssembly.copySlots 1 := by
      rintro ⟨j,h⟩; cases h
    change bank paramSlots (foreignBank W) F
      (BinsWriterAssembly.copySlots 1) = []
    rw [bank_outside _ _ _ _ hout]
    exact h28
  have hc : S (BinsWriterAssembly.copySlots 2) = [] := by
    have hout : ¬ ∃ j : ETHBinsJoinedScratch.Stack,
        paramSlots j = BinsWriterAssembly.copySlots 2 := by
      rintro ⟨j,h⟩; cases h
    change bank paramSlots (foreignBank W) F
      (BinsWriterAssembly.copySlots 2) = []
    rw [bank_outside _ _ _ _ hout]
    exact h61
  have hcopy := MatrixStage4ScalarPreparationOps.copy_run
    BinsWriterAssembly.copySlots S hc
  have hCopy :
      ((advance BinsWriterAssembly.copyProgram)^[2*Parameters.bins i+2])
        (⟨some BitMachineCopy.Label.scan,none,S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,none,finalBank W F i⟩ := by
    rw [hs,hd] at hcopy
    simpa only [BinsWriterAssembly.copyProgram,finalBank,
      BinsWriterAssembly.copySlots,List.length_replicate,
      List.append_nil,writer,S] using hcopy
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    BinsWriterAssembly.binProgram BinsWriterAssembly.copyProgram
    BinsWriterAssembly.binStart BitMachineCopy.Label.scan
    BinsWriterAssembly.binControl
    (ETHBinsJoinedScratch.scaleControl,(none,v))
    (none : Option Bool) none
    (initialBank i W) S (finalBank W F i)
    ub (2*Parameters.bins i+2) hBin hCopy
  refine ⟨u,by dsimp [bound]; omega,v,F,?_,hbin,hscale,?_⟩
  · simpa only [program,initialControl] using hr
  · intro k
    by_cases hk : k = 28
    · subst k
      simp [finalBank,writer]
    · have hout : ¬ ∃ j : ETHBinsJoinedScratch.Stack,
          paramSlots j = (writer k : Stack) := by
        rintro ⟨j,h⟩; cases h
      have hn : writer k ≠ writer 28 := by simpa [writer] using hk
      rw [finalBank,Function.update_of_ne hn,
        afterBins,bank_outside _ _ _ _ hout]
      simp [foreignBank,writer,Function.update_of_ne hk]

#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedBinsGeneric
