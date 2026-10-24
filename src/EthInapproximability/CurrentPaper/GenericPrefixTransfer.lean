import EthInapproximability.CurrentPaper.GenericPrefixTransferFrame

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixTransfer

open Turing BitMachineEncoding BitMachineStackEmbedding
open PrefixCopy PrefixTransferFrame
open scoped Classical

theorem atN_ne_pairN : atN ≠ pairN := by
  simp [atN,pairN,atEmbedding,pairEmbedding]
theorem atSaved_ne_pairSaved : atSaved ≠ pairSaved := by
  simp [atSaved,pairSaved,atEmbedding,pairEmbedding]
theorem atCount_ne_pairCount : atCount ≠ pairCount := by
  simp [atCount,pairCount,atEmbedding,pairEmbedding]
theorem atN_ne_scratch : atN ≠ PrefixCopy.scratch := by
  simp [atN,atEmbedding,PrefixCopy.scratch]
theorem atSaved_ne_scratch : atSaved ≠ PrefixCopy.scratch := by
  simp [atSaved,atEmbedding,PrefixCopy.scratch]
theorem atCount_ne_scratch : atCount ≠ PrefixCopy.scratch := by
  simp [atCount,atEmbedding,PrefixCopy.scratch]
theorem pairN_ne_scratch : pairN ≠ PrefixCopy.scratch := by
  simp [pairN,pairEmbedding,PrefixCopy.scratch]
theorem pairSaved_ne_scratch : pairSaved ≠ PrefixCopy.scratch := by
  simp [pairSaved,pairEmbedding,PrefixCopy.scratch]
theorem pairCount_ne_scratch : pairCount ≠ PrefixCopy.scratch := by
  simp [pairCount,pairEmbedding,PrefixCopy.scratch]

noncomputable def nProgram :=
  PrefixCopy.copyProgram atN pairN
    atN_ne_pairN atN_ne_scratch pairN_ne_scratch
noncomputable def savedProgram :=
  PrefixCopy.copyProgram atSaved pairSaved
    atSaved_ne_pairSaved atSaved_ne_scratch pairSaved_ne_scratch
noncomputable def countProgram :=
  PrefixCopy.copyProgram atCount pairCount
    atCount_ne_pairCount atCount_ne_scratch pairCount_ne_scratch

noncomputable def phase1 :=
  BitMachineRawSequence.program nProgram savedProgram
    BitMachineCopy.Label.scan none none
noncomputable def program :=
  BitMachineRawSequence.program phase1 countProgram
    BitMachineCopy.Label.scan (none,none) none

theorem run (B : SourceBooleanPrefix.PrefixLoopMachine.Stack → List Bool)
    (n : Nat) (saved count : List Bool)
    (hn : B SourceBooleanPrefix.PrefixLoopMachine.source =
      List.replicate n true)
    (hs : B (.inl (.inl 2)) = saved)
    (hc : B (.inl (.inl 4)) = count) :
    ∃ T ≤ 2*(n+saved.length+count.length)+8,
      ((advance program)^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,none),none),framedAt B⟩ :
          TM2.Cfg (fun _ : PrefixCopy.Stack => Bool) _ _) =
        ⟨none,((none,none),none),paired B n saved count⟩ := by
  let B0 := framedAt B
  let B1 := Function.update B0 pairN (List.replicate n true)
  let B2 := Function.update B1 pairSaved saved
  let B3 := paired B n saved count
  have hsrcN : B0 atN = List.replicate n true := by
    change framedAt B (atEmbedding SourceBooleanPrefix.PrefixLoopMachine.source) = _
    rw [framed_at]
    exact hn
  have hdstN : B0 pairN = [] :=
    framed_pair_empty B SourceBooleanPrefix.PairVertexLoopMachine.source
  have hw0 : B0 PrefixCopy.scratch = [] := framed_scratch_empty B
  have hsrcS : B1 atSaved = saved := by
    have hne : atSaved ≠ pairN := by
      simp [atSaved,pairN,atEmbedding,pairEmbedding]
    simp only [B1,Function.update_of_ne hne]
    change framedAt B (atEmbedding (.inl (.inl 2))) = _
    rw [framed_at]
    exact hs
  have hdstS : B1 pairSaved = [] := by
    have hne : pairSaved ≠ pairN := by
      simp [pairSaved,pairN,pairEmbedding,
        SourceBooleanPrefix.PairVertexLoopMachine.source]
    simp only [B1,Function.update_of_ne hne]
    exact framed_pair_empty B (.inl (.inl (.inl 2)))
  have hw1 : B1 PrefixCopy.scratch = [] := by
    simp only [B1,Function.update_of_ne (Ne.symm pairN_ne_scratch)]
    exact hw0
  have hsrcC : B2 atCount = count := by
    have hneS : atCount ≠ pairSaved := by
      simp [atCount,pairSaved,atEmbedding,pairEmbedding]
    have hneN : atCount ≠ pairN := by
      simp [atCount,pairN,atEmbedding,pairEmbedding]
    simp only [B2,Function.update_of_ne hneS,
      B1,Function.update_of_ne hneN]
    change framedAt B (atEmbedding (.inl (.inl 4))) = _
    rw [framed_at]
    exact hc
  have hdstC : B2 pairCount = [] := by
    have hneS : pairCount ≠ pairSaved := by
      simp [pairCount,pairSaved,pairEmbedding]
    have hneN : pairCount ≠ pairN := by
      simp [pairCount,pairN,pairEmbedding,
        SourceBooleanPrefix.PairVertexLoopMachine.source]
    simp only [B2,Function.update_of_ne hneS,
      B1,Function.update_of_ne hneN]
    exact framed_pair_empty B (.inl (.inl (.inl 4)))
  have hw2 : B2 PrefixCopy.scratch = [] := by
    simp only [B2,Function.update_of_ne (Ne.symm pairSaved_ne_scratch)]
    exact hw1
  have hN := PrefixCopy.copy_run atN pairN
    atN_ne_pairN atN_ne_scratch pairN_ne_scratch
    B0 (List.replicate n true) hsrcN hdstN hw0
  have hS := PrefixCopy.copy_run atSaved pairSaved
    atSaved_ne_pairSaved atSaved_ne_scratch pairSaved_ne_scratch
    B1 saved hsrcS hdstS hw1
  have hC := PrefixCopy.copy_run atCount pairCount
    atCount_ne_pairCount atCount_ne_scratch pairCount_ne_scratch
    B2 count hsrcC hdstC hw2
  have hN' : ((advance nProgram)^[2*n+2])
      (⟨some .scan,none,B0⟩ :
        TM2.Cfg (fun _ : PrefixCopy.Stack => Bool) _ _) =
      ⟨none,none,B1⟩ := by
    simpa only [nProgram,B1,List.length_replicate] using hN
  obtain ⟨t1,ht1,hr1⟩ := BitMachineRawSequence.runs
    nProgram savedProgram BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none B0 B1 B2
    (2*n+2) (2*saved.length+2) hN' hS
  obtain ⟨T,hT,hr⟩ := BitMachineRawSequence.runs
    phase1 countProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan
    (none,none) (none,none) none none
    B0 B2 B3 t1 (2*count.length+2) hr1 hC
  refine ⟨T,by omega,?_⟩
  simpa only [program,B0,B3] using hr

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixTransfer
