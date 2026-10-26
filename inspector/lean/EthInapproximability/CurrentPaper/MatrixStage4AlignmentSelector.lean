import EthInapproximability.CurrentPaper.MatrixStage4OrdinalCopyAlignment

/-!
# Physical selector reference retained by the alignment decoder

The variable-bin alignment machine computes a unary reference selector and
preserves it through comparisons. This owner strengthens the existing
alignment-run interface to expose that literal output bank, then transports
it through raw-column splitting and the charged ordinal copy.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4AlignmentSelector

open Turing BitMachineEncoding BitMachineComposition
open MatrixStage4Codes MatrixStage4Digits MatrixStage4AlignmentDigits
open Construction

theorem align_after_low_selector (c : MatrixStage4LowDigitStream.Config)
    (bound q : ℕ) (ps : List ℕ)
    (hhalt : (MatrixStage4LowDigitStream.run bound c).l = none)
    (hstream : (MatrixStage4LowDigitStream.run bound c).stk 11 =
      MatrixStage4AlignmentStream.words ps)
    (href : (MatrixStage4LowDigitStream.run bound c).stk 9 =
      List.replicate q true)
    (hscratch : (MatrixStage4LowDigitStream.run bound c).stk 12 = []) :
    ∃ t ≤ bound + MatrixStage4AlignmentStream.budget ps q + 2,
      (MatrixStage4AlignmentFull.run t
        (MatrixStage4AlignmentFull.lowFrame c)).l = none ∧
      (MatrixStage4AlignmentFull.run t
        (MatrixStage4AlignmentFull.lowFrame c)).var.2.1 =
        ps.all (fun p => decide (p=q)) ∧
      (MatrixStage4AlignmentFull.run t
        (MatrixStage4AlignmentFull.lowFrame c)).stk 9 =
        List.replicate q true := by
  let d := MatrixStage4LowDigitStream.run bound c
  let bank := MatrixStage4AlignmentFull.alignForeign
    (MatrixStage4AlignmentFull.lowFrame d)
  obtain ⟨t₁,ht₁,h₁⟩ := MatrixStage4AlignmentFull.low_phase c bound hhalt
  have hb : MatrixStage4AlignmentFull.lowFrame d =
      MatrixStage4AlignmentFull.alignFrame bank d.var
        (MatrixStage4AlignmentStream.cfg (some .start)
          MatrixStage4AlignmentStream.initial
          (MatrixStage4AlignmentStream.words ps)
          (List.replicate q true) []) := by
    simpa only [d,bank,hstream,href,hscratch] using
      MatrixStage4AlignmentFull.bridge d hhalt
  obtain ⟨ta,hta,ha⟩ := MatrixStage4AlignmentStream.words_halt ps q
  have hahalt : (MatrixStage4AlignmentStream.run ta
      (MatrixStage4AlignmentStream.cfg (some .start)
        MatrixStage4AlignmentStream.initial
        (MatrixStage4AlignmentStream.words ps)
        (List.replicate q true) [])).l = none := by
    rw [ha]
    rfl
  obtain ⟨t₂,ht₂,h₂⟩ := MatrixStage4AlignmentFull.align_phase bank d.var
    (MatrixStage4AlignmentStream.cfg (some .start)
      MatrixStage4AlignmentStream.initial
      (MatrixStage4AlignmentStream.words ps)
      (List.replicate q true) []) ta hahalt
  rw [ha] at h₂
  let terminal := MatrixStage4AlignmentFull.alignFrame bank d.var
    (MatrixStage4AlignmentStream.cfg none
      (ps.all (fun p => decide (p=q)),none,none)
      [] (List.replicate q true) [])
  have hd : MatrixStage4AlignmentFull.run 1 terminal =
      ⟨none,terminal.var,terminal.stk⟩ := by
    change MatrixStage4AlignmentFull.run 1
      (⟨some MatrixStage4AlignmentFull.done,terminal.var,terminal.stk⟩ :
        MatrixStage4AlignmentFull.Config) = _
    exact MatrixStage4AlignmentFull.done_run terminal.var terminal.stk
  have h12 := MatrixStage4AlignmentFull.run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := MatrixStage4AlignmentFull.run_add h12 1
  rw [hd] at h123
  refine ⟨t₁+t₂+1,by omega,?_,?_,?_⟩
  · rw [h123]
  · rw [h123]
    rfl
  · rw [h123]
    rfl

theorem raw_bin_alignment_selector {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    let base := binBase a s q cy
    let wordSize := wordBase a s cy
    let n := code.val % base^s
    let reference := selectorDigit code (firstBin s hs)
    let c := MatrixStage4LowDigitStream.loopCfg
      (some MatrixStage4LowDigitStream.firstStart) (false,none)
      (List.replicate n true) [] [] [] []
      (List.replicate (s-1) true)
      (List.replicate base true) (List.replicate wordSize true)
    ∃ t ≤ MatrixStage4LowDigitStream.timeBudget n base wordSize (s-1)+
      MatrixStage4AlignmentStream.budget
        (MatrixStage4AlignmentCorrect.selectorWords code) reference+2,
      (MatrixStage4AlignmentFull.run t
        (MatrixStage4AlignmentFull.lowFrame c)).l = none ∧
      ((MatrixStage4AlignmentFull.run t
        (MatrixStage4AlignmentFull.lowFrame c)).var.2.1 = true ↔
        aligned hs ((rawColumnCode a s q cy).symm code)) ∧
      (MatrixStage4AlignmentFull.run t
        (MatrixStage4AlignmentFull.lowFrame c)).stk 9 =
        List.replicate reference true := by
  dsimp
  obtain ⟨tb,htb,hhalt,hscratch,href,hstream⟩ :=
    MatrixStage4LowDigitStream.raw_bin_stream_run hs code
  let base := binBase a s q cy
  let wordSize := wordBase a s cy
  let n := code.val % base^s
  let c := MatrixStage4LowDigitStream.loopCfg
    (some MatrixStage4LowDigitStream.firstStart) (false,none)
    (List.replicate n true) [] [] [] []
    (List.replicate (s-1) true)
    (List.replicate base true) (List.replicate wordSize true)
  obtain ⟨t,ht,he,hbit,hselector⟩ := align_after_low_selector c tb
    (selectorDigit code (firstBin s hs))
    (MatrixStage4AlignmentCorrect.selectorWords code)
    hhalt hstream href hscratch
  refine ⟨t,by omega,he,?_,hselector⟩
  rw [hbit]
  exact MatrixStage4AlignmentCorrect.selectorWords_all_iff hs code

theorem raw_ordinal_alignment_selector {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    let base := binBase a s q cy
    let wordSize := wordBase a s cy
    let outer := base^s
    let n := code.val%outer
    let reference := selectorDigit code (firstBin s hs)
    let input := MatrixStage4OrdinalCopyAlignment.alignmentInput code
    ∃ t ≤ MatrixUnaryDivision.totalTime code.val outer+
      MatrixStage4LowDigitStream.timeBudget n base wordSize (s-1)+
      MatrixStage4AlignmentStream.budget
        (MatrixStage4AlignmentCorrect.selectorWords code) reference+3,
      (MatrixStage4AlignmentFromOrdinal.run t input).l = none ∧
      ((MatrixStage4AlignmentFromOrdinal.run t input).var.2.2.1 = true ↔
        aligned hs ((rawColumnCode a s q cy).symm code)) ∧
      (MatrixStage4AlignmentFromOrdinal.run t input).stk 14 =
        List.replicate (code.val/outer) true ∧
      (MatrixStage4AlignmentFromOrdinal.run t input).stk 9 =
        List.replicate reference true := by
  dsimp
  let base := binBase a s q cy
  let wordSize := wordBase a s cy
  let outer := base^s
  let n := code.val%outer
  let splitInput := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate code.val true) (List.replicate outer true)
    [] [] [] []
  let splitOutput := MatrixUnaryDivision.cfg none false
    [] (List.replicate outer true) []
    (List.replicate n true) (List.replicate (code.val/outer) true) []
  have hdiv : MatrixUnaryDivision.run
      (MatrixUnaryDivision.totalTime code.val outer) splitInput =
      splitOutput := MatrixUnaryDivision.division_total_run code.val outer
  obtain ⟨t₁,ht₁,h₁⟩ := MatrixStage4AlignmentFromOrdinal.split_phase
    (List.replicate base true) (List.replicate wordSize true)
    (List.replicate (s-1) true) splitInput
    (MatrixUnaryDivision.totalTime code.val outer)
    (by rw [hdiv]; rfl)
  rw [hdiv] at h₁
  let foreign := MatrixStage4AlignmentFromOrdinal.alignmentForeign
    (MatrixStage4AlignmentFromOrdinal.splitFrame
      (List.replicate base true) (List.replicate wordSize true)
      (List.replicate (s-1) true) splitOutput)
  let lowInput := MatrixStage4LowDigitStream.loopCfg
    (some MatrixStage4LowDigitStream.firstStart) (false,none)
    (List.replicate n true) [] [] [] []
    (List.replicate (s-1) true)
    (List.replicate base true) (List.replicate wordSize true)
  have hb : MatrixStage4AlignmentFromOrdinal.splitFrame
      (List.replicate base true) (List.replicate wordSize true)
      (List.replicate (s-1) true) splitOutput =
      MatrixStage4AlignmentFromOrdinal.alignmentFrame foreign false
        (MatrixStage4AlignmentFull.lowFrame lowInput) := by
    simpa only [splitOutput,foreign,lowInput] using
      MatrixStage4AlignmentFromOrdinal.bridge
        (List.replicate base true) (List.replicate wordSize true)
        (List.replicate (s-1) true) splitOutput (by rfl)
  obtain ⟨ta,hta,haltA,hbitA,hselectorA⟩ :=
    raw_bin_alignment_selector hs code
  have hhalt : (MatrixStage4AlignmentFull.run ta
      (MatrixStage4AlignmentFull.lowFrame lowInput)).l = none := by
    simpa only [lowInput] using haltA
  obtain ⟨t₂,ht₂,h₂⟩ := MatrixStage4AlignmentFromOrdinal.alignment_phase
    foreign false (MatrixStage4AlignmentFull.lowFrame lowInput) ta hhalt
  let terminal := MatrixStage4AlignmentFromOrdinal.alignmentFrame foreign false
    (MatrixStage4AlignmentFull.run ta
      (MatrixStage4AlignmentFull.lowFrame lowInput))
  have hlabel : terminal.l = some MatrixStage4AlignmentFromOrdinal.done := by
    dsimp [terminal,MatrixStage4AlignmentFromOrdinal.alignmentFrame,
      BitMachineEncoding.renameCfg,BitMachineComposition.liftCfg]
    rw [hhalt]
    rfl
  have hd := MatrixStage4AlignmentFromOrdinal.finish terminal hlabel
  have h12 := MatrixStage4AlignmentFromOrdinal.run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := MatrixStage4AlignmentFromOrdinal.run_add h12 1
  rw [hd] at h123
  have hsame : MatrixStage4OrdinalCopyAlignment.alignmentInput code =
      MatrixStage4AlignmentFromOrdinal.splitFrame
        (List.replicate base true) (List.replicate wordSize true)
        (List.replicate (s-1) true) splitInput := by rfl
  refine ⟨t₁+t₂+1,?_,?_,?_,?_,?_⟩
  · dsimp [outer,base,wordSize,n] at ht₁ hta ⊢
    omega
  · rw [hsame,h123]
  · rw [hsame,h123]
    simpa only [terminal,MatrixStage4AlignmentFromOrdinal.alignmentFrame,
      BitMachineEncoding.renameCfg,BitMachineComposition.liftCfg,
      lowInput] using hbitA
  · rw [hsame,h123]
    rfl
  · rw [hsame,h123]
    simpa only [terminal,MatrixStage4AlignmentFromOrdinal.alignmentFrame,
      BitMachineEncoding.renameCfg,BitMachineComposition.liftCfg,
      lowInput] using hselectorA

theorem copy_alignment_selector {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    let base := binBase a s q cy
    let wordSize := wordBase a s cy
    let outer := base^s
    let n := code.val%outer
    let reference := selectorDigit code (firstBin s hs)
    let target := MatrixStage4OrdinalCopyAlignment.alignmentInput code
    let input := MatrixStage4OrdinalCopyAlignment.copyFrame target.var
      (MatrixStage4OrdinalCopyAlignment.copyForeign target)
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate code.val true) [] [])
    ∃ t ≤ (2*code.val+2)+
      (MatrixUnaryDivision.totalTime code.val outer+
        MatrixStage4LowDigitStream.timeBudget n base wordSize (s-1)+
        MatrixStage4AlignmentStream.budget
          (MatrixStage4AlignmentCorrect.selectorWords code) reference+3)+1,
      (MatrixStage4OrdinalCopyAlignment.run t input).l = none ∧
      (MatrixStage4OrdinalCopyAlignment.run t input).stk 19 =
        List.replicate code.val true ∧
      ((MatrixStage4OrdinalCopyAlignment.run t input).var.2.2.2.1 = true ↔
        aligned hs ((rawColumnCode a s q cy).symm code)) ∧
      (MatrixStage4OrdinalCopyAlignment.run t input).stk 14 =
        List.replicate (code.val/outer) true ∧
      (MatrixStage4OrdinalCopyAlignment.run t input).stk 9 =
        List.replicate reference true ∧
      (MatrixStage4OrdinalCopyAlignment.run t input).stk 20 = [] := by
  dsimp
  let target := MatrixStage4OrdinalCopyAlignment.alignmentInput code
  let source := List.replicate code.val true
  let cin := BitMachineCopy.cfg (some .scan) none source [] []
  have hcopy : BitMachineCopy.run (2*code.val+2) cin =
      BitMachineCopy.cfg none none source source [] := by
    simpa only [cin,source,List.length_replicate,List.append_nil]
      using BitMachineCopy.run_correct none source []
  obtain ⟨t₁,ht₁,h₁⟩ := MatrixStage4OrdinalCopyAlignment.copy_phase
    target.var (MatrixStage4OrdinalCopyAlignment.copyForeign target)
    cin (2*code.val+2) (by rw [hcopy]; rfl)
  rw [hcopy] at h₁
  have hb : MatrixStage4OrdinalCopyAlignment.copyFrame target.var
      (MatrixStage4OrdinalCopyAlignment.copyForeign target)
      (BitMachineCopy.cfg none none source source []) =
      MatrixStage4OrdinalCopyAlignment.alignmentFrame none
        (MatrixStage4OrdinalCopyAlignment.originalForeign source) target := by
    apply MatrixStage4OrdinalCopyAlignment.bridge target source
    · rfl
    · have hmap : MatrixStage4AlignmentFromOrdinal.splitStacks.symm
          (15 : Fin 19) = Sum.inl (0 : Fin 6) := by decide
      simp only [target,source,MatrixStage4OrdinalCopyAlignment.alignmentInput,
        MatrixStage4AlignmentFromOrdinal.splitFrame,
        BitMachineEncoding.renameCfg,
        BitMachineComposition.liftCfg,MatrixUnaryDivision.cfg,hmap,
        Sum.elim_inl]
      rfl
  obtain ⟨ta,hta,hal,hflag,hquo,hsel⟩ :=
    raw_ordinal_alignment_selector hs code
  have hhalt : (MatrixStage4AlignmentFromOrdinal.run ta target).l = none := by
    simpa only [target] using hal
  obtain ⟨t₂,ht₂,h₂⟩ := MatrixStage4OrdinalCopyAlignment.alignment_phase
    none (MatrixStage4OrdinalCopyAlignment.originalForeign source)
    target ta hhalt
  let terminal := MatrixStage4OrdinalCopyAlignment.alignmentFrame none
    (MatrixStage4OrdinalCopyAlignment.originalForeign source)
    (MatrixStage4AlignmentFromOrdinal.run ta target)
  have hlabel : terminal.l = some MatrixStage4OrdinalCopyAlignment.done := by
    dsimp [terminal,MatrixStage4OrdinalCopyAlignment.alignmentFrame,
      BitMachineEncoding.renameCfg,BitMachineComposition.liftCfg]
    rw [hhalt]
    rfl
  have hf := MatrixStage4OrdinalCopyAlignment.finish terminal hlabel
  have h12 := MatrixStage4OrdinalCopyAlignment.run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := MatrixStage4OrdinalCopyAlignment.run_add h12 1
  rw [hf] at h123
  refine ⟨t₁+t₂+1,by omega,?_,?_,?_,?_,?_,?_⟩
  · rw [h123]
  · rw [h123]
    rfl
  · rw [h123]
    simpa only [terminal,MatrixStage4OrdinalCopyAlignment.alignmentFrame,
      BitMachineEncoding.renameCfg,BitMachineComposition.liftCfg,
      target] using hflag
  · rw [h123]
    simpa only [terminal,MatrixStage4OrdinalCopyAlignment.alignmentFrame,
      BitMachineEncoding.renameCfg,BitMachineComposition.liftCfg,
      target] using hquo
  · rw [h123]
    simpa only [terminal,MatrixStage4OrdinalCopyAlignment.alignmentFrame,
      BitMachineEncoding.renameCfg,BitMachineComposition.liftCfg,
      target] using hsel
  · rw [h123]
    rfl

end EthInapproximability.CurrentPaper.MatrixStage4AlignmentSelector
