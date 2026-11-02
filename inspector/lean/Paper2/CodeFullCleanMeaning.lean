import Paper2.CodeFullCleanStep
import Mathlib.Tactic

/-! The two persistent interpreter banks after the physical clean step
agree with the first-order source's next code and output. -/

namespace Paper2.CodeFullCleanMeaning

open Turing
open EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization

noncomputable section

abbrev Stack := CodeFullCleanStep.Stack

def codeSlot : Stack := CodeHeaderDraw.h 0
def outputSlot : Stack := CodeHeaderDraw.output

def readyBank (s : State) (tape : List Bool) (B R : Nat) :
    Stack → List Bool :=
  Sum.elim (DrawParameterLoader.initialBank tape 0 B R)
    (CodeScanner.bank
      (CodeHeaderMachine.contents
        (CodeAdminNormalization.todoWord s.todo) [] [] [] [] [] [])
      s.output.reverse)

theorem start_bank (s : State) (tape : List Bool) (B R : Nat) :
    (CodeAdminBranchJoin.start s tape B R).stk = readyBank s tape B R := by
  funext k
  cases k with
  | inl k =>
      change (EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank
        CodeAdminDraw.adminSlot (CodeAdminDraw.foreign tape B R)
        (CodeAdminNormalization.stateCfg s).stk) (.inl k) = _
      rw [EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_outside]
      · rfl
      · rintro ⟨j,hj⟩
        cases hj
  | inr k =>
      change (EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank
        CodeAdminDraw.adminSlot (CodeAdminDraw.foreign tape B R)
        (CodeAdminNormalization.stateCfg s).stk) (.inr k) = _
      rw [show (Sum.inr k : Stack) = CodeAdminDraw.adminSlot k from rfl]
      rw [EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_at]
      simp [CodeAdminNormalization.stateCfg,CodeAdminMachine.ready,
        CodeAdminMachine.cfg,readyBank,CodeAdminDraw.adminSlot]

theorem reset_ready (S : Stack → List Bool) (s : State)
    (tape : List Bool) (B R : Nat)
    (hT : S (CodeHeaderDraw.d 0) = tape)
    (hB : S (CodeHeaderDraw.d 11) = List.replicate B true)
    (hR : S (CodeHeaderDraw.d 12) = List.replicate R true)
    (hC : S codeSlot = CodeAdminNormalization.todoWord s.todo)
    (hO : S outputSlot = s.output.reverse) :
    CodeInterpreterReset.resetBank S = readyBank s tape B R := by
  funext k
  rcases k with ((i | j) | (i | j))
  · fin_cases i <;> simp [CodeInterpreterReset.resetBank,
      CodeInterpreterReset.keep,readyBank,
      DrawParameterLoader.initialBank,DrawParameterLoader.mainBank,
      CodeHeaderDraw.d,codeSlot,outputSlot] at * <;>
      first | exact hT | exact hB | exact hR
  · simp [CodeInterpreterReset.resetBank,CodeInterpreterReset.keep,
      readyBank,DrawParameterLoader.initialBank,
      DrawParameterLoader.mainBank]
  · fin_cases i
    all_goals simp [CodeInterpreterReset.resetBank,
      CodeInterpreterReset.keep,readyBank,CodeScanner.bank,
      CodeHeaderMachine.contents,codeSlot,outputSlot,
      CodeHeaderDraw.h] at *
    all_goals exact hC
  · fin_cases j
    all_goals simp [CodeInterpreterReset.resetBank,
      CodeInterpreterReset.keep,readyBank,CodeScanner.bank,
      codeSlot,outputSlot,CodeHeaderDraw.output] at *
    all_goals exact hO

theorem reset_final_ready (flag : CodeAdminBranchJoin.Control)
    (S : Stack → List Bool) (s : State) (tape : List Bool) (B R : Nat)
    (hT : S (CodeHeaderDraw.d 0) = tape)
    (hB : S (CodeHeaderDraw.d 11) = List.replicate B true)
    (hR : S (CodeHeaderDraw.d 12) = List.replicate R true)
    (hC : S codeSlot = CodeAdminNormalization.todoWord s.todo)
    (hO : S outputSlot = s.output.reverse) :
    (CodeInterpreterReset.final flag S).stk =
      (CodeAdminBranchJoin.start s tape B R).stk := by
  rw [CodeInterpreterReset.final,show
    CodeInterpreterReset.resetBank S = readyBank s tape B R from
      reset_ready S s tape B R hT hB hR hC hO,
    ← start_bank]

private theorem output_public_slot (input suffix : List Bool)
    (D B R : Nat) (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) (j : Fin 16) (hj : j.val = 11 ∨ j.val = 12) :
    (LoadedTicketMachine.outputBank input suffix D B R F word) (.inl j) =
      DrawParameterLoader.mainBank input (Nat.clog 2 D)
        (B - Nat.clog 2 D) R (D-1) D B R [] [] F (.inl j) := by
  rw [LoadedTicketMachine.outputBank,
    EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_outside]
  rintro ⟨k,hk⟩
  have hv := congrArg (fun x : DrawParameterLoader.Stack =>
    match x with | .inl z => z.val | .inr _ => 0) hk
  cases k with
  | inl k =>
      simp [LoadedTicketMachine.ticketEmbed,
        LoadedTicketMachine.ticketSlot] at hv
      omega
  | inr k =>
      fin_cases k
      simp [LoadedTicketMachine.ticketEmbed,
        LoadedTicketMachine.ticketSlot] at hv
      omega

theorem result_public_slots (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind) (tail n a b outputWord : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    (CodeHeaderDraw.resultCfg D B R N hB tape kind tail n a b
      outputWord F).stk (CodeHeaderDraw.d 11) = List.replicate B true ∧
    (CodeHeaderDraw.resultCfg D B R N hB tape kind tail n a b
      outputWord F).stk (CodeHeaderDraw.d 12) = List.replicate R true := by
  constructor
  · change (LoadedTicketMachine.outputBank _ _ D B R F _)
      (.inl (11 : Fin 16)) = _
    rw [output_public_slot _ _ _ _ _ _ _ 11 (Or.inl rfl)]
    simp [DrawParameterLoader.mainBank]
  · change (LoadedTicketMachine.outputBank _ _ D B R F _)
      (.inl (12 : Fin 16)) = _
    rw [output_public_slot _ _ _ _ _ _ _ 12 (Or.inr rfl)]
    simp [DrawParameterLoader.mainBank]

theorem handled_outer (saved : CodeDrawResultHandler.Saved)
    (S : Stack → List Bool) (newOutput : List Bool)
    (j : Fin 16) (hj : j ≠ 15) :
    (CodeDrawResultHandler.framed saved S
      (CodeDrawOutput.cfg none none [] newOutput)).stk
        (CodeHeaderDraw.d j) = S (CodeHeaderDraw.d j) := by
  change (EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank
    CodeDrawResultHandler.outputSlot S
    (CodeDrawOutput.cfg none none [] newOutput).stk)
      (CodeHeaderDraw.d j) = _
  apply EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_outside
  rintro ⟨k,hk⟩
  fin_cases k <;> simp [CodeDrawResultHandler.outputSlot,
    CodeHeaderDraw.d,CodeHeaderDraw.output] at hk; omega

theorem handled_result_public (D B R N : Nat)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind) (tail n a b outputWord : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (newOutput : List Bool) :
    let raw := CodeAdminDraw.drawResult D B R N hB tape kind
      tail n a b outputWord F
    let handled := CodeDrawResultHandler.framed raw.var raw.stk
      (CodeDrawOutput.cfg none none [] newOutput)
    handled.stk (CodeHeaderDraw.d 0) =
      (RecursiveSamplingTape.writeTape B R N tape.2).val ∧
    handled.stk (CodeHeaderDraw.d 11) = List.replicate B true ∧
    handled.stk (CodeHeaderDraw.d 12) = List.replicate R true := by
  intro raw handled
  have hpublic := result_public_slots D B R N hB tape kind
    tail n a b outputWord F
  have htape := (CodeHeaderDraw.result_tape_ticket D B R N hB tape kind
    tail n a b outputWord F).1
  constructor
  · rw [show handled.stk (CodeHeaderDraw.d 0) =
      raw.stk (CodeHeaderDraw.d 0) from handled_outer _ _ _ 0 (by decide)]
    simpa [raw,CodeAdminDraw.drawResult,BitMachineInline.cfg] using htape
  constructor
  · rw [show handled.stk (CodeHeaderDraw.d 11) =
      raw.stk (CodeHeaderDraw.d 11) from handled_outer _ _ _ 11 (by decide)]
    simpa [raw,CodeAdminDraw.drawResult,BitMachineInline.cfg] using hpublic.1
  · rw [show handled.stk (CodeHeaderDraw.d 12) =
      raw.stk (CodeHeaderDraw.d 12) from handled_outer _ _ _ 12 (by decide)]
    simpa [raw,CodeAdminDraw.drawResult,BitMachineInline.cfg] using hpublic.2

theorem handled_code (saved : CodeDrawResultHandler.Saved)
    (S : Stack → List Bool) (newOutput : List Bool) :
    (CodeDrawResultHandler.framed saved S
      (CodeDrawOutput.cfg none none [] newOutput)).stk codeSlot = S codeSlot := by
  change (EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank
    CodeDrawResultHandler.outputSlot S
    (CodeDrawOutput.cfg none none [] newOutput).stk) codeSlot = _
  apply EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_outside
  rintro ⟨k,hk⟩
  fin_cases k <;> cases hk

theorem handled_output (saved : CodeDrawResultHandler.Saved)
    (S : Stack → List Bool) (newOutput : List Bool) :
    (CodeDrawResultHandler.framed saved S
      (CodeDrawOutput.cfg none none [] newOutput)).stk outputSlot = newOutput := by
  change (EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank
    CodeDrawResultHandler.outputSlot S
    (CodeDrawOutput.cfg none none [] newOutput).stk)
      (CodeDrawResultHandler.outputSlot 1) = _
  rw [EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_at]
  rfl

theorem clean_code (flag : CodeAdminBranchJoin.Control)
    (S : Stack → List Bool) :
    (CodeInterpreterReset.final flag S).stk codeSlot = S codeSlot := by
  exact CodeInterpreterReset.reset_code S

theorem clean_output (flag : CodeAdminBranchJoin.Control)
    (S : Stack → List Bool) :
    (CodeInterpreterReset.final flag S).stk outputSlot = S outputSlot := by
  exact CodeInterpreterReset.reset_output S

theorem ticket_next_banks (D B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (cs : List Code) (out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (q : Fin D) :
    let raw := CodeAdminDraw.drawResult D B R N hB tape .ticket
      (CodeAdminNormalization.todoWord cs) (List.replicate D true) [] [] out.reverse F
    let handled := CodeDrawResultHandler.framed raw.var raw.stk
      (CodeDrawOutput.cfg none none []
        (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ out.reverse))
    let joined := CodeAdminResultJoin.resultCfg handled
    let endpoint : CodeAdminBranchJoin.Config :=
      ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
    let clean := CodeInterpreterReset.final endpoint.var endpoint.stk
    clean.stk codeSlot =
      CodeAdminNormalization.todoWord
        (GeneratorCode.advance ⟨.ticket D::cs,out⟩ q.val).todo ∧
    clean.stk outputSlot =
      (GeneratorCode.advance ⟨.ticket D::cs,out⟩ q.val).output.reverse := by
  intro raw handled joined endpoint clean
  cases D with
  | zero => omega
  | succ k =>
  constructor
  · rw [show clean.stk codeSlot = endpoint.stk codeSlot from clean_code _ _]
    change handled.stk codeSlot = _
    rw [handled_code]
    have hslot := (CodeHeaderDraw.result_header_slots (k+1) B R N hB tape
      .ticket (CodeAdminNormalization.todoWord cs)
      (List.replicate (k+1) true) [] [] out.reverse F).1
    simpa [raw,codeSlot,CodeAdminDraw.drawResult,BitMachineInline.cfg,
      GeneratorCode.advance,CodeAdminNormalization.todoWord] using hslot
  · rw [show clean.stk outputSlot = endpoint.stk outputSlot from clean_output _ _]
    change handled.stk outputSlot = _
    rw [handled_output]
    simp [GeneratorCode.advance,RecursiveLabelCodecScratch.finCodec,
      List.reverse_append]

theorem ticket_ready_bank (D B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (cs : List Code) (out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (q : Fin D) :
    let next := GeneratorCode.advance ⟨.ticket D::cs,out⟩ q.val
    let raw := CodeAdminDraw.drawResult D B R N hB tape .ticket
      (CodeAdminNormalization.todoWord cs) (List.replicate D true) [] [] out.reverse F
    let handled := CodeDrawResultHandler.framed raw.var raw.stk
      (CodeDrawOutput.cfg none none []
        (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ out.reverse))
    let joined := CodeAdminResultJoin.resultCfg handled
    let endpoint : CodeAdminBranchJoin.Config :=
      ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
    (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
      (CodeAdminBranchJoin.start next
        (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
  intro next raw handled joined endpoint
  have hp := handled_result_public D B R N hB tape .ticket
    (CodeAdminNormalization.todoWord cs) (List.replicate D true) [] []
    out.reverse F
    (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ out.reverse)
  have hn := ticket_next_banks D B R N hD hB tape cs out F q
  apply reset_final_ready endpoint.var endpoint.stk next
    (RecursiveSamplingTape.writeTape B R N tape.2).val B R
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2
  · exact (clean_code endpoint.var endpoint.stk).symm.trans hn.1
  · exact (clean_output endpoint.var endpoint.stk).symm.trans hn.2

theorem bit_next_banks (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (cs : List Code) (out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (q : Fin 2) :
    let raw := CodeAdminDraw.drawResult 2 B R N hB tape .bit
      (CodeAdminNormalization.todoWord cs) [] [] [] out.reverse F
    let handled := CodeDrawResultHandler.framed raw.var raw.stk
      (CodeDrawOutput.cfg none none [] (decide (q.val=1)::out.reverse))
    let joined := CodeAdminResultJoin.resultCfg handled
    let endpoint : CodeAdminBranchJoin.Config :=
      ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
    let clean := CodeInterpreterReset.final endpoint.var endpoint.stk
    clean.stk codeSlot =
      CodeAdminNormalization.todoWord
        (GeneratorCode.advance ⟨.bit::cs,out⟩ q.val).todo ∧
    clean.stk outputSlot =
      (GeneratorCode.advance ⟨.bit::cs,out⟩ q.val).output.reverse := by
  intro raw handled joined endpoint clean
  constructor
  · rw [show clean.stk codeSlot = endpoint.stk codeSlot from clean_code _ _]
    change handled.stk codeSlot = _
    rw [handled_code]
    have hslot := (CodeHeaderDraw.result_header_slots 2 B R N hB tape
      .bit (CodeAdminNormalization.todoWord cs) [] [] [] out.reverse F).1
    simpa [raw,codeSlot,CodeAdminDraw.drawResult,BitMachineInline.cfg,
      GeneratorCode.advance,CodeAdminNormalization.todoWord] using hslot
  · rw [show clean.stk outputSlot = endpoint.stk outputSlot from clean_output _ _]
    change handled.stk outputSlot = _
    rw [handled_output]
    simp [GeneratorCode.advance,List.reverse_append]

theorem bit_ready_bank (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (cs : List Code) (out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (q : Fin 2) :
    let next := GeneratorCode.advance ⟨.bit::cs,out⟩ q.val
    let raw := CodeAdminDraw.drawResult 2 B R N hB tape .bit
      (CodeAdminNormalization.todoWord cs) [] [] [] out.reverse F
    let handled := CodeDrawResultHandler.framed raw.var raw.stk
      (CodeDrawOutput.cfg none none [] (decide (q.val=1)::out.reverse))
    let joined := CodeAdminResultJoin.resultCfg handled
    let endpoint : CodeAdminBranchJoin.Config :=
      ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
    (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
      (CodeAdminBranchJoin.start next
        (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
  intro next raw handled joined endpoint
  have hp := handled_result_public 2 B R N hB tape .bit
    (CodeAdminNormalization.todoWord cs) [] [] []
    out.reverse F (decide (q.val=1)::out.reverse)
  have hn := bit_next_banks B R N hB tape cs out F q
  apply reset_final_ready endpoint.var endpoint.stk next
    (RecursiveSamplingTape.writeTape B R N tape.2).val B R
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2
  · exact (clean_code endpoint.var endpoint.stk).symm.trans hn.1
  · exact (clean_output endpoint.var endpoint.stk).symm.trans hn.2

theorem branch_next_banks (D a b B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (f g h : Code) (cs : List Code) (out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (q : Fin D) :
    let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
      (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
      (List.replicate D true) (List.replicate a true)
      (List.replicate b true) out.reverse F
    let raw := CodeAdminDraw.drawResult D B R N hB tape .branch3
      (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
      (List.replicate D true) (List.replicate a true)
      (List.replicate b true) out.reverse F
    let joined : CodeAdminResultJoin.Config :=
      CodeAdminResultJoin.resultCfg ⟨none,(raw.var,none),raw.stk⟩
    let selected := CodeBranchAdapter.final base.var base.stk
      (List.replicate D true) out.reverse q.val a b f g h
      (CodeAdminNormalization.todoWord cs)
    let endpoint := CodeAdminBranchJoin.branchCfg joined.var selected
    let clean := CodeInterpreterReset.final endpoint.var endpoint.stk
    clean.stk codeSlot =
      CodeAdminNormalization.todoWord
        (GeneratorCode.advance ⟨.branch3 D a b f g h::cs,out⟩ q.val).todo ∧
    clean.stk outputSlot =
      (GeneratorCode.advance ⟨.branch3 D a b f g h::cs,out⟩ q.val).output.reverse := by
  intro base raw joined selected endpoint clean
  cases D with
  | zero => omega
  | succ k =>
  constructor
  · rw [show clean.stk codeSlot = endpoint.stk codeSlot from clean_code _ _]
    change selected.stk codeSlot = _
    simp [selected,CodeBranchAdapter.final,CodeBranchAdapter.framedBank,
      codeSlot,CodeHeaderDraw.h,GeneratorCode.advance,
      CodeAdminNormalization.todoWord,List.flatMap_cons]
  · rw [show clean.stk outputSlot = endpoint.stk outputSlot from clean_output _ _]
    change selected.stk outputSlot = _
    simp [selected,CodeBranchAdapter.final,CodeBranchAdapter.framedBank,
      outputSlot,CodeHeaderDraw.output,GeneratorCode.advance]

theorem branch_ready_bank (D a b B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (f g h : Code) (cs : List Code) (out : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (q : Fin D) :
    let next := GeneratorCode.advance ⟨.branch3 D a b f g h::cs,out⟩ q.val
    let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
      (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
      (List.replicate D true) (List.replicate a true)
      (List.replicate b true) out.reverse F
    let raw := CodeAdminDraw.drawResult D B R N hB tape .branch3
      (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
      (List.replicate D true) (List.replicate a true)
      (List.replicate b true) out.reverse F
    let joined : CodeAdminResultJoin.Config :=
      CodeAdminResultJoin.resultCfg ⟨none,(raw.var,none),raw.stk⟩
    let selected := CodeBranchAdapter.final base.var base.stk
      (List.replicate D true) out.reverse q.val a b f g h
      (CodeAdminNormalization.todoWord cs)
    let endpoint := CodeAdminBranchJoin.branchCfg joined.var selected
    (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
      (CodeAdminBranchJoin.start next
        (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
  intro next base raw joined selected endpoint
  have hp := result_public_slots D B R N hB tape .branch3
    (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) out.reverse F
  have htape := (CodeHeaderDraw.result_tape_ticket D B R N hB tape .branch3
    (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) out.reverse F).1
  have hn := branch_next_banks D a b B R N hD hB tape f g h cs out F q
  apply reset_final_ready endpoint.var endpoint.stk next
    (RecursiveSamplingTape.writeTape B R N tape.2).val B R
  · simpa [endpoint,CodeAdminBranchJoin.branchCfg,BitMachineInline.cfg,
      selected,CodeBranchAdapter.final,CodeBranchAdapter.framedBank,
      base] using htape
  · simpa [endpoint,CodeAdminBranchJoin.branchCfg,BitMachineInline.cfg,
      selected,CodeBranchAdapter.final,CodeBranchAdapter.framedBank,
      base] using hp.1
  · simpa [endpoint,CodeAdminBranchJoin.branchCfg,BitMachineInline.cfg,
      selected,CodeBranchAdapter.final,CodeBranchAdapter.framedBank,
      base] using hp.2
  · exact (clean_code endpoint.var endpoint.stk).symm.trans hn.1
  · exact (clean_output endpoint.var endpoint.stk).symm.trans hn.2

#print axioms ticket_next_banks
#print axioms bit_next_banks
#print axioms branch_next_banks
#print axioms reset_final_ready
#print axioms ticket_ready_bank
#print axioms bit_ready_bank
#print axioms branch_ready_bank

end
end Paper2.CodeFullCleanMeaning
