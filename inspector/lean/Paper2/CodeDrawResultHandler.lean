import Paper2.CodeAdminDraw
import Paper2.CodeDrawOutput
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import Mathlib.Tactic

/-! A fixed, status-preserving ticket/bit result handler. -/

namespace Paper2.CodeDrawResultHandler

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

noncomputable section

abbrev Stack := CodeAdminDraw.Stack
abbrev Saved := CodeAdminDraw.Control
abbrev Control := Saved × Option Bool

inductive Admin where | dispatch
  deriving DecidableEq, Fintype

abbrev Label := Admin ⊕ (Saved × CodeDrawOutput.Label)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def outputSlot : Fin 2 ↪ Stack where
  toFun
    | 0 => CodeHeaderDraw.d 15
    | _ => CodeHeaderDraw.output
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp [CodeHeaderDraw.d,
      CodeHeaderDraw.output] at h ⊢

def savedStatus (v : Saved) : Option Bool := v.1.1.2.2
def savedKind (v : Saved) : Option CodeHeaderMachine.Kind := v.1.2.2

noncomputable def outputProgram (saved : Saved) (l : CodeDrawOutput.Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineStackEmbedding.stmt outputSlot (fun x => .inr (saved,x))
    (fun w => (saved,w)) Prod.snd none (CodeDrawOutput.program l)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl .dispatch =>
      branch (fun v => savedStatus v.1 == some true)
        (branch (fun v => savedKind v.1 == some .ticket)
          (goto (fun v => .inr (v.1,.ticket)))
          (branch (fun v => savedKind v.1 == some .bit)
            (goto (fun v => .inr (v.1,.bitStart))) halt))
        halt
  | .inr (saved,l) => outputProgram saved l

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def start (c : CodeAdminDraw.Config) : Config :=
  ⟨some (.inl .dispatch),(c.var,none),c.stk⟩

noncomputable def framed (saved : Saved) (S : Stack → List Bool)
    (c : CodeDrawOutput.Config) : Config :=
  BitMachineStackEmbedding.cfg outputSlot S
    (fun l => .inr (saved,l)) (fun w => (saved,w)) none c

theorem framed_start (saved : Saved) (S : Stack → List Bool)
    (label : CodeDrawOutput.Label) (input output : List Bool)
    (hi : S (CodeHeaderDraw.d 15) = input)
    (ho : S CodeHeaderDraw.output = output) :
    framed saved S (CodeDrawOutput.cfg (some label) none input output) =
      ⟨some (.inr (saved,label)),(saved,none),S⟩ := by
  change (⟨some (.inr (saved,label)),(saved,none),
    BitMachineStackEmbedding.bank outputSlot S
      (CodeDrawOutput.cfg (some label) none input output).stk⟩ : Config) = _
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k
  · simpa [outputSlot, CodeDrawOutput.cfg, CodeDrawOutput.bank] using hi.symm
  · simpa [outputSlot, CodeDrawOutput.cfg, CodeDrawOutput.bank] using ho.symm

private theorem output_lift_read (saved : Saved) :
    Function.LeftInverse Prod.snd (fun w : Option Bool => (saved,w)) := by
  intro w; rfl

theorem output_run (saved : Saved) (S : Stack → List Bool)
    (c : CodeDrawOutput.Config) (t : Nat)
    (hh : (((advance CodeDrawOutput.program)^[t]) c).l = none) :
    ∃ u ≤ t, run u (framed saved S c) =
      framed saved S (((advance CodeDrawOutput.program)^[t]) c) := by
  obtain ⟨u,hu,hur⟩ := BitMachineStackEmbedding.outputs outputSlot S
    (fun l => .inr (saved,l)) (fun w => (saved,w)) Prod.snd
    (output_lift_read saved) none CodeDrawOutput.program program
    (by intro l; rfl) c t hh
  exact ⟨u,hu,hur⟩

theorem dispatch_failure (saved : Saved) (S : Stack → List Bool)
    (hfail : savedStatus saved ≠ some true) :
    run 1 (start ⟨none,saved,S⟩) = ⟨none,(saved,none),S⟩ := by
  have hf : (savedStatus saved == some true) = false := by
    simp [hfail]
  simp [run, start, program, BitMachineEncoding.advance, TM2.step,
    TM2.stepAux, hf]

theorem dispatch_ticket (saved : Saved) (S : Stack → List Bool)
    (hs : savedStatus saved = some true)
    (hk : savedKind saved = some .ticket) :
    run 1 (start ⟨none,saved,S⟩) =
      ⟨some (.inr (saved,.ticket)),(saved,none),S⟩ := by
  simp [run, start, program, BitMachineEncoding.advance, TM2.step,
    TM2.stepAux, hs, hk]

theorem dispatch_bit (saved : Saved) (S : Stack → List Bool)
    (hs : savedStatus saved = some true)
    (hk : savedKind saved = some .bit) :
    run 1 (start ⟨none,saved,S⟩) =
      ⟨some (.inr (saved,.bitStart)),(saved,none),S⟩ := by
  have hne : ((some CodeHeaderMachine.Kind.bit) ==
      (some CodeHeaderMachine.Kind.ticket)) = false := by decide
  simp [run, start, program, BitMachineEncoding.advance, TM2.step,
    TM2.stepAux, hs, hk, hne]

theorem accepted_ticket (saved : Saved) (S : Stack → List Bool)
    (input output : List Bool)
    (hs : savedStatus saved = some true)
    (hk : savedKind saved = some .ticket)
    (hi : S (CodeHeaderDraw.d 15) = input)
    (ho : S CodeHeaderDraw.output = output) :
    ∃ t ≤ input.length+2,
      run t (start ⟨none,saved,S⟩) =
        framed saved S (CodeDrawOutput.cfg none none [] (input.reverse ++ output)) := by
  let c := CodeDrawOutput.cfg (some .ticket) none input output
  have hlocal := CodeDrawOutput.ticket_word input output none
  have hh : (((advance CodeDrawOutput.program)^[input.length+1]) c).l = none := by
    rw [hlocal]; rfl
  obtain ⟨u,hu,hur⟩ := output_run saved S c (input.length+1) hh
  refine ⟨u+1,by omega,?_⟩
  have hadd : run (u+1) (start ⟨none,saved,S⟩) =
      run u (run 1 (start ⟨none,saved,S⟩)) := by
    simp [run, Function.iterate_add_apply]
  rw [hadd,dispatch_ticket saved S hs hk,
    ← framed_start saved S .ticket input output hi ho,hur,hlocal]

theorem accepted_bit (saved : Saved) (S : Stack → List Bool)
    (i : Fin 2) (output : List Bool)
    (hs : savedStatus saved = some true)
    (hk : savedKind saved = some .bit)
    (hi : S (CodeHeaderDraw.d 15) =
      (RecursiveLabelCodecScratch.finCodec 2).encode i)
    (ho : S CodeHeaderDraw.output = output) :
    ∃ t ≤ i.val+3,
      run t (start ⟨none,saved,S⟩) =
        framed saved S (CodeDrawOutput.cfg none none []
          (decide (i.val=1)::output)) := by
  let c := CodeDrawOutput.cfg (some .bitStart) none
    ((RecursiveLabelCodecScratch.finCodec 2).encode i) output
  have hlocal := CodeDrawOutput.bit_codec i output
  have hh : (((advance CodeDrawOutput.program)^[i.val+2]) c).l = none := by
    rw [hlocal]; rfl
  obtain ⟨u,hu,hur⟩ := output_run saved S c (i.val+2) hh
  refine ⟨u+1,by omega,?_⟩
  have hadd : run (u+1) (start ⟨none,saved,S⟩) =
      run u (run 1 (start ⟨none,saved,S⟩)) := by
    simp [run, Function.iterate_add_apply]
  rw [hadd,dispatch_bit saved S hs hk,
    ← framed_start saved S .bitStart _ output hi ho,hur,hlocal]

theorem result_status (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind) (tail n a b output : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    savedStatus (CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F).var =
      some (CappedSampler.runWideBits D B R hB tape.1).isSome ∧
    savedKind (CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F).var =
      some kind := by
  exact ⟨rfl,rfl⟩

theorem result_input_output (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind) (tail n a b output : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    (CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F).stk
      (CodeHeaderDraw.d 15) = LoadedTicketMachine.resultWord D B R N hB tape ∧
    (CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F).stk
      CodeHeaderDraw.output = output := by
  constructor
  · exact (CodeHeaderDraw.result_tape_ticket D B R N hB tape kind
      tail n a b output F).2
  · exact (CodeHeaderDraw.result_header_slots D B R N hB tape kind
      tail n a b output F).2.2.2.2

theorem actual_failure (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind) (tail n a b output : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (hq : CappedSampler.runWideBits D B R hB tape.1 = none) :
    run 1 (start (CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F)) =
      ⟨none,((CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F).var,none),
        (CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F).stk⟩ := by
  apply dispatch_failure
  have hf : savedStatus
      (CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F).var =
        some false := by
    simpa [hq] using
      (result_status D B R N hB tape kind tail n a b output F).1
  change savedStatus
    (CodeAdminDraw.drawResult D B R N hB tape kind tail n a b output F).var ≠
      some true
  rw [hf]
  decide

theorem actual_ticket_success (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (tail n a b output : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ t ≤ D+2,
      run t (start (CodeAdminDraw.drawResult D B R N hB tape .ticket
        tail n a b output F)) =
        framed (CodeAdminDraw.drawResult D B R N hB tape .ticket
          tail n a b output F).var
          (CodeAdminDraw.drawResult D B R N hB tape .ticket
            tail n a b output F).stk
          (CodeDrawOutput.cfg none none []
            (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ output)) := by
  let c := CodeAdminDraw.drawResult D B R N hB tape .ticket tail n a b output F
  have hs : savedStatus c.var = some true := by
    simpa [c,hq] using (result_status D B R N hB tape .ticket tail n a b output F).1
  have hk : savedKind c.var = some .ticket := by
    exact (result_status D B R N hB tape .ticket tail n a b output F).2
  have hi : c.stk (CodeHeaderDraw.d 15) =
      (RecursiveLabelCodecScratch.finCodec D).encode q := by
    rw [(result_input_output D B R N hB tape .ticket tail n a b output F).1]
    exact CodeHeaderDraw.result_word_success D B R N hB tape q hq
  have ho : c.stk CodeHeaderDraw.output = output :=
    (result_input_output D B R N hB tape .ticket tail n a b output F).2
  obtain ⟨t,ht,hr⟩ := accepted_ticket c.var c.stk
    ((RecursiveLabelCodecScratch.finCodec D).encode q) output hs hk hi ho
  refine ⟨t,?_,by simpa [c] using hr⟩
  have hlen : ((RecursiveLabelCodecScratch.finCodec D).encode q).length = q.val+1 := by
    simp [RecursiveLabelCodecScratch.finCodec]
  omega

theorem actual_bit_success (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (tail output : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (q : Fin 2) (hq : CappedSampler.runWideBits 2 B R hB tape.1 = some q) :
    ∃ t ≤ 4,
      run t (start (CodeAdminDraw.drawResult 2 B R N hB tape .bit
        tail [] [] [] output F)) =
        framed (CodeAdminDraw.drawResult 2 B R N hB tape .bit
          tail [] [] [] output F).var
          (CodeAdminDraw.drawResult 2 B R N hB tape .bit
            tail [] [] [] output F).stk
          (CodeDrawOutput.cfg none none [] (decide (q.val=1)::output)) := by
  let c := CodeAdminDraw.drawResult 2 B R N hB tape .bit tail [] [] [] output F
  have hs : savedStatus c.var = some true := by
    simpa [c,hq] using (result_status 2 B R N hB tape .bit tail [] [] [] output F).1
  have hk : savedKind c.var = some .bit :=
    (result_status 2 B R N hB tape .bit tail [] [] [] output F).2
  have hi : c.stk (CodeHeaderDraw.d 15) =
      (RecursiveLabelCodecScratch.finCodec 2).encode q := by
    rw [(result_input_output 2 B R N hB tape .bit tail [] [] [] output F).1]
    exact CodeHeaderDraw.result_word_success 2 B R N hB tape q hq
  have ho : c.stk CodeHeaderDraw.output = output :=
    (result_input_output 2 B R N hB tape .bit tail [] [] [] output F).2
  obtain ⟨t,ht,hr⟩ := accepted_bit c.var c.stk q output hs hk hi ho
  exact ⟨t,by omega,by simpa [c] using hr⟩

#print axioms dispatch_failure
#print axioms accepted_ticket
#print axioms accepted_bit
#print axioms actual_failure
#print axioms actual_ticket_success
#print axioms actual_bit_success

end
end Paper2.CodeDrawResultHandler
