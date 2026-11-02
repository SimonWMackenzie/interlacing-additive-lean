import Paper2.DrawParameterLoader
import Paper2.CappedTicketStatusSource
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import Mathlib.Tactic

/-! A physically loaded one-draw ticket machine. No prepared scalar is an input. -/

namespace Paper2.LoadedTicketMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

noncomputable section

abbrev Stack := DrawParameterLoader.Stack
abbrev StatusStack := TicketStatus.Stack
abbrev StatusLabel := BitMachineRawSequence.Label
  (TicketWordScratch.DrawLabel ⊕ Unit) TicketStatus.Label
abbrev StatusControl := (TicketWordScratch.DrawControl × Unit) × Option Bool

def ticketSlot : StatusStack → Stack
  | .inl i => .inl ⟨i.val, by omega⟩
  | .inr _ => .inl 15

private theorem ticketSlot_injective : Function.Injective ticketSlot := by
  intro x y h
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          simp only [ticketSlot, Sum.inl.injEq, Fin.mk.injEq] at h
          exact congrArg Sum.inl (Fin.ext h)
      | inr j =>
          fin_cases j
          have hv := congrArg (fun x : Stack =>
            match x with | .inl z => z.val | .inr _ => 0) h
          simp [ticketSlot] at hv
          omega
  | inr i =>
      fin_cases i
      cases y with
      | inl j =>
          have hv := congrArg (fun x : Stack =>
            match x with | .inl z => z.val | .inr _ => 0) h
          simp [ticketSlot] at hv
          omega
      | inr j => fin_cases j; rfl

def ticketEmbed : StatusStack ↪ Stack :=
  ⟨ticketSlot, ticketSlot_injective⟩

noncomputable def ticketProgram :
    StatusLabel → TM2.Stmt (fun _ : Stack => Bool) StatusLabel StatusControl :=
  fun l => BitMachineStackEmbedding.stmt ticketEmbed id id id none
    (TicketStatus.fullProgram l)

abbrev statusStart : StatusLabel :=
  BitMachineRawSequence.leftLabel (.inl TicketWordScratch.drawStart)
abbrev statusStartControl : StatusControl :=
  ((TicketWordScratch.drawInitial, ()), none)

abbrev LoaderLabel := DrawParameterLoader.FullLabel
abbrev LoaderControl := DrawParameterLoader.FullControl
abbrev loaderStartLabel : LoaderLabel :=
  BitMachineRawSequence.leftLabel
    (Sum.inl EthInapproximability.CurrentPaper.BitMachineCopy.Label.scan)
abbrev loaderStartControl : LoaderControl :=
  (ETHParameterScaleMachineLogCopy.copyControl none, none)

abbrev Label := BitMachineRawSequence.Label LoaderLabel StatusLabel
abbrev Control := BitMachineRawSequence.Control LoaderControl StatusControl

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program DrawParameterLoader.fullProgram ticketProgram
    statusStart loaderStartControl statusStartControl

noncomputable def start (tape : List Bool) (D B R : Nat) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨some (BitMachineRawSequence.leftLabel loaderStartLabel),
    (loaderStartControl, statusStartControl),
    (DrawParameterLoader.fullStart tape D B R).stk⟩

noncomputable def run (t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c

def loaderBound (D B R : Nat) : Nat :=
  (2 * D + 2 +
    (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 6) *
      (D + 1) ^ 2) +
  (3 * Nat.clog 2 D + 2 * B + 2 * R + 2 * (D-1) + 11) + 1

def ticketBound (D B R : Nat) : Nat :=
  TicketWordScratch.drawBound D B R + D + 2

def resultWord (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) : List Bool :=
  match CappedSampler.runWideBits D B R hB tape.1 with
  | none => []
  | some q => (RecursiveLabelCodecScratch.finCodec D).encode q

noncomputable def outputBank (input suffix : List Bool) (D B R : Nat)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) : Stack → List Bool :=
  BitMachineStackEmbedding.bank ticketEmbed
    (DrawParameterLoader.mainBank input (Nat.clog 2 D)
      (B - Nat.clog 2 D) R (D-1) D B R [] [] F)
    (TicketStatus.bank (TicketWordScratch.emptyBank suffix) word)

private theorem source_bank_matches (D B R N : Nat)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    TicketStatus.bank
      (TicketWordScratch.sourceInitialBank D B R N tape) [] =
      (fun k => DrawParameterLoader.mainBank
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val (Nat.clog 2 D)
        (B - Nat.clog 2 D) R (D-1) D B R [] [] F (ticketEmbed k)) := by
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i; rfl

private theorem source_bank_full (D B R N : Nat)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    BitMachineStackEmbedding.bank ticketEmbed
      (DrawParameterLoader.mainBank
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val
        (Nat.clog 2 D) (B - Nat.clog 2 D) R (D-1) D B R [] [] F)
      (TicketStatus.bank (TicketWordScratch.sourceInitialBank D B R N tape) []) =
    DrawParameterLoader.mainBank
      (RecursiveSamplingTape.writeTape B R (N+1) tape).val
      (Nat.clog 2 D) (B - Nat.clog 2 D) R (D-1) D B R [] [] F := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  exact congrFun (source_bank_matches D B R N tape F) k

private theorem ticket_lifted (D B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (F : DrawParameterLoader.LogCopyStack → List Bool) :
    ∃ t ≤ ticketBound D B R,
      ((advance ticketProgram)^[t])
        ⟨some statusStart, statusStartControl,
          DrawParameterLoader.mainBank
            (RecursiveSamplingTape.writeTape B R (N+1) tape).val
            (Nat.clog 2 D) (B - Nat.clog 2 D) R (D-1) D B R [] [] F⟩ =
        ⟨none,
          ((TicketWordScratch.drawInitial, ()),
            some (CappedSampler.runWideBits D B R hB tape.1).isSome),
          outputBank (RecursiveSamplingTape.writeTape B R (N+1) tape).val
            (RecursiveSamplingTape.writeTape B R N tape.2).val D B R F
            (resultWord D B R N hB tape)⟩ := by
  obtain ⟨ts, hts, hrs⟩ := TicketStatus.source_ticket D B R N hD hB tape []
  let S : StatusStack → List Bool :=
    TicketStatus.bank (TicketWordScratch.sourceInitialBank D B R N tape) []
  let T : StatusStack → List Bool :=
    TicketStatus.bank
      (TicketWordScratch.emptyBank (RecursiveSamplingTape.writeTape B R N tape.2).val)
      (resultWord D B R N hB tape)
  let L : Stack → List Bool :=
    DrawParameterLoader.mainBank
      (RecursiveSamplingTape.writeTape B R (N+1) tape).val
      (Nat.clog 2 D) (B - Nat.clog 2 D) R (D-1) D B R [] [] F
  have hs : ((advance TicketStatus.fullProgram)^[ts])
      (⟨some statusStart, statusStartControl, S⟩ :
        TM2.Cfg (fun _ : StatusStack => Bool) StatusLabel StatusControl) =
      ⟨none, ((TicketWordScratch.drawInitial, ()),
          some (CappedSampler.runWideBits D B R hB tape.1).isSome), T⟩ := by
    simpa [S, T, statusStart, statusStartControl, resultWord] using hrs
  have hhalt : (((advance TicketStatus.fullProgram)^[ts])
      (⟨some statusStart, statusStartControl, S⟩ :
        TM2.Cfg (fun _ : StatusStack => Bool) StatusLabel StatusControl)).l = none := by
    rw [hs]
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs
    ticketEmbed L id id id (by intro v; rfl) none
    TicketStatus.fullProgram ticketProgram (by intro l; rfl)
    (⟨some statusStart, statusStartControl, S⟩ :
      TM2.Cfg (fun _ : StatusStack => Bool) StatusLabel StatusControl)
    ts hhalt
  rw [hs] at hr
  refine ⟨t, ht.trans hts, ?_⟩
  have hbank : BitMachineStackEmbedding.bank ticketEmbed L S = L := by
    simpa [L, S] using source_bank_full D B R N tape F
  simpa [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, hbank, outputBank, L, T, S] using hr

/-- One fixed program starts with only tape and unary public parameters,
physically loads the capped-draw bank, consumes the serialized draw, and
emits the status-sensitive ticket. The status bit remains in finite control. -/
theorem loaded_source_ticket (D B R N : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ loaderBound D B R + ticketBound D B R + 1 ∧
      run t (start (RecursiveSamplingTape.writeTape B R (N+1) tape).val D B R) =
        ⟨none,
          (loaderStartControl,
            ((TicketWordScratch.drawInitial, ()),
              some (CappedSampler.runWideBits D B R hB tape.1).isSome)),
          outputBank (RecursiveSamplingTape.writeTape B R (N+1) tape).val
            (RecursiveSamplingTape.writeTape B R N tape.2).val D B R F
            (resultWord D B R N hB tape)⟩ := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  let suffix := (RecursiveSamplingTape.writeTape B R N tape.2).val
  obtain ⟨tl,c,htl,hrl⟩ := DrawParameterLoader.full_loader input D B R hD hB
  let F : DrawParameterLoader.LogCopyStack → List Bool :=
    DrawParameterLoader.withLog
      (fun k => DrawParameterLoader.afterLogBank input D B R c (.inr k)) []
  let S : Stack → List Bool := (DrawParameterLoader.fullStart input D B R).stk
  let L : Stack → List Bool :=
    DrawParameterLoader.mainBank input (Nat.clog 2 D)
      (B - Nat.clog 2 D) R (D-1) D B R [] [] F
  let U : Stack → List Bool :=
    outputBank input suffix D B R F (resultWord D B R N hB tape)
  have ha : ((advance DrawParameterLoader.fullProgram)^[tl])
      (⟨some loaderStartLabel, loaderStartControl, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) LoaderLabel LoaderControl) =
      ⟨none, loaderStartControl, L⟩ := by
    simpa [DrawParameterLoader.fullRun, DrawParameterLoader.fullStart,
      loaderStartLabel, loaderStartControl, S, L, F] using hrl
  obtain ⟨te,hte,hre⟩ := ticket_lifted D B R N hD hB tape F
  have hb : ((advance ticketProgram)^[te])
      (⟨some statusStart, statusStartControl, L⟩ :
        TM2.Cfg (fun _ : Stack => Bool) StatusLabel StatusControl) =
      ⟨none,
        ((TicketWordScratch.drawInitial, ()),
          some (CappedSampler.runWideBits D B R hB tape.1).isSome), U⟩ := by
    simpa [L, U, input, suffix] using hre
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    DrawParameterLoader.fullProgram ticketProgram
    loaderStartLabel statusStart
    loaderStartControl loaderStartControl
    statusStartControl
    ((TicketWordScratch.drawInitial, ()),
      some (CappedSampler.runWideBits D B R hB tape.1).isSome)
    S L U tl te ha hb
  refine ⟨t,F,?_,?_⟩
  · dsimp [loaderBound, ticketBound] at *
    omega
  · simpa [run, start, program, S, U, input, suffix] using hr

theorem output_tape (input suffix : List Bool) (D B R : Nat)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) :
    (outputBank input suffix D B R F word) (.inl 0) = suffix := by
  rw [outputBank, ← show ticketEmbed (.inl (0 : Fin 10)) = (.inl (0 : Fin 16)) by rfl,
    BitMachineStackEmbedding.bank_at]
  rfl

theorem output_ticket (input suffix : List Bool) (D B R : Nat)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) :
    (outputBank input suffix D B R F word) (.inl 15) = word := by
  rw [outputBank, ← show ticketEmbed (.inr (0 : Fin 1)) = (.inl (15 : Fin 16)) by rfl,
    BitMachineStackEmbedding.bank_at]
  rfl

theorem output_draw_work_empty (input suffix : List Bool) (D B R : Nat)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) (i : Fin 10) (hi : i ≠ 0) :
    (outputBank input suffix D B R F word)
      (.inl (⟨i.val, by omega⟩ : Fin 16)) = [] := by
  rw [outputBank,
    ← show ticketEmbed (.inl i) =
        (.inl (⟨i.val, by omega⟩ : Fin 16)) by rfl,
    BitMachineStackEmbedding.bank_at]
  fin_cases i <;>
    simp [TicketStatus.bank, TicketWordScratch.emptyBank,
      CappedLoop.Comparator.bank] at hi ⊢

private theorem output_foreign_outer (input suffix : List Bool) (D B R : Nat)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) (i : Fin 16)
    (hi : 10 ≤ i.val) (hne : i.val ≠ 15) :
    (outputBank input suffix D B R F word) (.inl i) =
      DrawParameterLoader.mainBank input (Nat.clog 2 D)
        (B - Nat.clog 2 D) R (D-1) D B R [] [] F (.inl i) := by
  rw [outputBank, BitMachineStackEmbedding.bank_outside]
  rintro ⟨k,h⟩
  cases k with
  | inl j =>
      have hv := congrArg (fun x : Stack =>
        match x with | .inl z => z.val | .inr _ => 0) h
      simp [ticketEmbed, ticketSlot] at hv
      omega
  | inr j =>
      fin_cases j
      have hv := congrArg (fun x : Stack =>
        match x with | .inl z => z.val | .inr _ => 0) h
      simp [ticketEmbed, ticketSlot] at hv
      omega

theorem output_outer_work_empty (input suffix : List Bool) (D B R : Nat)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) :
    (outputBank input suffix D B R F word) (.inl 13) = [] ∧
    (outputBank input suffix D B R F word) (.inl 14) = [] := by
  constructor
  · rw [output_foreign_outer input suffix D B R F word 13 (by decide) (by decide)]
    rfl
  · rw [output_foreign_outer input suffix D B R F word 14 (by decide) (by decide)]
    rfl

theorem output_inner (input suffix : List Bool) (D B R : Nat)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) (k : DrawParameterLoader.LogCopyStack) :
    (outputBank input suffix D B R F word) (.inr k) = F k := by
  rw [outputBank, BitMachineStackEmbedding.bank_outside]
  · rfl
  · rintro ⟨j,h⟩
    cases j <;> simp [ticketEmbed, ticketSlot] at h

theorem output_saved (input suffix : List Bool) (D B R : Nat)
    (F : DrawParameterLoader.LogCopyStack → List Bool)
    (word : List Bool) :
    (outputBank input suffix D B R F word) (.inl 10) = List.replicate D true ∧
    (outputBank input suffix D B R F word) (.inl 11) = List.replicate B true ∧
    (outputBank input suffix D B R F word) (.inl 12) = List.replicate R true := by
  constructor
  · rw [outputBank, BitMachineStackEmbedding.bank_outside]
    · rfl
    · rintro ⟨k,h⟩
      cases k with
      | inl i =>
          have hv := congrArg (fun x : Stack =>
            match x with | .inl z => z.val | .inr _ => 0) h
          simp [ticketEmbed, ticketSlot] at hv
          omega
      | inr i => fin_cases i; simp [ticketEmbed, ticketSlot] at h
  constructor
  · rw [outputBank, BitMachineStackEmbedding.bank_outside]
    · rfl
    · rintro ⟨k,h⟩
      cases k with
      | inl i =>
          have hv := congrArg (fun x : Stack =>
            match x with | .inl z => z.val | .inr _ => 0) h
          simp [ticketEmbed, ticketSlot] at hv
          omega
      | inr i => fin_cases i; simp [ticketEmbed, ticketSlot] at h
  · rw [outputBank, BitMachineStackEmbedding.bank_outside]
    · rfl
    · rintro ⟨k,h⟩
      cases k with
      | inl i =>
          have hv := congrArg (fun x : Stack =>
            match x with | .inl z => z.val | .inr _ => 0) h
          simp [ticketEmbed, ticketSlot] at hv
          omega
      | inr i => fin_cases i; simp [ticketEmbed, ticketSlot] at h

#print axioms loaded_source_ticket
#print axioms output_tape
#print axioms output_ticket
#print axioms output_draw_work_empty
#print axioms output_outer_work_empty
#print axioms output_inner
#print axioms output_saved

end
end Paper2.LoadedTicketMachine
