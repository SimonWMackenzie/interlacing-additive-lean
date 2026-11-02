import CurrentAdditive.RoundedLoadedClock
import Paper2.CodeAdminReady
import Paper2.CodeHeaderDraw

/-! Actual rounded loaded draw in the physical generic Code interpreter bank.
Only the existing header layout is reused; the capped sampler is never called.
The four shared banks are unary alphabet, unary width, random tape and result.
Every remaining local arithmetic stack is private and initially empty. -/

namespace EthInapproximability.CurrentPaper.RoundedCodeDraw

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev OldStack := Paper2.CodeHeaderDraw.Stack
abbrev LocalStack := RoundedLoadedDraw.Stack
abbrev Stack := OldStack ⊕ LocalStack

def oldTape : OldStack := Paper2.CodeHeaderDraw.d 0
def oldWidth : OldStack := Paper2.CodeHeaderDraw.d 11
def oldAlphabet : OldStack := Paper2.CodeHeaderDraw.h 1
def oldResult : OldStack := Paper2.CodeHeaderDraw.d 15

def slot (k : LocalStack) : Stack :=
  if k = RoundedPrepare.publicA then .inl oldAlphabet else
  if k = RoundedPrepare.publicB then .inl oldWidth else
  if k = RoundedPrepare.tape then .inl oldTape else
  if k = RoundedPrepare.output then .inl oldResult else .inr k

theorem slot_injective : Function.Injective slot := by
  intro i j h
  unfold slot at h
  split_ifs at h <;> simp_all [oldAlphabet, oldWidth, oldTape, oldResult,
    Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.h]

def includeDraw : LocalStack ↪ Stack := ⟨slot, slot_injective⟩

abbrev Label := RoundedLoadedDraw.Label
abbrev Control := RoundedLoadedDraw.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program (l : Label) := stackStmt includeDraw (RoundedLoadedDraw.program l)
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def inputBank (S : OldStack → List Bool) : Stack → List Bool :=
  Sum.elim S (fun _ => [])

def start (S : OldStack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel (.copy .fuel .scan)),
    RoundedLoadedDraw.initial, inputBank S⟩

def resultBank (S : OldStack → List Bool) (a b : ℕ)
    (input suffix result : List Bool) : Stack → List Bool :=
  bank includeDraw (inputBank S) (RoundedLoadedDraw.finalBank a b input suffix result)

theorem input_bank (S : OldStack → List Bool) (a b : ℕ) (bits : List Bool)
    (ha : S oldAlphabet = List.replicate a true)
    (hb : S oldWidth = List.replicate b true)
    (ht : S oldTape = bits) (ho : S oldResult = []) :
    bank includeDraw (inputBank S) (RoundedPrepare.initialBank a b bits) = inputBank S := by
  apply bank_eq_self
  intro k
  change RoundedPrepare.initialBank a b bits k = inputBank S (slot k)
  unfold slot RoundedPrepare.initialBank
  split_ifs <;> subst_vars <;>
    simp_all [inputBank, RoundedPrepare.publicA, RoundedPrepare.publicB,
      RoundedPrepare.tape, RoundedPrepare.output, RoundedCleanDraw.output,
      RoundedCleanDraw.tape]

theorem physical_finCodec (S : OldStack → List Bool) (a b : ℕ) (ha : 0 < a)
    (bits : Fin b → Bool) (suffix : List Bool)
    (hA : S oldAlphabet = List.replicate a true)
    (hB : S oldWidth = List.replicate b true)
    (hT : S oldTape = Paper2.CappedTicketMachine.ticketWord bits ++ suffix)
    (hO : S oldResult = []) :
    ∃ t ≤ RoundedLoadedClock.coefficient * (a + b + 2) ^ 2,
      run t (start S) =
        ⟨none, RoundedLoadedDraw.initial, resultBank S a b
          (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) suffix
          ((Paper2.RecursiveLabelCodecScratch.finCodec a).encode
            (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
              (Paper2.CappedSampler.bitsTicketEquiv b bits)))⟩ := by
  obtain ⟨t, ht, hr⟩ := RoundedLoadedClock.physical_finCodec a b ha bits suffix
  have h := BitMachineStackRun.run includeDraw (inputBank S) RoundedLoadedDraw.program
    (RoundedLoadedDraw.start a b (Paper2.CappedTicketMachine.ticketWord bits ++ suffix)) t
  change ((advance RoundedLoadedDraw.program)^[t]) _ = _ at hr
  rw [hr] at h
  change run t
      ⟨some (BitMachineRawSequence.leftLabel (.copy .fuel .scan)),
        RoundedLoadedDraw.initial,
        bank includeDraw (inputBank S)
          (RoundedPrepare.initialBank a b (Paper2.CappedTicketMachine.ticketWord bits ++ suffix))⟩ = _ at h
  rw [input_bank S a b _ hA hB hT hO] at h
  exact ⟨t, ht, h⟩

#print axioms physical_finCodec

end
end EthInapproximability.CurrentPaper.RoundedCodeDraw
