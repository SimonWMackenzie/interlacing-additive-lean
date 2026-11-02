import CurrentAdditive.RoundedPrepare
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! One fixed loaded rounded draw from public unary a,b and a fresh bit tape.
The canonical binary alphabet and rounded workspace are produced physically.
The final result uses the existing exact unary finCodec. -/

namespace EthInapproximability.CurrentPaper.RoundedLoadedDraw

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := RoundedPrepare.Stack
abbrev Label := BitMachineRawSequence.Label RoundedPrepare.Label RoundedCleanDraw.Label
abbrev Control := RoundedPrepare.Control × RoundedCleanDraw.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def drawEmbed : RoundedCleanDraw.Stack ↪ Stack :=
  ⟨Sum.inl, by intro i j h; exact Sum.inl_injective h⟩

def drawProgram (l : RoundedCleanDraw.Label) := stackStmt drawEmbed (RoundedCleanDraw.program l)

def initial : Control := (RoundedPrepare.initial, RoundedCleanDraw.initial)

def program := BitMachineRawSequence.program RoundedPrepare.program drawProgram
  (.ticket (.rounded .load)) RoundedPrepare.initial RoundedCleanDraw.initial

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def start (a b : ℕ) (tape : List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel (.copy .fuel .scan)), initial,
    RoundedPrepare.initialBank a b tape⟩

def finalBank (a b : ℕ) (input suffix result : List Bool) : Stack → List Bool :=
  bank drawEmbed (RoundedPrepare.finalBank a b input) (RoundedCleanDraw.cleanBank suffix result)

def clock (a b : ℕ) : ℕ := RoundedPrepare.clock a b +
  RoundedCleanDraw.clock a.bits (List.replicate b false) + 1

theorem physical_word (a b : ℕ) (ha : 0 < a) (word suffix : List Bool)
    (hlen : word.length = b) :
    ∃ t ≤ RoundedPrepare.clock a b + RoundedCleanDraw.clock a.bits word + 1,
      run t (start a b (word ++ suffix)) =
        ⟨none, initial, finalBank a b (word ++ suffix) suffix
          (List.replicate (EncodedCommunication.bitsValue
            (RoundedMachine.outputWord a.bits word)) true ++ [false])⟩ := by
  obtain ⟨u, hu, hprepare⟩ := RoundedPrepare.physical_prepare a b (word ++ suffix)
  obtain ⟨v, hv, hdraw⟩ := RoundedCleanDraw.physical_clean a.bits word suffix
    (by simpa [EncodedCommunication.bitsValue_bits] using ha)
  let S := RoundedPrepare.finalBank a b (word ++ suffix)
  have hbank : bank drawEmbed S (RoundedCleanDraw.start a.bits word suffix a).stk = S := by
    apply bank_eq_self
    intro k
    exact congrFun (RoundedPrepare.rounded_start_bank a b word suffix hlen) k |>.symm
  have hd := BitMachineStackRun.run drawEmbed S RoundedCleanDraw.program
    (RoundedCleanDraw.start a.bits word suffix a) v
  have hr : RoundedCleanDraw.run v (RoundedCleanDraw.start a.bits word suffix a) =
      ⟨none, RoundedCleanDraw.initial, RoundedCleanDraw.cleanBank suffix
        (List.replicate (EncodedCommunication.bitsValue (RoundedMachine.outputWord a.bits word))
          true ++ [false])⟩ := by
    simpa only [EncodedCommunication.bitsValue_bits] using hdraw
  change (((advance RoundedCleanDraw.program)^[v]) _) = _ at hr
  rw [hr] at hd
  have hd' : ((advance drawProgram)^[v])
      (⟨some (.ticket (.rounded .load)), RoundedCleanDraw.initial, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, RoundedCleanDraw.initial,
        finalBank a b (word ++ suffix) suffix
          (List.replicate (EncodedCommunication.bitsValue
            (RoundedMachine.outputWord a.bits word)) true ++ [false])⟩ := by
    change ((advance drawProgram)^[v])
      ⟨some (.ticket (.rounded .load)), RoundedCleanDraw.initial,
        bank drawEmbed S (RoundedCleanDraw.start a.bits word suffix a).stk⟩ = _ at hd
    rw [hbank] at hd
    exact hd
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs RoundedPrepare.program drawProgram
    (.copy .fuel .scan) (.ticket (.rounded .load))
    RoundedPrepare.initial RoundedPrepare.initial RoundedCleanDraw.initial RoundedCleanDraw.initial
    (RoundedPrepare.initialBank a b (word ++ suffix)) S
    (finalBank a b (word ++ suffix) suffix
      (List.replicate (EncodedCommunication.bitsValue
        (RoundedMachine.outputWord a.bits word)) true ++ [false])) u v hprepare hd'
  exact ⟨t, by omega, hrun⟩

theorem physical_finCodec (a b : ℕ) (ha : 0 < a)
    (bits : Fin b → Bool) (suffix : List Bool) :
    ∃ t ≤ RoundedPrepare.clock a b +
        RoundedCleanDraw.clock a.bits (Paper2.CappedTicketMachine.ticketWord bits) + 1,
      run t (start a b (Paper2.CappedTicketMachine.ticketWord bits ++ suffix)) =
        ⟨none, initial, finalBank a b
          (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) suffix
          ((Paper2.RecursiveLabelCodecScratch.finCodec a).encode
            (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
              (Paper2.CappedSampler.bitsTicketEquiv b bits)))⟩ := by
  obtain ⟨t, ht, hr⟩ := physical_word a b ha
    (Paper2.CappedTicketMachine.ticketWord bits) suffix
    (Paper2.CappedTicketMachine.ticketWord_length bits)
  exact ⟨t, ht, by simpa only [RoundedMachine.output_matches_draw a b ha bits] using hr⟩

#print axioms physical_word
#print axioms physical_finCodec

end
end EthInapproximability.CurrentPaper.RoundedLoadedDraw
