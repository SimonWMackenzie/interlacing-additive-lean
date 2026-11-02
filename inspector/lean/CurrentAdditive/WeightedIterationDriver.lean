import CurrentAdditive.WeightedIterationLoader
import CurrentAdditive.WeightedIterationClock
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Ordinary Bank2[stateword, unary rounds] driver. The machine, its program,
start and control depend only on the actual fixed one-step machine. -/

namespace CurrentAdditive.WeightedIterationDriver

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

noncomputable section
variable (M : BitMachine.Machine)

abbrev Stack := WeightedIterationLoader.Stack M

def loopSlots : BitMachineIteration.Stack M ↪ Stack M where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def loopProgram (l : BitMachineIteration.Label M) :=
  BitMachineStackEmbedding.stackStmt (loopSlots M) (BitMachineIteration.program M l)

def loopStart : BitMachineIteration.Label M := .inr .testFuel

def loopInitial : BitMachineIteration.Control M := (M.initial,none)

def program := BitMachineRawSequence.program (WeightedIterationLoader.program M)
  (loopProgram M) (loopStart M) none (loopInitial M)

abbrev Label := BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 2)
  (BitMachineIteration.Label M)
abbrev Control := Option Bool × BitMachineIteration.Control M

def start : Label M := BitMachineRawSequence.leftLabel (.scan 0)
def initial : Control M := (none,loopInitial M)

def machine : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack M) (.inl (.inl M.input)) (start M) (initial M) (program M)

def input (state : List Bool) (k : Nat) : List Bool :=
  WeightedIterationLoader.packet state (List.replicate k true)

def clock (states : Nat → List Bool) (b : Nat → Nat) (k : Nat) : Nat :=
  5*((input (states 0) k).length+1)+WeightedIterationClock.cumulative M states b k+1

theorem loop_run (states : Nat → List Bool) (b : Nat → Nat) (fuel : List Bool)
    (hstep : ∀ j < fuel.length, M.OutputsWithin (states j) (states (j+1)) (b j)) :
    ∃ t ≤ WeightedIterationClock.cumulative M states b fuel.length,
      ((advance (loopProgram M))^[t])
        (⟨some (loopStart M),loopInitial M,
          WeightedIterationLoader.readyBank M (states 0) fuel⟩ : TM2.Cfg _ _ _) =
        ⟨none,loopInitial M,Sum.elim
          (BitMachineIteration.finished M (states fuel.length)).stk (fun _ => [])⟩ := by
  obtain ⟨t,ht,hr⟩ := WeightedIterationClock.run M states b fuel hstep
  have hin : ∀ j,
      (BitMachineIteration.ready M (states 0) fuel).stk j =
      WeightedIterationLoader.readyBank M (states 0) fuel (loopSlots M j) := by
    intro j
    rfl
  have he := WeightedRawWords.region_run (loopSlots M) (BitMachineIteration.program M)
    _ _ _ hr (WeightedIterationLoader.readyBank M (states 0) fuel) hin
  refine ⟨t,ht,?_⟩
  change ((advance (loopProgram M))^[t]) _ = _ at he
  refine he.trans ?_
  congr 1
  funext j
  cases j with
  | inl j =>
      change BitMachineStackEmbedding.bank (loopSlots M) _ _ (loopSlots M j) = _
      rw [BitMachineStackEmbedding.bank_at]
      rfl
  | inr j =>
      rw [BitMachineStackEmbedding.bank_outside _ _ _ _ (by
        intro ⟨i,hi⟩
        cases hi)]
      rfl

theorem outputs (states : Nat → List Bool) (b : Nat → Nat) (k : Nat)
    (hstep : ∀ j < k, M.OutputsWithin (states j) (states (j+1)) (b j)) :
    (machine M).OutputsWithin (input (states 0) k) (states k) (clock M states b k) := by
  classical
  let fuel := List.replicate k true
  have hfuel : fuel.length=k := List.length_replicate
  obtain ⟨a,ha,hr⟩ := WeightedIterationLoader.parse M (states 0) fuel
  obtain ⟨btime,hb,hbr⟩ := loop_run M states b fuel (by simpa only [hfuel] using hstep)
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
    (WeightedIterationLoader.program M) (loopProgram M) (.scan 0) (loopStart M)
    none (some true) (loopInitial M) (loopInitial M)
    (WeightedIterationLoader.initialBank M (WeightedIterationLoader.packet (states 0) fuel))
    _ _ a btime hr hbr
  apply outputsWithin_of_raw_run (.inr 0 : Stack M) (.inl (.inl M.input))
    (start M) (initial M) (program M) (input (states 0) k) (states k)
    t (clock M states b k)
  · unfold clock
    change a ≤ 5*((input (states 0) k).length+1) at ha
    rw [hfuel] at hb
    omega
  · have hh := congrArg (fun c => c.l) he
    simpa only [program,start,initial,WeightedIterationLoader.initialBank,rawInit,input,fuel]
      using hh
  · have hout := congrArg (fun c => c.stk (.inl (.inl M.input) : Stack M)) he
    simpa only [program,start,initial,WeightedIterationLoader.initialBank,rawInit,input,fuel,
      Sum.elim_inl,BitMachineIteration.finished,BitMachine.Machine.init,↓reduceIte,
      hfuel] using hout

theorem outputs_uniform (states : Nat → List Bool) (k L T : Nat)
    (hstep : ∀ j < k, M.OutputsWithin (states j) (states (j+1)) T)
    (hlen : ∀ j < k, (states j).length ≤ L) :
    (machine M).OutputsWithin (input (states 0) k) (states k)
      (5*((input (states 0) k).length+1)+k*BitMachineIteration.roundBound M L T+2) := by
  have hr := outputs M states (fun _ => T) k hstep
  have hc := WeightedIterationClock.cumulative_le M states (fun _ => T) k L T
    hlen (by intros;exact le_rfl)
  apply BitMachine.outputsWithin_mono (machine M) hr
  unfold clock
  omega

#print axioms outputs
#print axioms outputs_uniform

end
end CurrentAdditive.WeightedIterationDriver
