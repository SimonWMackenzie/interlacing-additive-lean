import EthInapproximability.CurrentPaper.SourceCSPGuardStatus

/-!
# One all-input physical header guard and status collection program

The raw-input length/header/constraint-count machine is followed by one
literal Boolean-status collection transition on its existing stack bank.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGuardStatusSequence

open Turing BitMachineEncoding

abbrev Stack := SourceCSPInputFrame.Stack
abbrev GuardLabel (a q : Nat) := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label BitMachineCopy.Label
      SourceInputLengthUnary.CountLabel)
    (SourceCSPInputValid.HeaderLabel a q))
  SourceCSPQueryRange.Label
abbrev GuardControl :=
  SourceCSPInputGuarded.HeaderControl × SourceCSPQueryRange.Control

def guardStart (a q : Nat) : GuardLabel a q :=
  .inl (.inl (.inl BitMachineCopy.Label.scan))

def guardInitial : GuardControl :=
  ((((none, none),
    (((((none, none), none), none), (none, none, none))))),
    ((none, none), (none, false)))

def program (a q : Nat) :=
  BitMachineRawSequence.program (SourceCSPInputGuarded.program a q)
    SourceCSPGuardStatus.program () (guardInitial) (none, none)

def bound (a q L : Nat) : Nat :=
  SourceCSPInputGuardedPoly.polyBound a q L + 2

/-- The raw-input header and count guards are combined by an actual final
transition. The leading bit of the final status cell is their conjunction;
the bounded-count output loses only its leading guard bit. -/
theorem all_input (a q : Nat) (input : List Bool) :
    ∃ t S v wa wq word,
      t ≤ bound a q input.length ∧
      ((advance (program a q))^[t])
        (⟨some (.inl (guardStart a q)),
          (guardInitial, (none, none)),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label (GuardLabel a q) Unit)
            (GuardControl × SourceCSPGuardStatus.Control)) =
        ⟨none, (guardInitial, v), S⟩ ∧
      (S SourceCSPGuardStatus.statusSlot).head? =
        some ((SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)) &&
          decide (EncodedCommunication.bitsValue word ≤ input.length)) ∧
      S SourceCSPGuardStatus.guardSlot =
        List.replicate (min (EncodedCommunication.bitsValue word)
          input.length) true := by
  obtain ⟨th, Sh, vh, wa, wq, word, hth, hrh, hflag, hresult, _, _⟩ :=
    SourceCSPInputGuardedPoly.all_input a q input
  let h := SourceCSPHeaderValidFlag.parserGood input &&
    decide (wq = q.bits) && decide (wa = a.bits)
  let g := decide (EncodedCommunication.bitsValue word ≤ input.length)
  let unary := List.replicate
    (min (EncodedCommunication.bitsValue word) input.length) true
  have hresult' : Sh SourceCSPGuardStatus.guardSlot = g :: unary := by
    simpa [SourceCSPGuardStatus.guardSlot, ProtocolBoundedUnary.result,
      g, unary] using hresult
  let c := advance SourceCSPGuardStatus.program
    (⟨some (), (none, none), Sh⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Unit SourceCSPGuardStatus.Control)
  have hc := SourceCSPGuardStatus.collect_step Sh h g unary hflag hresult'
  have hcb : c.l = none ∧
      c.stk SourceCSPGuardStatus.statusSlot =
        (h && g) :: Sh SourceCSPGuardStatus.statusSlot ∧
      c.stk SourceCSPGuardStatus.guardSlot = unary := by
    simpa only [c] using ⟨hc.1, hc.2.1, hc.2.2.1⟩
  have hrcollect : ((advance SourceCSPGuardStatus.program)^[1])
      (⟨some (), (none, none), Sh⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit SourceCSPGuardStatus.Control) =
      ⟨none, c.var, c.stk⟩ := by
    change c = ⟨none, c.var, c.stk⟩
    cases hcv : c with
    | mk l v s =>
        cases l with
        | none => rfl
        | some l =>
            have hx : some l = (none : Option Unit) := by
              simpa only [hcv] using hcb.1
            cases hx
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPInputGuarded.program a q) SourceCSPGuardStatus.program
    (guardStart a q) () guardInitial
    (((((none, none),
      (((((none, none), none), none), (none, none, none))))), vh) : GuardControl)
    ((none, none) : SourceCSPGuardStatus.Control) c.var
    (SourceCSPInputFrame.initial input) Sh c.stk th 1
    (by simpa only [guardStart, guardInitial] using hrh) hrcollect
  refine ⟨t, c.stk, c.var, wa, wq, word, ?_, ?_, ?_, ?_⟩
  · dsimp only [bound]
    omega
  · simpa only [program] using hr
  · simpa only [h, g] using congrArg List.head? hcb.2.1
  · exact hcb.2.2

end EthInapproximability.CurrentPaper.SourceCSPGuardStatusSequence
