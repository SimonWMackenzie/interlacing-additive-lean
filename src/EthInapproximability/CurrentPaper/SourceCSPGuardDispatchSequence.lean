import EthInapproximability.CurrentPaper.SourceCSPGuardDispatch

/-!
# Ordinary raw input through finite CSP branch dispatch

The physical input-length/header/count/status controller is sequenced with
the physical reject/zero/positive branch selector on the same stack bank.
The terminal tag still needs the corresponding output or row-loop machine.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGuardDispatchSequence

open Turing BitMachineEncoding

abbrev Stack := SourceCSPInputFrame.Stack
abbrev HeaderLabel (a q : Nat) := BitMachineRawSequence.Label
  (SourceCSPGuardStatusSequence.GuardLabel a q) Unit
abbrev HeaderControl :=
  SourceCSPGuardStatusSequence.GuardControl × SourceCSPGuardStatus.Control

def headerStart (a q : Nat) : HeaderLabel a q :=
  .inl (SourceCSPGuardStatusSequence.guardStart a q)

def headerInitial : HeaderControl :=
  (SourceCSPGuardStatusSequence.guardInitial, (none, none))

def program (a q : Nat) :=
  BitMachineRawSequence.program
    (SourceCSPGuardStatusSequence.program a q)
    SourceCSPGuardDispatch.program .status
    headerInitial SourceCSPGuardDispatch.initialControl

def bound (a q L : Nat) : Nat :=
  SourceCSPGuardStatusSequence.bound a q L + 6

/-- On every raw input, the single finite program halts with the exact
branch tag prescribed by the literally parsed status and stack operands.
No row or clause-output claim is included here. -/
theorem all_input (a q : Nat) (input : List Bool) :
    ∃ (t : Nat) (S : Stack → List Bool) (S₀ : Stack → List Bool)
      (v : SourceCSPGuardDispatch.Control) (wa wq word : List Bool),
      t ≤ bound a q input.length ∧
      ((advance (program a q))^[t])
        (⟨some (.inl (headerStart a q)),
          (headerInitial, SourceCSPGuardDispatch.initialControl),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label (HeaderLabel a q)
              SourceCSPGuardDispatch.Label)
            (HeaderControl × SourceCSPGuardDispatch.Control)) =
        ⟨none, (headerInitial, v), S⟩ ∧
      v.2 = some (SourceCSPGuardDispatch.classify
        ((SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)) &&
          decide (EncodedCommunication.bitsValue word ≤ input.length))
        (S₀ SourceCSPGuardDispatch.vertexSlot)
        (S₀ SourceCSPGuardDispatch.countSlot)
        (S₀ SourceCSPGuardDispatch.sourceSlot)) := by
  obtain ⟨th, Sh, vh, wa, wq, word, hth, hrh, hstatus, _⟩ :=
    SourceCSPGuardStatusSequence.all_input a q input
  let good := (SourceCSPHeaderValidFlag.parserGood input &&
      decide (wq = q.bits) && decide (wa = a.bits)) &&
      decide (EncodedCommunication.bitsValue word ≤ input.length)
  have hshape : ∃ tail, Sh SourceCSPGuardDispatch.statusSlot = good :: tail := by
    change (Sh SourceCSPGuardStatus.statusSlot).head? = some good at hstatus
    cases hcell : Sh SourceCSPGuardStatus.statusSlot with
    | nil => simp [hcell] at hstatus
    | cons b tail =>
        have hb : b = good := by
          simpa only [hcell, List.head?_cons,
            Option.some.injEq] using hstatus
        subst b
        exact ⟨tail, by simpa only [SourceCSPGuardDispatch.statusSlot] using hcell⟩
  obtain ⟨tail, hshape⟩ := hshape
  obtain ⟨td, htd, hdhalt, hdout⟩ :=
    SourceCSPGuardDispatch.total Sh good tail hshape
  let cd := SourceCSPGuardDispatch.run td Sh
  change cd.l = none at hdhalt
  have hrd : ((advance SourceCSPGuardDispatch.program)^[td])
      (⟨some .status, SourceCSPGuardDispatch.initialControl, Sh⟩ :
        SourceCSPGuardDispatch.Config) =
      ⟨none, cd.var, cd.stk⟩ := by
    change cd = ⟨none, cd.var, cd.stk⟩
    cases hcd : cd with
    | mk l v s =>
        cases l with
        | none => rfl
        | some l =>
            have hx : some l = (none : Option SourceCSPGuardDispatch.Label) := by
              simpa only [hcd] using hdhalt
            cases hx
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPGuardStatusSequence.program a q)
    SourceCSPGuardDispatch.program
    (headerStart a q) .status headerInitial
    (SourceCSPGuardStatusSequence.guardInitial, vh)
    SourceCSPGuardDispatch.initialControl cd.var
    (SourceCSPInputFrame.initial input) Sh cd.stk th td
    (by simpa only [headerStart, headerInitial] using hrh) hrd
  refine ⟨t, cd.stk, Sh, cd.var, wa, wq, word, ?_, ?_, ?_⟩
  · dsimp only [bound]
    omega
  · simpa only [program] using hr
  · exact hdout

end EthInapproximability.CurrentPaper.SourceCSPGuardDispatchSequence
