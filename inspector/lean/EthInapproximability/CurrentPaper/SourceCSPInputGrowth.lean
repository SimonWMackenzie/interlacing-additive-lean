import EthInapproximability.CurrentPaper.SourceCSPInputValid
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
# Parsed header-word size from physical transition growth

No arbitrary bitstream can cause the actual finite header controller to
create a long `m` stack in fewer than the charged number of transitions.
This supplies the missing raw-input polynomial bound without assuming the
bitstream is well formed.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPInputGrowth

open Turing BitMachineEncoding

def mSlot : SourceCSPInputFrame.Stack := .inl (.inl (.inl 1))

def headerBound (a q L : Nat) : Nat :=
  3 * L + 4 + 4 * (2 * L + 4) + 3 +
    (a.bits.length + 1) + (q.bits.length + 1) + 5

def growthConstant (a q : Nat) : Nat :=
  BitMachineStackGrowth.perStep (SourceCSPInputValid.inputProgram a q)

theorem word_length_from_run (a q : Nat) (input : List Bool) (t : Nat)
    (S : SourceCSPInputFrame.Stack → List Bool)
    (v : SourceCSPInputValid.HeaderControl)
    (hrun : ((advance (SourceCSPInputValid.inputProgram a q))^[t])
        (⟨some (.inl (.inl BitMachineCopy.Label.scan)),
          ((none, none),
            ((((none, none), none), none), (none, none, none))),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label
                SourceInputLengthUnary.CountLabel)
              (SourceCSPInputValid.HeaderLabel a q))
            ((Option Bool × Option Bool) × SourceCSPInputValid.HeaderControl)) =
        ⟨none, ((none, none), v), S⟩) :
    (S mSlot).length ≤ growthConstant a q * t := by
  have hg := BitMachineStackGrowth.run_growth
    (SourceCSPInputValid.inputProgram a q)
    (⟨some (.inl (.inl BitMachineCopy.Label.scan)),
      ((none, none),
        ((((none, none), none), none), (none, none, none))),
      SourceCSPInputFrame.initial input⟩ :
      TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
        (BitMachineRawSequence.Label
          (BitMachineRawSequence.Label BitMachineCopy.Label
            SourceInputLengthUnary.CountLabel)
          (SourceCSPInputValid.HeaderLabel a q))
        ((Option Bool × Option Bool) × SourceCSPInputValid.HeaderControl))
    t mSlot
  rw [hrun] at hg
  simpa [growthConstant, mSlot, SourceCSPInputFrame.initial,
    SourceCSPHeaderCheck.parserInitial,
    SourceCSPRowController.contents] using hg

theorem word_length_bound (a q : Nat) (input : List Bool) :
    ∃ t S v wa wq,
      t ≤ headerBound a q input.length ∧
      ((advance (SourceCSPInputValid.inputProgram a q))^[t])
        (⟨some (.inl (.inl BitMachineCopy.Label.scan)),
          ((none, none),
            ((((none, none), none), none), (none, none, none))),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label
                SourceInputLengthUnary.CountLabel)
              (SourceCSPInputValid.HeaderLabel a q))
            ((Option Bool × Option Bool) × SourceCSPInputValid.HeaderControl)) =
        ⟨none, ((none, none), v), S⟩ ∧
      S (.inl SourceCSPHeaderValidFlag.flagSlot) =
        [SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)] ∧
      S (.inr 2) = List.replicate input.length true ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = []) ∧
      (S mSlot).length ≤ growthConstant a q * headerBound a q input.length := by
  obtain ⟨t, S, v, wa, wq, ht, hr, hf, hc, hu⟩ :=
    SourceCSPInputValid.all_input a q input
  have ht' : t ≤ headerBound a q input.length := by
    simpa only [headerBound] using ht
  have hw := word_length_from_run a q input t S v hr
  refine ⟨t, S, v, wa, wq, ht', hr, hf, hc, hu, ?_⟩
  exact hw.trans (Nat.mul_le_mul_left _ ht')

end EthInapproximability.CurrentPaper.SourceCSPInputGrowth
