import EthInapproximability.CurrentPaper.SourceCSPInputGuarded
import EthInapproximability.CurrentPaper.SourceCSPInputGrowth

/-!
# Uniform raw-input transition bound for the guarded CSP header

The parsed constraint-count word is bounded by finite-program stack growth,
even when the raw bitstream is malformed. Thus the guard's variable-word
charge is replaced by an explicit fixed-parameter polynomial in raw length.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPInputGuardedPoly

open Turing BitMachineEncoding
open SourceCSPInputGuarded

def polyBound (a q L : Nat) : Nat :=
  inputBound a q L +
    guardBound (SourceCSPInputGrowth.growthConstant a q * inputBound a q L) L + 1

private theorem guardBound_mono {W W' L : Nat} (h : W ≤ W') :
    guardBound W L ≤ guardBound W' L := by
  have hm := Nat.mul_le_mul_left (L + 1)
    (show 4 * W + 5 ≤ 4 * W' + 5 by omega)
  unfold guardBound
  omega

/-- The actual combined finite machine checks both header and `m ≤ |input|`
on every raw Boolean input within a uniform fixed-parameter polynomial.
This does not yet check rows or emit the ordered 3CNF. -/
theorem all_input (a q : Nat) (input : List Bool) :
    ∃ t S v wa wq word,
      t ≤ polyBound a q input.length ∧
      ((advance (program a q))^[t])
        (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
          ((((none, none),
            (((((none, none), none), none), (none, none, none))))),
            ((none, none), (none, false))),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label BitMachineCopy.Label
                  SourceInputLengthUnary.CountLabel)
                (SourceCSPInputValid.HeaderLabel a q))
              SourceCSPQueryRange.Label)
            (HeaderControl × SourceCSPQueryRange.Control)) =
        ⟨none,
          ((((none, none),
            (((((none, none), none), none), (none, none, none))))), v), S⟩ ∧
      S FlagSlot =
        [SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)] ∧
      S (.inr 6) =
        ProtocolBoundedUnary.result word
          (List.replicate input.length true) [] ∧
      S (.inl (.inl (.inl 1))) = word ∧
      S (.inr 2) = List.replicate input.length true := by
  obtain ⟨th, Sh, vh, wa, wq, hth, hrh, hflag, hcap, hunused, hwordBound⟩ :=
    SourceCSPInputGrowth.word_length_bound a q input
  let word := Sh (.inl (.inl (.inl 1)))
  let cap := List.replicate input.length true
  have hready : SourceCSPConstraintGuard.Ready Sh word cap := by
    refine ⟨rfl, hcap, ?_, ?_, ?_, ?_⟩
    · exact hunused 3 (by decide)
    · exact hunused 4 (by decide)
    · exact hunused 5 (by decide)
    · exact hunused 6 (by decide)
  obtain ⟨tg, vg, Sg, htg, hrg, hword, hcapg, hresult, _, _⟩ :=
    SourceCSPConstraintGuard.guard_total word cap Sh hready
  have hflagG : Sg FlagSlot = Sh FlagSlot := by
    have h := guard_preserves_flag Sh tg
    rw [hrg] at h
    exact h
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPInputValid.inputProgram a q)
    SourceCSPConstraintGuard.guardProgram
    (.inl (.inl BitMachineCopy.Label.scan) :
      BitMachineRawSequence.Label
        (BitMachineRawSequence.Label BitMachineCopy.Label
          SourceInputLengthUnary.CountLabel)
        (SourceCSPInputValid.HeaderLabel a q))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) :
      SourceCSPQueryRange.Label)
    (((none, none),
      (((((none, none), none), none), (none, none, none)))) : HeaderControl)
    ((none, none), vh)
    (((none, none), (none, false)) : SourceCSPQueryRange.Control) vg
    (SourceCSPInputFrame.initial input) Sh Sg th tg hrh hrg
  refine ⟨t, Sg, vg, wa, wq, word, ?_, ?_, ?_, hresult, hword, hcapg⟩
  · have hword' : word.length ≤
        SourceCSPInputGrowth.growthConstant a q * inputBound a q input.length := by
      simpa only [word, inputBound, SourceCSPInputGrowth.headerBound] using hwordBound
    have hg := guardBound_mono (L := input.length) hword'
    have hth' : th ≤ inputBound a q input.length := by
      simpa only [inputBound, SourceCSPInputGrowth.headerBound] using hth
    have htg' : tg ≤ guardBound word.length input.length := by
      simpa only [cap, List.length_replicate, guardBound] using htg
    unfold polyBound
    omega
  · simpa only [program] using hr
  · exact hflagG.trans hflag

end EthInapproximability.CurrentPaper.SourceCSPInputGuardedPoly
