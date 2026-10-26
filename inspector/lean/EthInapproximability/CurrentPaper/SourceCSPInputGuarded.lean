import EthInapproximability.CurrentPaper.SourceCSPInputValid
import EthInapproximability.CurrentPaper.SourceCSPConstraintGuard
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# All-input header flag through the physical bounded constraint guard

The raw input is counted and its fixed header is checked, then the arbitrary
binary `m` word is compared against the unary raw length. The guard has
disjoint stack support from the fixed-header flag.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPInputGuarded

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPInputFrame.Stack
abbrev FlagSlot : Stack := .inl SourceCSPHeaderValidFlag.flagSlot

private theorem embedded_outside {K J L V : Type*}
    [DecidableEq K] [DecidableEq J]
    (ι : K ↪ J) (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (l : L) (v : V) (before : J → List Bool) (t : Nat) (j : J)
    (hj : ¬ ∃ k, ι k = j) :
    (((advance (fun l => stmt ι id id id none (P l)))^[t])
      (⟨some l, v, before⟩ : TM2.Cfg (fun _ : J => Bool) L V)).stk j = before j := by
  let localCfg : TM2.Cfg (fun _ : K => Bool) L V :=
    ⟨some l, v, fun k => before (ι k)⟩
  have hstart : stackCfg ι before localCfg =
      (⟨some l, v, before⟩ : TM2.Cfg (fun _ : J => Bool) L V) := by
    simp only [stackCfg, localCfg, bank_restrict]
  rw [← hstart]
  change (((advance (fun l => stackStmt ι
      (BitMachineInline.stmt id id id none (P l))))^[t])
      (stackCfg ι before localCfg)).stk j = before j
  rw [BitMachineStackRun.run]
  exact bank_outside ι before _ j hj

theorem guard_preserves_flag (before : Stack → List Bool) (t : Nat) :
    (((advance SourceCSPConstraintGuard.guardProgram)^[t])
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
        ((none, none), (none, false)), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SourceCSPQueryRange.Label
          SourceCSPQueryRange.Control)).stk FlagSlot = before FlagSlot := by
  have h := embedded_outside SourceCSPConstraintGuard.guardEmbedding
    SourceCSPQueryRange.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((none, none), (none, false)) before t FlagSlot (by
      rintro ⟨k, hk⟩
      fin_cases k <;> simp [SourceCSPConstraintGuard.guardEmbedding,
        FlagSlot, SourceCSPHeaderValidFlag.flagSlot] at hk)
  simpa only [SourceCSPConstraintGuard.guardProgram] using h

abbrev HeaderControl :=
  ((Option Bool × Option Bool) × SourceCSPInputValid.HeaderControl)

def program (a q : Nat) :=
  BitMachineRawSequence.program (SourceCSPInputValid.inputProgram a q)
    SourceCSPConstraintGuard.guardProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (((none, none),
      (((((none, none), none), none), (none, none, none)))) : HeaderControl)
    (((none, none), (none, false)) : SourceCSPQueryRange.Control)

def inputBound (a q L : Nat) : Nat :=
  3 * L + 4 + 4 * (2 * L + 4) + 3 +
    (a.bits.length + 1) + (q.bits.length + 1) + 5

def guardBound (W L : Nat) : Nat :=
  2 * W + 2 + (2 * L + 2) + 1 +
    (L + 1) * (4 * W + 5) + 1

/-- One finite machine reaches both header and constraint-count statuses on
arbitrary Boolean input. The charged bound still contains the parsed `m`
word length; bounding that word by raw input length is a separate needed
lemma before this can serve as a pointwise polynomial-runtime certificate. -/
theorem all_input (a q : Nat) (input : List Bool) :
    ∃ t S v wa wq word,
      t ≤ inputBound a q input.length +
        guardBound word.length input.length + 1 ∧
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
  obtain ⟨th, Sh, vh, wa, wq, hth, hrh, hflag, hcap, hunused⟩ :=
    SourceCSPInputValid.all_input a q input
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
  · change t ≤ inputBound a q input.length +
      guardBound word.length input.length + 1
    simp only [inputBound, guardBound] at *
    simp only [cap, List.length_replicate] at htg
    omega
  · simpa only [program] using hr
  · exact hflagG.trans hflag

end EthInapproximability.CurrentPaper.SourceCSPInputGuarded
