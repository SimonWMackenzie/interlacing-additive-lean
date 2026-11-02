import Paper2.E6Cut
import Paper2.NPTruncRun
import Paper2.SelectedTape
import Paper2.BindMachine
-- a-eth-owner-6 copy of frozen a-eth-owner-5/E5Cls.lean (SHA-256 490ac41ff1df5308ccacf90b68cf78c98c4f7aebff67bd4eed3e6910972b5038); import lines renamed only.
-- root successor copy (29 September 2026, for the R22 batch): the docstring line citing a non-existent `clsTime_le` (a-eth-owner-5-audit defect D2) corrected; no other change.

/-!
# Paper A (lock v12), lane `owner:a-eth-5`, segment 2: the classifier stage

ONE fixed machine `clsStage C` for EVERY `SelectedTape.Algorithm C` (in particular the A27
`HeaderStrip.selectedClassifier E`): the admitted truncation program
`NPOwner1.Trunc.machine Bind.idMachine C.cR C.dR` (it computes `1^(C.tapeLength x)` from `x` inside
the fixed machine and keeps exactly that prefix of the block; admitted identity witness
`Bind.idMachine`), then `C.machine`. On `pair x c2` with `C.tapeLength x ≤ |c2|` it prints
`C.output x (c2.take (C.tapeLength x))` within `clsTime C |x| Y` for every `Y ≥ |c2|`
(`clsStage_outputs`); the handoff is charged by the admitted `composition_outputsWithin`.
`clsTime C |x| Y` is the explicit clock of that run; this module states no polynomial bound on it (the D-A6 budget is charged downstream, in `E6DecClock`).

No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth5

open EthInapproximability.CurrentPaper

/-- THE fixed classifier stage. -/
def clsStage (C : Paper2.SelectedTape.Algorithm) : BitMachine.Machine :=
  BitMachineComposition.composition
    (NPOwner1.Trunc.machine Paper2.SelectedTape.Bind.idMachine C.cR C.dR) C.machine

/-- The classifier stage clock: `X` = the header word length, `Y` = a bound on the block length. -/
def clsTime (C : Paper2.SelectedTape.Algorithm) (X Y : ℕ) : ℕ :=
  NPOwner1.Trunc.timeBound C.cR C.dR Paper2.SelectedTape.Bind.idC Paper2.SelectedTape.Bind.idD
      Paper2.SelectedTape.Bind.idMachine.pushBound (2 * X + 1 + Y) +
    2 * (2 * X + 1 + C.cR * (X + 1) ^ C.dR) + 2 + C.cT * (X + 1) ^ C.dT

theorem trunc_timeBound_mono (c d cf df pb : ℕ) {N N' : ℕ} (h : N ≤ N') :
    NPOwner1.Trunc.timeBound c d cf df pb N ≤ NPOwner1.Trunc.timeBound c d cf df pb N' := by
  unfold NPOwner1.Trunc.timeBound
  gcongr

/-- **Segment 2: the classifier stage runs `C` on the header word with its block.** -/
theorem clsStage_outputs (C : Paper2.SelectedTape.Algorithm) (x c2 : List Bool) (Y : ℕ)
    (hY : c2.length ≤ Y) (h : C.tapeLength x ≤ c2.length) :
    (clsStage C).OutputsWithin (EncodedComplexity.pair x c2)
      (C.output x (c2.take (C.tapeLength x))) (clsTime C x.length Y) := by
  have hpre := NPOwner1.Trunc.machine_outputs Paper2.SelectedTape.Bind.idMachine C.cR C.dR id
    Paper2.SelectedTape.Bind.idC Paper2.SelectedTape.Bind.idD Paper2.SelectedTape.Bind.idRuns
    (EncodedComplexity.pair x c2)
  rw [NPOwner1.Trunc.result_pair] at hpre
  simp only [id] at hpre
  have hword := Paper2.SelectedTape.Bind.ofFn_prefixFn c2 (C.tapeLength x) h
  have htarget : C.machine.OutputsWithin
      (EncodedComplexity.pair x (c2.take (C.tapeLength x)))
      (C.output x (c2.take (C.tapeLength x))) (C.cT * (x.length + 1) ^ C.dT) := by
    let P := fun v : List Bool => C.machine.OutputsWithin (EncodedComplexity.pair x v)
      (C.output x v) (C.cT * (x.length + 1) ^ C.dT)
    exact (congrArg P hword).mp (C.runs x (Paper2.SelectedTape.Bind.prefixFn c2 (C.tapeLength x) h))
  have hTL : C.tapeLength x = C.cR * (x.length + 1) ^ C.dR := rfl
  rw [← hTL] at hpre
  have hlen : (EncodedComplexity.pair x c2).length ≤ 2 * x.length + 1 + Y := by
    rw [EncodedComplexity.pair_length]; omega
  have hpre' := BitMachine.outputsWithin_mono _ hpre (trunc_timeBound_mono _ _ _ _ _ hlen)
  have hC := BitMachineComposition.composition_outputsWithin _ _ hpre' htarget
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hml : (EncodedComplexity.pair x (c2.take (C.tapeLength x))).length =
      2 * x.length + 1 + C.cR * (x.length + 1) ^ C.dR := by
    rw [EncodedComplexity.pair_length, List.length_take, Nat.min_eq_left h, hTL]
  rw [hml]
  unfold clsTime
  omega

end Paper2.AEth5

end

#print axioms Paper2.AEth5.trunc_timeBound_mono
#print axioms Paper2.AEth5.clsStage_outputs
