import EthInapproximability.CurrentPaper.SourceClausePairGateCleanup

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateCycle

open Turing BitMachineEncoding
open SourceBooleanEncoding EncodedCNF
open scoped Classical

abbrev Stack := PairUnitLift.Stack

noncomputable def firstProgram (bit ell : Fin 2) (sign : Bool)
    (w : Nat) :=
  BitMachineRawSequence.program (PairGatePrep.program bit ell w)
    (PairGateExecute.program sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (((((), ((), none)), ((), none)), none), ())
    PairGateExecute.gateControl

noncomputable def program (bit ell : Fin 2) (sign : Bool)
    (w : Nat) :=
  BitMachineRawSequence.program (firstProgram bit ell sign w)
    PairGateCleanup.program (.clear 0)
    ((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl) ((), none)

theorem run {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) :
    let bit := if ell = 0 then s else t
    let sign := if ell = 0 then PairSignedGate.signFirst s t
      else PairSignedGate.signSecond s t
    ∃ T ≤ PrefixGateOperands.preparationCost bit.val (width 2 q + 1)
        (List.replicate v.val true) +
      (v.val + bit.val + 4) +
      (2 * (pairOrdinal v s t) + 2) +
      (PairGatePatch.offsetSize ell 0 + 2) + 3 +
      SourceClauseRowGate.cost v.val 2 bit.val n ell.val
        (pairOrdinal v s t) (width 2 q + 1) sign + 1 +
      PrefixSharedClear.cost (PairGateCleanup.localBank (q := q)
        v s t ell saved output count) + 1,
      ((advance (program bit ell sign (width 2 q + 1)))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (SourceClauseFixedBatch.labelAt
                      (PrefixGateOperands.constantSize bit.val
                        (width 2 q + 1)) 0))))))),
          (((((((), ((), none)), ((), none)), none), ()),
            PairGateExecute.gateControl), ((), none)),
          PairUnitLift.pairBank n v.val (pairOrdinal v s t)
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (((((((), ((), none)), ((), none)), none), ()),
            PairGateExecute.gateControl), ((), none)),
          PairUnitLift.pairBank n v.val (pairOrdinal v s t)
            ((clauseFields (PairSignedGate.emittedGate (q := q)
              v s t ell)).reverse ++ saved)
            output (true :: true :: true :: count)⟩ := by
  dsimp
  let bit : Fin 2 := if ell = 0 then s else t
  let sign : Bool := if ell = 0 then PairSignedGate.signFirst s t
    else PairSignedGate.signSecond s t
  let B0 := PairUnitLift.pairBank n v.val (pairOrdinal v s t)
    saved output count
  let B1 := PairGatePrep.ready (q := q) v bit ell (pairOrdinal v s t)
    saved output count
  let B2 := PairGateExecute.finished (q := q) v s t ell
    saved output count
  let B3 := PairUnitLift.pairBank n v.val (pairOrdinal v s t)
    ((clauseFields (PairSignedGate.emittedGate (q := q)
      v s t ell)).reverse ++ saved)
    output (true :: true :: true :: count)
  obtain ⟨a, ha, hA⟩ := PairGatePrep.run (q := q) v bit ell
    (pairOrdinal v s t) saved output count
  obtain ⟨b, hb, hB⟩ := PairGateExecute.run (q := q) v s t ell
    saved output count
  obtain ⟨c, hc, hC⟩ := PairGateCleanup.run (q := q) v s t ell
    saved output count
  obtain ⟨u, hu, hU⟩ := BitMachineRawSequence.runs
    (PairGatePrep.program bit ell (width 2 q + 1))
    (PairGateExecute.program sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (PrefixGateOperands.constantSize bit.val
                (width 2 q + 1)) 0)))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (((((), ((), none)), ((), none)), none), ())
    (((((), ((), none)), ((), none)), none), ())
    PairGateExecute.gateControl PairGateExecute.gateControl
    B0 B1 B2 a b hA hB
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (firstProgram bit ell sign (width 2 q + 1))
    PairGateCleanup.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (PrefixGateOperands.constantSize bit.val
                  (width 2 q + 1)) 0))))))
    (.clear 0)
    ((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl)
    ((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl)
    ((), none) ((), none)
    B0 B2 B3 u c hU hC
  exact ⟨T, by dsimp [bit, sign] at ha hb; omega,
    by simpa only [program, B0, B3] using hrun⟩

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateCycle
