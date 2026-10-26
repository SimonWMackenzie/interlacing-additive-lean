import EthInapproximability.CurrentPaper.GenericPairGateCleanup

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateCycle

open Turing BitMachineEncoding
open SourceBooleanPrefix EncodedCNF
open scoped Classical

abbrev Stack := PairUnitLift.Stack

noncomputable def firstProgram {a : Nat} (bit : Fin a)
    (ell : Fin 2) (sign : Bool) (w : Nat) :=
  BitMachineRawSequence.program (PairGatePrep.program a bit ell w)
    (PairGateExecute.program sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (((((), ((), none)), ((), none)), none), ())
    PairGateExecute.gateControl

noncomputable def program {a : Nat} (bit : Fin a)
    (ell : Fin 2) (sign : Bool) (w : Nat) :=
  BitMachineRawSequence.program (firstProgram bit ell sign w)
    PairGateCleanup.program (.clear 0)
    ((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl) ((), none)

theorem run {n a : Nat} (v : Fin n) (bit : Fin a)
    (ell : Fin 2) (ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ T ≤ GateOperands.cost a bit.val w (List.replicate v.val true) +
      (v.val + bit.val + 4) + (2*ordinal+2) +
      (PairGatePatch.offsetSize ell 0 + 2) + 3 +
      SourceClauseRowGate.cost v.val a bit.val n ell.val ordinal w sign + 1 +
      PrefixSharedClear.cost (PairGateCleanup.localBank v bit ell.val
        ordinal w sign saved output count) + 1,
      ((advance (program bit ell sign w))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (SourceClauseFixedBatch.labelAt
                      (GateOperands.constantSize a bit.val w) 0))))))),
          (((((((), ((), none)), ((), none)), none), ()),
            PairGateExecute.gateControl), ((), none)),
          PairUnitLift.pairBank n v.val ordinal saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (((((((), ((), none)), ((), none)), none), ()),
            PairGateExecute.gateControl), ((), none)),
          PairUnitLift.pairBank n v.val ordinal
            ((clauseFields (PairGateCleanup.emitted v bit ell.val
              ordinal w sign)).reverse ++ saved)
            output (true :: true :: true :: count)⟩ := by
  let B0 := PairUnitLift.pairBank n v.val ordinal saved output count
  let B1 := PairGatePrep.ready v bit w ordinal ell.val saved output count
  let B2 := PairGateExecute.finished v bit ell.val ordinal w sign
    saved output count
  let B3 := PairUnitLift.pairBank n v.val ordinal
    ((clauseFields (PairGateCleanup.emitted v bit ell.val ordinal w sign)).reverse ++ saved)
    output (true :: true :: true :: count)
  obtain ⟨p, hp, hP⟩ := PairGatePrep.run v bit ell w ordinal saved output count
  obtain ⟨g, hg, hG⟩ := PairGateExecute.run v bit ell.val ordinal w sign
    saved output count
  obtain ⟨c, hc, hC⟩ := PairGateCleanup.run v bit ell.val ordinal w sign
    saved output count
  obtain ⟨u, hu, hU⟩ := BitMachineRawSequence.runs
    (PairGatePrep.program a bit ell w) (PairGateExecute.program sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (GateOperands.constantSize a bit.val w) 0)))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (((((), ((), none)), ((), none)), none), ())
    (((((), ((), none)), ((), none)), none), ())
    PairGateExecute.gateControl PairGateExecute.gateControl
    B0 B1 B2 p g hP hG
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (firstProgram bit ell sign w) PairGateCleanup.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (GateOperands.constantSize a bit.val w) 0))))))
    (.clear 0)
    ((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl)
    ((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl)
    ((), none) ((), none) B0 B2 B3 u c hU hC
  exact ⟨T, by omega, by simpa only [program, B0, B3] using hrun⟩

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateCycle
