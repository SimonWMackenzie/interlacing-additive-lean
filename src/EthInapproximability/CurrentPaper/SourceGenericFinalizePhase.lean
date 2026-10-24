import EthInapproximability.CurrentPaper.SourceGenericConverterStack
import EthInapproximability.CurrentPaper.SourceGenericVariableUnary

/-!
# Header and finalizer phase (unit 1, segment 4)

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE, arbitrary
fixed positive alphabet `a` (the header scanner needs `0 < a`).

ONE fixed-`(a,q)` phase program on the converter bank that physically builds
the admitted finalizer's entire input bank
`SourceClauseCountFinalize.inputBank (sourceVariables P) (sourceEmittedCount P hq)
(sourceReversePayload P hq) []` and runs the unchanged finalizer:

1. copy unary `n` (writer vertex) to header cell `h0`;
2. copy unary `m` (validator row-count cell) to header cell `h1`;
3. run the admitted generic affine scanner `SourceGenericVariableUnary.program a q`,
   consuming `h0`,`h1` and writing `true^(sourceVariables P)` in the finalizer's
   variable cell;
4. copy the reverse payload (writer saved) to the finalizer's payload cell;
5. copy the unary clause count (writer count) to the counter's fuel cell;
6. clear the validator's output slot (the finalizer's output cell);
7. run `SourceClauseCountFinalize.program` (unary-to-binary count, finalizer).

All copies, the clear, the scanner and six handoffs are charged. The input
words are hypotheses about the ACTUAL bank reached by segment 2 (discharged in
`SourceGenericConverterRun`), not supplied outputs.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.Converter

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

/-! ## Cell facts -/

theorem vertex_ne_h0 (q : Nat) : vertexCell q ≠ h0 q := by intro h; cases h
theorem vertex_ne_scr (q : Nat) : vertexCell q ≠ scr q := by intro h; cases h
theorem h0_ne_scr (q : Nat) : h0 q ≠ scr q := by simp [h0, scr]
theorem countG_ne_h1 (q : Nat) : countGCell q ≠ h1 q := by intro h; cases h
theorem countG_ne_scr (q : Nat) : countGCell q ≠ scr q := by intro h; cases h
theorem h1_ne_scr (q : Nat) : h1 q ≠ scr q := by simp [h1, scr]
theorem saved_ne_fin1 (q : Nat) : savedCellC q ≠ fin1 q := by intro h; cases h
theorem saved_ne_scr (q : Nat) : savedCellC q ≠ scr q := by intro h; cases h
theorem fin1_ne_scr (q : Nat) : fin1 q ≠ scr q := by simp [fin1, scr]
theorem countC_ne_fuel (q : Nat) : countCellC q ≠ fuel q := by intro h; cases h
theorem countC_ne_scr (q : Nat) : countCellC q ≠ scr q := by intro h; cases h
theorem fuel_ne_scr (q : Nat) : fuel q ≠ scr q := by simp [fuel, scr]

/-! ## The phase program -/

noncomputable def copyN (q : Nat) :=
  copyProgram (vertexCell q) (h0 q) (scr q)
    (vertex_ne_h0 q) (vertex_ne_scr q) (h0_ne_scr q)
noncomputable def copyM (q : Nat) :=
  copyProgram (countGCell q) (h1 q) (scr q)
    (countG_ne_h1 q) (countG_ne_scr q) (h1_ne_scr q)
noncomputable def scanProgram (a q : Nat) :=
  fun l => stackStmt (hdrEmb q) (SourceGenericVariableUnary.program a q l)
noncomputable def copyP (q : Nat) :=
  copyProgram (savedCellC q) (fin1 q) (scr q)
    (saved_ne_fin1 q) (saved_ne_scr q) (fin1_ne_scr q)
noncomputable def copyC (q : Nat) :=
  copyProgram (countCellC q) (fuel q) (scr q)
    (countC_ne_fuel q) (countC_ne_scr q) (fuel_ne_scr q)
noncomputable def clearOut (q : Nat) := clearProgram (outCell q)
noncomputable def finProgram (q : Nat) :=
  fun l => stackStmt (finEmb q) (SourceClauseCountFinalize.program l)

noncomputable def p6 (q : Nat) :=
  BitMachineRawSequence.program (clearOut q) (finProgram q)
    (BitMachineRawSequence.leftLabel (.inr .testFuel)) ((), none)
    ((SourceClauseCountFinalize.counter.initial, none), none)
noncomputable def p5 (q : Nat) :=
  BitMachineRawSequence.program (copyC q) (p6 q)
    (BitMachineRawSequence.leftLabel 0) none
    (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))
noncomputable def p4 (q : Nat) :=
  BitMachineRawSequence.program (copyP q) (p5 q)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, (((), none), ((SourceClauseCountFinalize.counter.initial, none), none)))
noncomputable def p3 (a q : Nat) :=
  BitMachineRawSequence.program (scanProgram a q) (p4 q)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))))
noncomputable def p2 (a q : Nat) :=
  BitMachineRawSequence.program (copyM q) (p3 a q)
    (BitMachineRawSequence.leftLabel .vertexScan) none
    (none, (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none)))))
/-- The fixed segment-4 phase. -/
noncomputable def phase (a q : Nat) :=
  BitMachineRawSequence.program (copyN q) (p2 a q)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
    (none, (none, (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))))))

/-- The phase's start (= end) control. -/
noncomputable def phaseControl (a q : Nat) :
    FirstRow.CtlOf (phase a q) :=
  (none, (none, (none, (none, (none,
    (((), none), ((SourceClauseCountFinalize.counter.initial, none), none)))))))

/-! ## Intermediate banks -/

section Banks

variable {q : Nat}

noncomputable def bank1 (W : CStack q → List Bool) (n : Nat) : CStack q → List Bool :=
  Function.update W (h0 q) (List.replicate n true)
noncomputable def bank2 (W : CStack q → List Bool) (n m : Nat) : CStack q → List Bool :=
  Function.update (bank1 W n) (h1 q) (List.replicate m true)
noncomputable def bank3 (W : CStack q → List Bool) (n m vars : Nat) :
    CStack q → List Bool :=
  bank (hdrEmb q) (bank2 W n m)
    (SourceAffineUnary.contents [] [] (List.replicate vars true))
noncomputable def bank4 (W : CStack q → List Bool) (n m vars : Nat)
    (payload : List Bool) : CStack q → List Bool :=
  Function.update (bank3 W n m vars) (fin1 q) payload
noncomputable def bank5 (W : CStack q → List Bool) (n m vars : Nat)
    (payload : List Bool) (cnt : Nat) : CStack q → List Bool :=
  Function.update (bank4 W n m vars payload) (fuel q) (List.replicate cnt true)
noncomputable def bank6 (W : CStack q → List Bool) (n m vars : Nat)
    (payload : List Bool) (cnt : Nat) : CStack q → List Bool :=
  Function.update (bank5 W n m vars payload cnt) (outCell q) []

/-- The finalizer's exact exit bank (from the admitted `count_and_finalize`). -/
noncomputable def finExit (vars cnt : Nat) (payload : List Bool) :
    SourceClauseCountFinalize.Stack → List Bool :=
  bank SourceClauseCountFinalize.finalizerEmbedding
    (SourceClauseCountFinalize.convertedBank vars cnt payload [])
    (SourceClauseMachine.cfg none none [] [] [] []
      (EncodedGraph.unary vars ++ EncodedCommunication.natField cnt ++
        payload.reverse ++ [])).stk

/-- Exact whole exit bank of the phase. -/
noncomputable def phaseFinal (W : CStack q → List Bool) (n m vars : Nat)
    (payload : List Bool) (cnt : Nat) : CStack q → List Bool :=
  bank (finEmb q) (bank6 W n m vars payload cnt) (finExit vars cnt payload)

end Banks

/-- Explicit charged clock of the phase. -/
noncomputable def phaseClock (a q n m vars cnt payloadLen outLen : Nat) : Nat :=
  (2*n+2) + ((2*m+2) + (SourceGenericVariableUnary.time a q n m +
    ((2*payloadLen+2) + ((2*cnt+2) + ((outLen+2) +
      (UnaryBinaryEncoding.coefficient * (cnt + 1) ^ 2 +
        (payloadLen + 3 * cnt.bits.length + vars + 5) + 1) + 1) + 1) + 1) + 1) + 1) + 1

theorem finExit_out (vars cnt : Nat) (payload : List Bool) :
    finExit vars cnt payload (.inl 3) =
      EncodedGraph.unary vars ++ EncodedCommunication.natField cnt ++
        payload.reverse ++ [] := by
  unfold finExit
  rw [show (.inl 3 : SourceClauseCountFinalize.Stack) =
      SourceClauseCountFinalize.finalizerEmbedding 4 by
    simp [SourceClauseCountFinalize.finalizerEmbedding], bank_at]
  rfl

/-- The finalizer output is exactly the literal encoded three-CNF. -/
theorem encode_identity {n m a q : Nat} (P : SourceBooleanEncoding.CSP n m a q) (hq : 0 < q) :
    EncodedGraph.unary (SourceGenericOrder.sourceVariables P) ++
        EncodedCommunication.natField (SourceGenericOrder.sourceEmittedCount P hq) ++
        (SourceGenericOrder.sourceReversePayload P hq).reverse ++ [] =
      EncodedCNF.encode (SourceBooleanEncoding.threeCNF P hq) := by
  rw [SourceGenericOrder.sourceVariables_eq P hq,
    SourceGenericOrder.sourceEmittedCount_eq P hq,
    SourceGenericOrder.sourceReversePayload_eq]
  simp [EncodedCNF.encode, List.append_assoc]

#print axioms finExit_out
#print axioms encode_identity

end EthInapproximability.CurrentPaper.SourceGenericComposite.Converter
