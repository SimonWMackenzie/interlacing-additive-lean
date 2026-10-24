import EthInapproximability.CurrentPaper.SourceGenericFinalizePhaseRun

/-!
# The complete fixed generic converter and its accepted-branch run
(unit 1, segment 4)

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE, arbitrary
fixed positive alphabet `a`, positive arity `q`.

`converter a q hq` is ONE fixed raw-input program on `CStack q`: the actual
global validator, the live verdict branch (reject/zero halt in place), and on
acceptance the body `RawSequence(segment-2 body, segment-4 phase)`.
`accepted_run` follows the SAME reached bank from the actual accepting
validator halt through staging, prefix, all rows, the physical transfer into
the admitted finalizer's input bank, and the finalizer; the validator output
slot then holds `EncodedCNF.encode (threeCNF P hq)` for the read-back instance.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.Converter

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def body2C {a q : Nat} (hq : 0 < q) :=
  fun l => stackStmt (mainEmb q) (FirstRow.program (a := a) hq l)

/-- Accepted-branch body: segment-2 body, then the segment-4 phase. -/
noncomputable def body {a q : Nat} (hq : 0 < q) :=
  BitMachineRawSequence.program (body2C (a := a) hq) (phase a q)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (SourceCSPFirstRowController.bodyInitial,
      (FirstRow.ambControl a q, FirstRow.suffixStart (a := a) hq))
    (phaseControl a q)

noncomputable def bodyInit {a q : Nat} (hq : 0 < q) :
    FirstRow.CtlOf (body (a := a) hq) :=
  ((SourceCSPFirstRowController.bodyInitial,
      (FirstRow.ambControl a q, FirstRow.suffixStart (a := a) hq)),
    phaseControl a q)

/-- THE fixed raw-input generic converter. -/
noncomputable def converter (a q : Nat) (hq : 0 < q) :=
  topC a q (body (a := a) hq)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceCSPFirstRowController.bodyStart (q := q) (a := a))))
    (bodyInit (a := a) hq)

/-- The label type of a fixed program (used only to name it). -/
abbrev LabOf {K L V : Type} [DecidableEq K]
    (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type := L

noncomputable def converterInitial (a q : Nat) (hq : 0 < q) (input : List Bool) :=
  topCInitial a q (LB := LabOf (body (a := a) hq)) (bodyInit (a := a) hq) input

/-- The segment-2 exit bank inside the converter bank. -/
noncomputable def rowsDoneBank {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool) :
    CStack q → List Bool :=
  bank (mainEmb q) (bank (globalEmbC q) (fun _ => []) S)
    (FirstRow.finalBank hq hm rows S U lastRow)

/-- Exact final bank of the accepted branch. -/
noncomputable def acceptedFinal {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool) :
    CStack q → List Bool :=
  phaseFinal (rowsDoneBank hq hm rows S U lastRow) n m
    (SourceGenericOrder.sourceVariables (SourceCSPCodec.fromRows n m a q rows).system)
    (SourceGenericOrder.sourceReversePayload
      (SourceCSPCodec.fromRows n m a q rows).system hq)
    (SourceGenericOrder.sourceEmittedCount
      (SourceCSPCodec.fromRows n m a q rows).system hq)

theorem count_ne_loop {q : Nat} :
    (SourceCSPHeaderRowBridge.count : SourceCSPGlobalDecisionProgram.Stack q) ≠
      SourceCSPHeaderRowBridge.loopCount := by
  intro h; cases h

theorem output_ne_loop {q : Nat} :
    (SourceCSPGlobalDecisionProgram.outputSlot :
      SourceCSPGlobalDecisionProgram.Stack q) ≠
      SourceCSPHeaderRowBridge.loopCount := by
  intro h; cases h

/-- Segment 4: the accepted branch of the fixed converter, from the ACTUAL
accepting validator halt, ends with the literal encoded three-CNF of the
read-back instance in the validator output slot. -/
theorem accepted_run {a q : Nat} (ha : 0 < a) (hq : 0 < q)
    (input : List Bool) (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩) :
    ∃ (n m : Nat) (hm : 0 < m) (suffix : List Bool)
      (rows : Fin m → SourceCSPCodec.Row n a q)
      (U : SourceCSPFirstRowController.Stack q → List Bool)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool) (t : Nat),
      0 < n ∧ n ≤ q * m ∧ m ≤ input.length ∧
      input = SourceCSPHeaderParse.header n m a q ++ suffix ∧
      SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
        some (rows, []) ∧
      (∀ x, (U x).length ≤ AcceptedSource.envelope a q input.length) ∧
      t ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1 + 1 +
        (((SourceCSPFirstRowController.stageBound suffix n +
            SourceCSPFirstRowController.rowBound a q n suffix + 1) +
          (PrefixAmbientProgram.cost n a q +
            FirstRow.suffixClock hq hm rows U input.length + 1) + 1) +
        phaseClock a q n m
          (SourceGenericOrder.sourceVariables
            (SourceCSPCodec.fromRows n m a q rows).system)
          (SourceGenericOrder.sourceEmittedCount
            (SourceCSPCodec.fromRows n m a q rows).system hq)
          (SourceGenericOrder.sourceReversePayload
            (SourceCSPCodec.fromRows n m a q rows).system hq).length
          (S SourceCSPGlobalDecisionProgram.outputSlot).length + 1) ∧
      ((advance (converter a q hq))^[t]) (converterInitial a q hq input) =
        ⟨none, (SourceCSPSelectiveStage.globalInitialControl a q, bodyInit hq),
          acceptedFinal hq hm rows S U lastRow⟩ ∧
      acceptedFinal hq hm rows S U lastRow (outCell q) =
        EncodedCNF.encode (SourceBooleanEncoding.threeCNF
          (SourceCSPCodec.fromRows n m a q rows).system hq) := by
  obtain ⟨n, m, hm, suffix, rest, rows, U, lastRow, t2, hn, hsize, hmL,
    hinput, hread, _, _, hcount, _, _, _, _, _, _, _, _, _, _,
    hUenv, ht2, hrun2, _⟩ := FirstRow.body_run hq input tg vr S hacc
  obtain ⟨tb0, _, _, _, _, htb0, hglob, _⟩ :=
    AcceptedSource.raw_accepted_source a q input tg vr S hacc
  let F0 : CStack q → List Bool := bank (globalEmbC q) (fun _ => []) S
  -- lift the segment-2 body
  have hF0 : bank (mainEmb q) F0 (FirstRow.globalBank S) = F0 := by
    apply bank_eq_self
    intro x
    change FirstRow.globalBank S x = bank (globalEmbC q) (fun _ => []) S (mainEmb q x)
    rw [globalBankC_eq, bank_at]
  have hl := BitMachineStackRun.run (mainEmb q) F0 (FirstRow.program (a := a) hq)
    (⟨some (BitMachineRawSequence.leftLabel
        (SourceCSPFirstRowController.bodyStart (q := q) (a := a))),
      (SourceCSPFirstRowController.bodyInitial,
        (FirstRow.ambControl a q, FirstRow.suffixStart (a := a) hq)),
      FirstRow.globalBank S⟩ : TM2.Cfg (fun _ : SourceGenericComposite.Stack q => Bool) _ _) t2
  rw [hrun2] at hl
  simp only [stackCfg, hF0] at hl
  -- the phase premises, read off the actual reached bank
  let W := rowsDoneBank hq hm rows S U lastRow
  have hfields := SourceCSPNextRowBridge.callback_bank_fields
    (SourceGenericAllRowLoop.withRemaining
      (Function.update S SourceCSPHeaderRowBridge.loopCount []) 0)
    lastRow n (m - 1) (SourceGenericOrder.sourceReversePayload (SourceCSPCodec.fromRows n m a q rows).system hq) []
    (List.replicate (SourceGenericOrder.sourceEmittedCount (SourceCSPCodec.fromRows n m a q rows).system hq) true)
  have hWfsb : ∀ z, W (mainEmb q (fsbEmb q z)) =
      SourceCSPNextRowBridge.callbackBank
        (SourceGenericAllRowLoop.withRemaining
          (Function.update S SourceCSPHeaderRowBridge.loopCount []) 0)
        lastRow n (m - 1) (SourceGenericOrder.sourceReversePayload (SourceCSPCodec.fromRows n m a q rows).system hq) []
        (List.replicate (SourceGenericOrder.sourceEmittedCount (SourceCSPCodec.fromRows n m a q rows).system hq) true) z := by
    intro z
    change bank (mainEmb q) F0 (FirstRow.finalBank hq hm rows S U lastRow)
      (mainEmb q (fsbEmb q z)) = _
    rw [bank_at, Payload.finalBank_eq, bank_at]
  have hV : W (vertexCell q) = List.replicate n true :=
    (hWfsb _).trans hfields.2.2.2.1
  have hP : W (savedCellC q) = SourceGenericOrder.sourceReversePayload (SourceCSPCodec.fromRows n m a q rows).system hq :=
    (hWfsb _).trans hfields.2.2.2.2.2.1
  have hC : W (countCellC q) =
      List.replicate (SourceGenericOrder.sourceEmittedCount (SourceCSPCodec.fromRows n m a q rows).system hq) true :=
    (hWfsb _).trans hfields.2.2.2.2.2.2.2
  have hM : W (countGCell q) = List.replicate m true := by
    change W (mainEmb q (fsbEmb q (.inl SourceCSPHeaderRowBridge.count))) = _
    rw [hWfsb]
    change SourceGenericAllRowLoop.withRemaining
      (Function.update S SourceCSPHeaderRowBridge.loopCount []) 0
      SourceCSPHeaderRowBridge.count = _
    rw [SourceGenericAllRowLoop.withRemaining,
      Function.update_of_ne count_ne_loop, Function.update_of_ne count_ne_loop]
    exact hcount
  have hOut : W (outCell q) = S SourceCSPGlobalDecisionProgram.outputSlot := by
    change W (mainEmb q (fsbEmb q (.inl SourceCSPGlobalDecisionProgram.outputSlot))) = _
    rw [hWfsb]
    change SourceGenericAllRowLoop.withRemaining
      (Function.update S SourceCSPHeaderRowBridge.loopCount []) 0
      SourceCSPGlobalDecisionProgram.outputSlot = _
    rw [SourceGenericAllRowLoop.withRemaining,
      Function.update_of_ne output_ne_loop, Function.update_of_ne output_ne_loop]
  have hE : ∀ e : Extra, W (.inr e) = [] := by
    intro e
    have h1 : ¬ ∃ x, mainEmb q x = (.inr e : CStack q) := by
      rintro ⟨x, hx⟩; cases hx
    have h2 : ¬ ∃ g, globalEmbC q g = (.inr e : CStack q) := by
      rintro ⟨g, hg⟩; cases hg
    change bank (mainEmb q) (bank (globalEmbC q) (fun _ => []) S)
      (FirstRow.finalBank hq hm rows S U lastRow) (.inr e) = []
    rw [bank_outside _ _ _ _ h1, bank_outside _ _ _ _ h2]
  obtain ⟨t4, ht4, hrun4, hout⟩ :=
    phase_run (n := n) (m := m) ha hq (SourceCSPCodec.fromRows n m a q rows).system W hV hM hP hC hE
  rw [hOut] at ht4
  obtain ⟨tB, htB, hB⟩ := BitMachineRawSequence.runs
    (body2C (a := a) hq) (phase a q)
    (BitMachineRawSequence.leftLabel
      (SourceCSPFirstRowController.bodyStart (q := q) (a := a)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (SourceCSPFirstRowController.bodyInitial,
      (FirstRow.ambControl a q, FirstRow.suffixStart (a := a) hq))
    (SourceCSPFirstRowController.bodyInitial,
      (FirstRow.ambControl a q, FirstRow.suffixEnd (a := a) hq))
    (phaseControl a q) (phaseControl a q)
    F0 W (acceptedFinal hq hm rows S U lastRow) t2 t4 hl hrun4
  obtain ⟨T, hT, hR⟩ := topC_accepted_run (body (a := a) hq)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceCSPFirstRowController.bodyStart (q := q) (a := a))))
    (bodyInit (a := a) hq) (bodyInit (a := a) hq)
    input tb0 vr S hglob tB _ hB
  have ht4' : t4 ≤ phaseClock a q n m
      (SourceGenericOrder.sourceVariables
        (SourceCSPCodec.fromRows n m a q rows).system)
      (SourceGenericOrder.sourceEmittedCount
        (SourceCSPCodec.fromRows n m a q rows).system hq)
      (SourceGenericOrder.sourceReversePayload
        (SourceCSPCodec.fromRows n m a q rows).system hq).length
      (S SourceCSPGlobalDecisionProgram.outputSlot).length := ht4
  refine ⟨n, m, hm, suffix, rows, U, lastRow, T, hn, hsize, hmL, hinput,
    hread, hUenv, ?_, hR, hout⟩
  omega

#print axioms accepted_run

end EthInapproximability.CurrentPaper.SourceGenericComposite.Converter
