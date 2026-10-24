import EthInapproximability.CurrentPaper.SourceOriginalVariableCapture
import EthInapproximability.CurrentPaper.EncodedETHSource
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# Original-variable capture followed by the cited sparse-source machine

The first finite program saves the original unary variable count while
restoring the whole CNF word. The cited sparsifier then runs on that restored
word. Its input stack is shared with the capture source stack, while every
other sparsifier stack is disjoint from the saved original count. No variable
count is read back from sparse branches.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalSparsificationMachine

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)

abbrev Stack := SourceOriginalVariableCapture.Stack ⊕ Fin S.machine.stackCount

private def captureSlots : SourceOriginalVariableCapture.Stack ↪ Stack S where
  toFun := Sum.inl
  inj' := Sum.inl_injective

private def sparseSlotFn (j : Fin S.machine.stackCount) : Stack S :=
  if j = S.machine.input then .inl 0 else .inr j

private def sparseSlots : Fin S.machine.stackCount ↪ Stack S where
  toFun := sparseSlotFn S
  inj' := by
    intro i j h
    by_cases hi : i = S.machine.input <;> by_cases hj : j = S.machine.input
    · exact hi.trans hj.symm
    · have : False := by simpa [sparseSlotFn, hi, hj] using h
      exact this.elim
    · have : False := by simpa [sparseSlotFn, hi, hj] using h
      exact this.elim
    · simpa [sparseSlotFn, hi, hj] using h

def outputSlots : Fin 2 ↪ Stack S where
  toFun
    | 0 => .inl 2
    | 1 => sparseSlots S S.machine.output
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · change (Sum.inl (2 : SourceOriginalVariableCapture.Stack) : Stack S) =
        sparseSlots S S.machine.output at h
      by_cases ho : S.machine.output = S.machine.input <;>
        simp [sparseSlots, sparseSlotFn, ho] at h
    · change sparseSlots S S.machine.output =
        (Sum.inl (2 : SourceOriginalVariableCapture.Stack) : Stack S) at h
      by_cases ho : S.machine.output = S.machine.input <;>
        simp [sparseSlots, sparseSlotFn, ho] at h
    · rfl

private def emptyBank : Stack S → List Bool := fun _ => []

noncomputable def startBank (input : List Bool) : Stack S → List Bool :=
  bank (captureSlots S) (emptyBank S)
    (SourceOriginalVariableCapture.cfg (some .scan) none input [] []).stk

noncomputable def capturedBank (input : List Bool) (n : ℕ) : Stack S → List Bool :=
  bank (captureSlots S) (emptyBank S)
    (SourceOriginalVariableCapture.cfg none none input []
      (List.replicate n true)).stk

noncomputable def finalBank (input : List Bool) (n T : ℕ) : Stack S → List Bool :=
  bank (sparseSlots S) (capturedBank S input n)
    ((S.machine).run T ((S.machine).init input)).stk

private def captureOn (l : SourceOriginalVariableCapture.Label) :
    TM2.Stmt (fun _ : Stack S => Bool) SourceOriginalVariableCapture.Label
      SourceOriginalVariableCapture.Control :=
  stackStmt (captureSlots S) (SourceOriginalVariableCapture.program l)

private def sparseOn (l : Fin S.machine.labelCount) :
    TM2.Stmt (fun _ : Stack S => Bool) (Fin S.machine.labelCount)
      (Fin S.machine.controlCount) :=
  stackStmt (sparseSlots S) (S.machine.program l)

def program := BitMachineRawSequence.program
  (captureOn S) (sparseOn S) S.machine.start none S.machine.initial

noncomputable def entry (input : List Bool) :
    TM2.Cfg (fun _ : Stack S => Bool)
      (BitMachineRawSequence.Label SourceOriginalVariableCapture.Label
        (Fin S.machine.labelCount))
      (BitMachineRawSequence.Control SourceOriginalVariableCapture.Control
        (Fin S.machine.controlCount)) :=
  ⟨some (BitMachineRawSequence.leftLabel SourceOriginalVariableCapture.Label.scan),
    (none, S.machine.initial), startBank S input⟩

noncomputable def sparseTime (input : List Bool) : ℕ :=
  S.timeConstant *
    ⌈(2 : ℝ) ^ ((η : ℝ) *
      (match EncodedCNF.decode input with | none => 0 | some f => f.variables))⌉₊ *
    (input.length+1)^S.timeExponent

noncomputable def totalTime (f : EncodedETHSource.ValidFormula) : ℕ :=
  2*f.val.variables+3 + sparseTime S (EncodedCNF.encode f.val) + 1

theorem sparseTime_encode (f : EncodedETHSource.ValidFormula) :
    sparseTime S (EncodedCNF.encode f.val) =
      S.timeConstant *
        ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
        ((EncodedCNF.encode f.val).length+1)^S.timeExponent := by
  simp only [sparseTime, EncodedCNF.decode_encode f.val f.property]

theorem totalTime_le_source_length (f : EncodedETHSource.ValidFormula) :
    totalTime S f ≤
      sparseTime S (EncodedCNF.encode f.val) +
        2*(EncodedCNF.encode f.val).length+4 := by
  have hn := SourceOriginalVariableCapture.original_n_le_input f.val
  unfold totalTime
  omega

private theorem capture_run (f : EncodedETHSource.ValidFormula) :
    ((advance (captureOn S))^[2*f.val.variables+3])
      (⟨some SourceOriginalVariableCapture.Label.scan, none,
        startBank S (EncodedCNF.encode f.val)⟩ :
        TM2.Cfg (fun _ : Stack S => Bool)
          SourceOriginalVariableCapture.Label
          SourceOriginalVariableCapture.Control) =
      ⟨none, none, capturedBank S (EncodedCNF.encode f.val) f.val.variables⟩ := by
  have h := BitMachineStackRun.run (captureSlots S) (emptyBank S)
    SourceOriginalVariableCapture.program
    (SourceOriginalVariableCapture.cfg (some .scan) none
      (EncodedCNF.encode f.val) [] []) (2*f.val.variables+3)
  have hraw :
      ((advance SourceOriginalVariableCapture.program)^[2*f.val.variables+3])
        (SourceOriginalVariableCapture.cfg (some .scan) none
          (EncodedCNF.encode f.val) [] []) =
        SourceOriginalVariableCapture.cfg none none
          (EncodedCNF.encode f.val) [] (List.replicate f.val.variables true) := by
    have hi : rawInit (0 : SourceOriginalVariableCapture.Stack)
        SourceOriginalVariableCapture.Label.scan
        (none : SourceOriginalVariableCapture.Control)
        (EncodedCNF.encode f.val) =
        SourceOriginalVariableCapture.cfg (some .scan) none
          (EncodedCNF.encode f.val) [] [] := by
      unfold rawInit SourceOriginalVariableCapture.cfg
      congr 1
      funext j
      fin_cases j <;> rfl
    rw [← hi]
    simpa only [SourceOriginalVariableCapture.run] using
      SourceOriginalVariableCapture.canonical_raw_run f.val
  rw [hraw] at h
  simpa only [captureOn, startBank, capturedBank,
    BitMachineStackEmbedding.stackCfg] using h

private theorem sparse_init_bank (input : List Bool) (n : ℕ) :
    bank (sparseSlots S) (capturedBank S input n)
      ((S.machine).init input).stk = capturedBank S input n := by
  apply bank_eq_self
  intro j
  by_cases hj : j = S.machine.input
  · subst j
    simp only [BitMachine.Machine.init, if_pos rfl]
    change input = capturedBank S input n (sparseSlots S S.machine.input)
    have hslot : sparseSlots S S.machine.input = .inl (0 : SourceOriginalVariableCapture.Stack) := by
      change sparseSlotFn S S.machine.input = _
      simp [sparseSlotFn]
    rw [hslot]
    change input = bank (captureSlots S) (emptyBank S)
      (SourceOriginalVariableCapture.cfg none none input []
        (List.replicate n true)).stk ((captureSlots S) 0)
    rw [bank_at]
    rfl
  · have hslot : sparseSlots S j = .inr j := by
      change sparseSlotFn S j = .inr j
      simp [sparseSlotFn, hj]
    rw [hslot]
    have hout : ¬ ∃ k : SourceOriginalVariableCapture.Stack,
        captureSlots S k = (Sum.inr j : Stack S) := by
      intro h
      obtain ⟨k, hk⟩ := h
      cases hk
    simp only [BitMachine.Machine.init, if_neg hj, capturedBank,
      bank_outside (captureSlots S) (emptyBank S) _ _ hout, emptyBank]

private theorem sparse_run (input : List Bool) (n T : ℕ) :
    ((advance (sparseOn S))^[T])
      (⟨some S.machine.start, S.machine.initial, capturedBank S input n⟩ :
        TM2.Cfg (fun _ : Stack S => Bool) (Fin S.machine.labelCount)
          (Fin S.machine.controlCount)) =
      ⟨((S.machine).run T ((S.machine).init input)).l,
        ((S.machine).run T ((S.machine).init input)).var,
        finalBank S input n T⟩ := by
  have h := BitMachineStackRun.run (sparseSlots S) (capturedBank S input n)
    S.machine.program (S.machine.init input) T
  simpa only [sparseOn, finalBank, BitMachineStackEmbedding.stackCfg,
    sparse_init_bank, BitMachine.Machine.run,
    BitMachine.Machine.step, advance] using h

theorem canonical_run (f : EncodedETHSource.ValidFormula) :
    let input := EncodedCNF.encode f.val
    let T := sparseTime S input
    let c := (S.machine).run T ((S.machine).init input)
    ∃ t ≤ totalTime S f,
      ((advance (program S))^[t]) (entry S input) =
        (⟨none, (none, c.var), finalBank S input f.val.variables T⟩ :
          TM2.Cfg (fun _ : Stack S => Bool) _ _) := by
  intro input T c
  have hS := S.runtime input
  change S.machine.OutputsWithin input
    (EncodedETHSource.sparsificationBits S.branches input) T at hS
  have hEnd := BitMachine.outputsWithin_at_bound S.machine hS
  have hFirst := capture_run S f
  have hSecond := sparse_run S input f.val.variables T
  rw [hEnd.1] at hSecond
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (captureOn S) (sparseOn S)
    SourceOriginalVariableCapture.Label.scan S.machine.start
    none none S.machine.initial c.var
    (startBank S input) (capturedBank S input f.val.variables)
    (finalBank S input f.val.variables T)
    (2*f.val.variables+3) T hFirst hSecond
  exact ⟨t, by simpa only [totalTime] using ht,
    by simpa only [program, entry] using hr⟩

theorem final_original_n (input : List Bool) (n T : ℕ) :
    finalBank S input n T (outputSlots S 0) = List.replicate n true := by
  have hout : ¬ ∃ j : Fin S.machine.stackCount,
      sparseSlots S j = outputSlots S 0 := by
    intro h
    obtain ⟨j, hj⟩ := h
    by_cases hi : j = S.machine.input
    · simp [outputSlots, sparseSlots, sparseSlotFn, hi] at hj
    · simp [outputSlots, sparseSlots, sparseSlotFn, hi] at hj
  rw [finalBank, bank_outside (sparseSlots S) _ _ _ hout]
  exact bank_at (captureSlots S) (emptyBank S) _ 2

theorem final_sparse_list (f : EncodedETHSource.ValidFormula) (T : ℕ)
    (hT : (S.machine).OutputsWithin (EncodedCNF.encode f.val)
      (EncodedETHSource.sparsificationBits S.branches
        (EncodedCNF.encode f.val)) T) :
    finalBank S (EncodedCNF.encode f.val) f.val.variables T
      (outputSlots S 1) =
        EncodedETHSource.formulaListBits (S.branches f) := by
  change bank (sparseSlots S)
    (capturedBank S (EncodedCNF.encode f.val) f.val.variables)
    ((S.machine).run T ((S.machine).init (EncodedCNF.encode f.val))).stk
      (sparseSlots S S.machine.output) = _
  rw [bank_at]
  have hOut := (BitMachine.outputsWithin_at_bound S.machine hT).2
  rw [hOut]
  have hdec := EncodedCNF.decode_encode f.val f.property
  unfold EncodedETHSource.sparsificationBits
  split
  · rename_i hnone
    rw [hdec] at hnone
    cases hnone
  · rename_i g hsome
    have hg : g = f.val := by
      have h := hsome.symm.trans hdec
      exact Option.some.inj h
    subst g
    have hf : (⟨f.val, EncodedCNF.decode_valid hsome⟩ :
        EncodedETHSource.ValidFormula) = f := by
      apply Subtype.ext
      rfl
    rw [hf]

theorem final_sparse_list_runtime (f : EncodedETHSource.ValidFormula) :
    finalBank S (EncodedCNF.encode f.val) f.val.variables
      (sparseTime S (EncodedCNF.encode f.val))
      (outputSlots S 1) =
        EncodedETHSource.formulaListBits (S.branches f) := by
  apply final_sparse_list S f
  simpa only [sparseTime] using S.runtime (EncodedCNF.encode f.val)

end EthInapproximability.CurrentPaper.SourceOriginalSparsificationMachine
