import EthInapproximability.CurrentPaper.ETHParameterScaleMachineInput
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! A first complete physical logarithmic candidate: preserve its raw unary
source, compute ceiling log on the LogCopy submachine, and physically copy
that output into a separate candidate cell. -/

namespace EthInapproximability.CurrentPaper.ETHScaleColumnCandidate

open Turing BitMachineEncoding BitMachineStackEmbedding
open ETHParameterScaleMachineLogCopy
open scoped Classical

abbrev Stack := ETHParameterScaleMachineLogCopy.Stack ⊕ Fin 2
abbrev Label := BitMachineRawSequence.Label ETHParameterScaleMachineLogCopy.Label BitMachineCopy.Label
abbrev Control := ETHParameterScaleMachineLogCopy.Control × Option Bool

def logEmbed : ETHParameterScaleMachineLogCopy.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := by intro a b h; exact Sum.inl.inj h

noncomputable def outEmbed : Fin 3 ↪ Stack where
  toFun
    | 0 => .inl (logStack logMachine.output)
    | 1 => .inr 0
    | _ => .inr 1
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢

noncomputable def initial (n : ℕ) : Stack → List Bool :=
  Sum.elim (start (List.replicate n true)).stk (fun _ => [])

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program
    (fun l => stackStmt logEmbed (ETHParameterScaleMachineLogCopy.program l))
    (fun l => stackStmt outEmbed (BitMachineCopy.program l))
    .scan (copyControl none) none

noncomputable def logCost (n : ℕ) : ℕ :=
  2*n+2 + (UnaryBinaryEncoding.coefficient+6)*(n+1)^2

/- A physical bound on the same fixed finite controller, with its output in
the separate candidate cell and the original unary source preserved. -/
theorem column_candidate (n : ℕ) :
    ∃ t ≤ logCost n + (2 * Nat.clog 2 n + 2) + 1,
      ∃ F : Stack → List Bool,
        ((advance program)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
            (copyControl none, none), initial n⟩ :
            TM2.Cfg (fun _ : Stack => Bool) Label Control) =
          ⟨none, (copyControl none, none), F⟩ ∧
        F (.inr 0) = List.replicate (Nat.clog 2 n) true ∧
        F (.inl (.inl 0)) = List.replicate n true := by
  obtain ⟨ta, c, hta, hlog, hc, ho⟩ := copied_log_run n
  let q := List.replicate n true
  let z := List.replicate (Nat.clog 2 n) true
  let S : Stack → List Bool := Sum.elim (afterLog q c).stk (fun _ => [])
  let T : Stack → List Bool := bank outEmbed S
    (BitMachineCopy.cfg none none z z []).stk
  have hfirst :
      ((advance (fun l => stackStmt logEmbed (ETHParameterScaleMachineLogCopy.program l)))^[ta])
        (⟨some (.inl .scan), copyControl none, initial n⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ETHParameterScaleMachineLogCopy.Label
            ETHParameterScaleMachineLogCopy.Control) =
        ⟨none, (afterLog q c).var, S⟩ := by
    have hbankStart : bank logEmbed (initial n) (start q).stk = initial n :=
      bank_eq_self logEmbed (initial n) (start q).stk (by intro k; rfl)
    have hbankEnd : bank logEmbed (initial n) (afterLog q c).stk = S := by
      funext k
      cases k with
      | inl x => exact bank_at logEmbed (initial n) _ x
      | inr x =>
          rw [bank_outside logEmbed (initial n) _ (.inr x) (by
            rintro ⟨y, hy⟩
            cases hy)]
          rfl
    have h := BitMachineStackRun.run logEmbed (initial n)
      ETHParameterScaleMachineLogCopy.program (start q) ta
    rw [show stackCfg logEmbed (initial n) (start q) =
      (⟨some (.inl .scan), copyControl none, initial n⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ETHParameterScaleMachineLogCopy.Label
          ETHParameterScaleMachineLogCopy.Control) by
        simp only [stackCfg, hbankStart]
        rfl] at h
    rw [show ((advance ETHParameterScaleMachineLogCopy.program)^[ta]) (start q) =
      afterLog q c from hlog] at h
    change _ = (⟨(afterLog q c).l, (afterLog q c).var,
      bank logEmbed (initial n) (afterLog q c).stk⟩ :
      TM2.Cfg (fun _ : Stack => Bool) ETHParameterScaleMachineLogCopy.Label
        ETHParameterScaleMachineLogCopy.Control) at h
    rw [hbankEnd] at h
    have hnone : (afterLog q c).l = none := by
      simp only [afterLog, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hc,
        Option.map_none]
    rw [hnone] at h
    exact h
  have houtStart :
      stackCfg outEmbed S (BitMachineCopy.cfg (some .scan) none z [] []) =
      (⟨some .scan, none, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) := by
    apply congrArg (fun W : Stack → List Bool =>
      (⟨some .scan, none, W⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)))
    apply bank_eq_self
    intro k
    fin_cases k
    · change z = (afterLog q c).stk (logStack logMachine.output)
      exact ((afterLog_output n c).trans ho).symm
    · rfl
    · rfl
  have hsecond :
      ((advance (fun l => stackStmt outEmbed (BitMachineCopy.program l)))^[
        2*z.length+2])
        (⟨some .scan, none, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, T⟩ := by
    have h := BitMachineStackRun.run outEmbed S BitMachineCopy.program
      (BitMachineCopy.cfg (some .scan) none z [] []) (2*z.length+2)
    rw [houtStart] at h
    rw [show ((advance BitMachineCopy.program)^[2*z.length+2])
      (BitMachineCopy.cfg (some .scan) none z [] []) =
      BitMachineCopy.cfg none none z z [] by
        simpa only [BitMachineCopy.run, List.append_nil] using
          BitMachineCopy.run_correct none z []] at h
    simpa [T, stackCfg] using h
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (fun l => stackStmt logEmbed (ETHParameterScaleMachineLogCopy.program l))
    (fun l => stackStmt outEmbed (BitMachineCopy.program l))
    (.inl .scan) .scan (copyControl none) (afterLog q c).var
    none none (initial n) S T ta (2*z.length+2) hfirst hsecond
  refine ⟨t, ?_, T, ?_, ?_, ?_⟩
  · simp only [z, List.length_replicate] at ht
    change t ≤ 2*n+2 + (UnaryBinaryEncoding.coefficient+6)*(n+1)^2 +
      (2 * Nat.clog 2 n + 2) + 1
    omega
  · simpa only [program] using hr
  · exact bank_at outEmbed S _ 1
  · have houtside : ¬ ∃ k : Fin 3, outEmbed k = (.inl (.inl 0) : Stack) := by
      rintro ⟨k, hk⟩
      fin_cases k <;> simp [outEmbed, logStack] at hk
    rw [show T (.inl (.inl 0)) = S (.inl (.inl 0)) from
      bank_outside outEmbed S _ _ houtside]
    change (afterLog q c).stk (.inl 0) = List.replicate n true
    exact afterLog_source n c

end EthInapproximability.CurrentPaper.ETHScaleColumnCandidate
