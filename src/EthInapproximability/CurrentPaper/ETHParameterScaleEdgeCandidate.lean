import EthInapproximability.CurrentPaper.ETHParameterScaleColumnCandidate

/-! Preserve the supplied raw unary edge word while preparing a distinct
private unary word of length edges+2 for the logarithm controller. -/

namespace EthInapproximability.CurrentPaper.ETHScaleEdgePreparation

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack := Fin 1 ⊕ (ETHScaleColumnCandidate.Stack ⊕ Fin 1)
abbrev Label := BitMachineRawSequence.Label BitMachineCopy.Label (Fin 2)
abbrev Control := Option Bool × Unit

def raw : Stack := .inl 0
def work : Stack := .inr (.inl (.inl (.inl 0)))
def scratch : Stack := .inr (.inr 0)

def copyEmbed : Fin 3 ↪ Stack where
  toFun
    | 0 => raw
    | 1 => work
    | _ => scratch
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [raw, work, scratch] at h ⊢

def addTwoProgram : Fin 2 → TM2.Stmt (fun _ : Stack => Bool) (Fin 2) Unit
  | 0 => .push work (fun _ => true) (.goto (fun _ => 1))
  | _ => .push work (fun _ => true) .halt

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program
    (fun l => stackStmt copyEmbed (BitMachineCopy.program l))
    addTwoProgram 0 none ()

noncomputable def initial (n : ℕ) : Stack → List Bool :=
  fun k => if k = raw then List.replicate n true else []

noncomputable def finalBank (n : ℕ) : Stack → List Bool :=
  Function.update
    (bank copyEmbed (initial n)
      (BitMachineCopy.cfg none none
        (List.replicate n true) (List.replicate n true) []).stk)
    work (List.replicate (n+2) true)

theorem prepared (n : ℕ) :
    ∃ t ≤ 2*n+5,
        ((advance program)^[t])
          (⟨some (BitMachineRawSequence.leftLabel .scan),
            (none, ()), initial n⟩ :
            TM2.Cfg (fun _ : Stack => Bool) Label Control) =
          ⟨none, (none, ()), finalBank n⟩ ∧
        finalBank n raw = List.replicate n true ∧
        finalBank n work = List.replicate (n+2) true := by
  let q := List.replicate n true
  let S := bank copyEmbed (initial n)
    (BitMachineCopy.cfg none none q q []).stk
  have hstart : stackCfg copyEmbed (initial n)
      (BitMachineCopy.cfg (some .scan) none q [] []) =
      (⟨some .scan, none, initial n⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) := by
    apply congrArg (fun W : Stack → List Bool =>
      (⟨some .scan, none, W⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)))
    apply bank_eq_self
    intro k
    fin_cases k <;> rfl
  have hcopy :
      ((advance (fun l => stackStmt copyEmbed (BitMachineCopy.program l)))^[2*n+2])
        (⟨some .scan, none, initial n⟩ :
          TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, S⟩ := by
    have h := BitMachineStackRun.run copyEmbed (initial n) BitMachineCopy.program
      (BitMachineCopy.cfg (some .scan) none q [] []) (2*n+2)
    rw [hstart] at h
    rw [show ((advance BitMachineCopy.program)^[2*n+2])
      (BitMachineCopy.cfg (some .scan) none q [] []) =
        BitMachineCopy.cfg none none q q [] by
        simpa only [q, List.length_replicate, BitMachineCopy.run,
          List.append_nil] using BitMachineCopy.run_correct none q []] at h
    simpa only [S, stackCfg] using h
  have hwork : S work = q := bank_at copyEmbed (initial n) _ 1
  let F : Stack → List Bool := Function.update S work (true :: true :: q)
  have hadd : ((advance addTwoProgram)^[2])
      (⟨some 0, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) (Fin 2) Unit) =
      ⟨none, (), F⟩ := by
    simp [Function.iterate_succ_apply', advance, addTwoProgram,
      TM2.step, TM2.stepAux, F, hwork]
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (fun l => stackStmt copyEmbed (BitMachineCopy.program l))
    addTwoProgram .scan 0 none none () () (initial n) S F
    (2*n+2) 2 hcopy hadd
  have hF : F = finalBank n := by
    funext k
    simp [F, finalBank, S, q, List.replicate_succ]
  refine ⟨t, by omega, ?_, ?_, ?_⟩
  · simpa only [program, ← hF] using hr
  · rw [← hF]
    change (Function.update S work (true :: true :: q)) raw = _
    rw [Function.update_of_ne (by decide : raw ≠ work)]
    exact bank_at copyEmbed (initial n) _ 0
  · rw [← hF]
    simp [F, work, q, List.replicate_succ]

def candidateEmbed : ETHScaleColumnCandidate.Stack ↪ Stack where
  toFun k := .inr (.inl k)
  inj' := by intro a b h; exact Sum.inl.inj (Sum.inr.inj h)

theorem prepared_candidate_bank (n : ℕ)
    (k : ETHScaleColumnCandidate.Stack) :
    finalBank n (candidateEmbed k) =
      ETHScaleColumnCandidate.initial (n+2) k := by
  classical
  by_cases hk : k = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
  · subst k
    change finalBank n work = _
    rw [show finalBank n work = List.replicate (n+2) true by
      simp [finalBank, work]]
    change List.replicate (n+2) true =
      bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
        (BitMachineCopy.cfg (some .scan) none
          (List.replicate (n+2) true) [] []).stk
        (ETHParameterScaleMachineLogCopy.copyStack 0)
    rw [bank_at]
    rfl
  · have hne : candidateEmbed k ≠ work := by
      intro h
      have : k = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack) := by
        cases k with
        | inl x =>
            cases x with
            | inl i => fin_cases i; rfl
            | inr x => cases x with
              | inl y => cases h
              | inr y => cases h
        | inr x => cases h
      exact hk this
    have hout : ¬ ∃ p : Fin 3, copyEmbed p = candidateEmbed k := by
      rintro ⟨p, hp⟩
      fin_cases p
      · simp [copyEmbed, raw, candidateEmbed] at hp
      · exact hne hp.symm
      · simp [copyEmbed, scratch, candidateEmbed] at hp
    change (Function.update _ work _) (candidateEmbed k) = _
    rw [Function.update_of_ne hne,
      bank_outside copyEmbed (initial n) _ _ hout]
    have hinit : initial n (candidateEmbed k) = [] := by
      simp [initial, raw, candidateEmbed]
    rw [hinit]
    cases k with
    | inr x => rfl
    | inl x =>
      symm
      change bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
        (BitMachineCopy.cfg (some .scan) none
          (List.replicate (n+2) true) [] []).stk x = []
      by_cases hmem : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = x
      · obtain ⟨p, hp⟩ := hmem
        rw [← hp, bank_at]
        fin_cases p
        all_goals first
          | exact (hk (congrArg Sum.inl (by
              simpa [ETHParameterScaleMachineLogCopy.copyStack] using hp.symm))).elim
          | rfl
      · rw [bank_outside _ _ _ _ hmem]

abbrev FullLabel :=
  BitMachineRawSequence.Label Label ETHScaleColumnCandidate.Label
abbrev FullControl := Control × ETHScaleColumnCandidate.Control

noncomputable def fullProgram : FullLabel →
    TM2.Stmt (fun _ : Stack => Bool) FullLabel FullControl :=
  BitMachineRawSequence.program program
    (fun l => stackStmt candidateEmbed (ETHScaleColumnCandidate.program l))
    (BitMachineRawSequence.leftLabel (.inl .scan))
    (none, ()) (ETHParameterScaleMachineLogCopy.copyControl none, none)

theorem edge_candidate (n : ℕ) :
    ∃ t ≤ (2*n+5) +
        (ETHScaleColumnCandidate.logCost (n+2) +
          (2 * Nat.clog 2 (n+2) + 2) + 1) + 1,
      ∃ F : Stack → List Bool,
        ((advance fullProgram)^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel .scan)),
            ((none, ()),
              (ETHParameterScaleMachineLogCopy.copyControl none, none)),
            initial n⟩ :
            TM2.Cfg (fun _ : Stack => Bool) FullLabel FullControl) =
          ⟨none, ((none, ()),
            (ETHParameterScaleMachineLogCopy.copyControl none, none)), F⟩ ∧
        F raw = List.replicate n true ∧
        F (candidateEmbed (.inr 0)) =
          List.replicate (Nat.clog 2 (n+2)) true := by
  obtain ⟨tp, htp, hp, _hraw, _hwork⟩ := prepared n
  obtain ⟨tc, htc, C, hc, hcandidate, _hsource⟩ :=
    ETHScaleColumnCandidate.column_candidate (n+2)
  let T : Stack → List Bool := bank candidateEmbed (finalBank n) C
  have hstart : stackCfg candidateEmbed (finalBank n)
      (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
        (ETHParameterScaleMachineLogCopy.copyControl none, none),
        ETHScaleColumnCandidate.initial (n+2)⟩ :
        TM2.Cfg (fun _ : ETHScaleColumnCandidate.Stack => Bool)
          ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control) =
      (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
        (ETHParameterScaleMachineLogCopy.copyControl none, none),
        finalBank n⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control) := by
    apply congrArg (fun W : Stack → List Bool =>
      (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
        (ETHParameterScaleMachineLogCopy.copyControl none, none), W⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control))
    exact bank_eq_self candidateEmbed (finalBank n)
      (ETHScaleColumnCandidate.initial (n+2))
        (fun k => (prepared_candidate_bank n k).symm)
  have hsecond :
      ((advance (fun l => stackStmt candidateEmbed
        (ETHScaleColumnCandidate.program l)))^[tc])
        (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
          (ETHParameterScaleMachineLogCopy.copyControl none, none),
          finalBank n⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control) =
        ⟨none, (ETHParameterScaleMachineLogCopy.copyControl none, none), T⟩ := by
    have h := BitMachineStackRun.run candidateEmbed (finalBank n)
      ETHScaleColumnCandidate.program
      (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
        (ETHParameterScaleMachineLogCopy.copyControl none, none),
        ETHScaleColumnCandidate.initial (n+2)⟩ :
        TM2.Cfg (fun _ : ETHScaleColumnCandidate.Stack => Bool)
          ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control) tc
    rw [hstart, hc] at h
    simpa only [T, stackCfg] using h
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    program
    (fun l => stackStmt candidateEmbed (ETHScaleColumnCandidate.program l))
    (BitMachineRawSequence.leftLabel .scan)
    (BitMachineRawSequence.leftLabel (.inl .scan))
    (none, ()) (none, ())
    (ETHParameterScaleMachineLogCopy.copyControl none, none)
    (ETHParameterScaleMachineLogCopy.copyControl none, none)
    (initial n) (finalBank n) T tp tc hp hsecond
  refine ⟨t, by omega, T, ?_, ?_, ?_⟩
  · simpa only [fullProgram] using hr
  · have hout : ¬ ∃ k : ETHScaleColumnCandidate.Stack,
        candidateEmbed k = raw := by
      rintro ⟨k, hk⟩
      cases hk
    rw [show T raw = finalBank n raw from
      bank_outside candidateEmbed (finalBank n) C raw hout]
    exact _hraw
  · exact (bank_at candidateEmbed (finalBank n) C (.inr 0)).trans
      hcandidate

end EthInapproximability.CurrentPaper.ETHScaleEdgePreparation
