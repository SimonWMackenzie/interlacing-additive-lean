import CurrentAdditive.CodeDKeepFlagV2
import CurrentAdditive.CodeDZeroEntryV2
import EthInapproximability.CurrentPaper.SourceListMachineWriter
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
One post-update entry is copied exactly, classified by the controller's
physical numerator test, and framed only on the nonzero branch.  The copied
entry sits in the writer's input bank while the zero test runs.
-/

namespace CurrentAdditive.CodeDKeepEntryV2

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

private noncomputable abbrev Z := CodeDZeroEntryV2.machine
private noncomputable abbrev W := SourceListMachineWriter.framingMachine true

inductive Admin where
  | afterCopy | afterTest
  deriving DecidableEq, Fintype

abbrev Stack := Fin Z.stackCount ⊕ (Fin W.stackCount ⊕ Unit)
abbrev Label := BitMachineCopy.Label ⊕
  (Fin Z.labelCount ⊕ (Fin W.labelCount ⊕ Admin))
abbrev Control := (Option Bool × Fin Z.controlCount) ×
  (Fin W.controlCount × Option Bool)

noncomputable def copyStack : Fin 3 ↪ Stack where
  toFun
    | 0 => .inl Z.input
    | 1 => .inr (.inl W.input)
    | 2 => .inr (.inr ())
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

noncomputable def zeroStack : Fin Z.stackCount ↪ Stack :=
  ⟨Sum.inl, Sum.inl_injective⟩

noncomputable def writerStack : Fin W.stackCount ↪ Stack :=
  ⟨fun k => .inr (.inl k), by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)⟩

noncomputable def copyControl (v : Option Bool) : Control :=
  ((v,Z.initial),(W.initial,none))

noncomputable def zeroControl (v : Fin Z.controlCount) : Control :=
  ((none,v),(W.initial,none))

noncomputable def writerControl (v : Fin W.controlCount) : Control :=
  ((none,Z.initial),(v,none))

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt copyStack Sum.inl
      copyControl (fun v => v.1.1) (some (.inr (.inr (.inr .afterCopy))))
      (BitMachineCopy.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt zeroStack
      (fun l => .inr (.inl l)) zeroControl (fun v => v.1.2)
      (some (.inr (.inr (.inr .afterTest)))) (Z.program l)
  | .inr (.inr (.inl l)) => BitMachineStackEmbedding.stmt writerStack
      (fun l => .inr (.inr (.inl l))) writerControl (fun v => v.2.1)
      none (W.program l)
  | .inr (.inr (.inr .afterCopy)) =>
      load (fun _ => zeroControl Z.initial)
        (goto (fun _ => .inr (.inl Z.start)))
  | .inr (.inr (.inr .afterTest)) =>
      peek (.inl Z.output) (fun v b => (v.1,(v.2.1,b)))
        (branch (fun v => v.2.2 == some true)
          halt
          (load (fun _ => writerControl W.initial)
            (goto (fun _ => .inr (.inr (.inl W.start))))))

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inl Z.input) (.inr (.inl W.output))
    (.inl .scan) (copyControl none) program

def result (input : List Bool) : List Bool :=
  if CodeDZeroEntryV2.result input = [true] then []
  else SourceListMachineWriter.result true input

private noncomputable def initialBank (x : List Bool) : Stack → List Bool :=
  fun k => if k = .inl Z.input then x else []

private noncomputable def copyBank (x : List Bool) : Stack → List Bool :=
  fun k => if k = .inl Z.input then x else
    if k = .inr (.inl W.input) then x else []

private theorem copyBank_at (x : List Bool) :
    BitMachineStackEmbedding.bank copyStack (initialBank x)
      (BitMachineCopy.stackContents x [] []) = initialBank x := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> simp [copyStack, initialBank, BitMachineCopy.stackContents]

private theorem copyBank_final (x : List Bool) :
    BitMachineStackEmbedding.bank copyStack (initialBank x)
      (BitMachineCopy.stackContents x x []) = copyBank x := by
  funext k
  cases k with
  | inl z =>
      by_cases hz : z = Z.input
      · subst z
        rw [show (Sum.inl Z.input : Stack) = copyStack (0 : Fin 3) from rfl]
        rw [BitMachineStackEmbedding.bank_at]
        simp [copyBank, copyStack, BitMachineCopy.stackContents]
      · have hout : ¬ ∃ j : Fin 3, copyStack j = Sum.inl z := by
          intro h
          obtain ⟨j, hj⟩ := h
          fin_cases j <;> simp [copyStack] at hj <;> exact hz hj.symm
        rw [BitMachineStackEmbedding.bank_outside copyStack _ _ _ hout]
        simp [initialBank, copyBank, hz]
  | inr p =>
      cases p with
      | inl w =>
          by_cases hw : w = W.input
          · subst w
            have h := BitMachineStackEmbedding.bank_at copyStack (initialBank x)
              (BitMachineCopy.stackContents x x []) (1 : Fin 3)
            simpa [copyStack, copyBank, BitMachineCopy.stackContents] using h
          · have hout : ¬ ∃ j : Fin 3, copyStack j = Sum.inr (Sum.inl w) := by
              intro h
              obtain ⟨j, hj⟩ := h
              fin_cases j <;> simp [copyStack] at hj <;> exact hw hj.symm
            rw [BitMachineStackEmbedding.bank_outside copyStack _ _ _ hout]
            simp [initialBank, copyBank, hw]
      | inr _ =>
          have h := BitMachineStackEmbedding.bank_at copyStack (initialBank x)
            (BitMachineCopy.stackContents x x []) (2 : Fin 3)
          simpa [copyStack, copyBank, BitMachineCopy.stackContents] using h

private theorem copy_phase (x : List Bool) :
    ∃ t ≤ 2*x.length+2,
      ((advance program)^[t])
        (⟨some (.inl .scan), copyControl none, initialBank x⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨some (.inr (.inr (.inr .afterCopy))),
          copyControl none, copyBank x⟩ := by
  have h := BitMachineStackEmbedding.outputs copyStack (initialBank x)
    (fun l : BitMachineCopy.Label => (Sum.inl l : Label))
    copyControl (fun v : Control => v.1.1)
    (by intro v; rfl)
    (some (.inr (.inr (.inr .afterCopy))))
    BitMachineCopy.program program (by intro l; rfl)
    (BitMachineCopy.cfg (some .scan) none x [] [])
    (2*x.length+2) (by rw [← BitMachineCopy.run, BitMachineCopy.run_correct]; rfl)
  obtain ⟨t, ht, hrun⟩ := h
  refine ⟨t, ht, ?_⟩
  have hr : ((advance BitMachineCopy.program)^[2*x.length+2])
    (BitMachineCopy.cfg (some .scan) none x [] []) =
      BitMachineCopy.cfg none none x x [] := by
    simpa only [BitMachineCopy.run, List.append_nil] using
      BitMachineCopy.run_correct none x []
  rw [hr] at hrun
  simpa [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, BitMachineCopy.cfg, copyBank_at, copyBank_final,
    ] using hrun

private theorem zero_initial (x : List Bool) :
    BitMachineStackEmbedding.bank zeroStack (copyBank x)
      (Z.init x).stk = copyBank x := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  simp [zeroStack, copyBank, BitMachine.Machine.init]

private theorem after_copy_step (x : List Bool) :
    advance program
      (⟨some (.inr (.inr (.inr .afterCopy))),
        copyControl none, copyBank x⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (.inr (.inl Z.start)),
        zeroControl Z.initial, copyBank x⟩ := by
  rfl

private theorem zero_phase (x : List Bool) :
    ∃ t ≤ CodeDZeroEntryV2.clock x,
      ∃ u ≤ t,
        (Z.run t (Z.init x)).l = none ∧
        (Z.run t (Z.init x)).stk Z.output = CodeDZeroEntryV2.result x ∧
        ((advance program)^[u])
          (⟨some (.inr (.inl Z.start)),
            zeroControl Z.initial, copyBank x⟩ :
            TM2.Cfg (fun _ : Stack => Bool) Label Control) =
          BitMachineStackEmbedding.cfg zeroStack (copyBank x)
            (fun l : Fin Z.labelCount =>
              (Sum.inr (Sum.inl l) : Label)) zeroControl
            (some (.inr (.inr (.inr .afterTest))))
            (Z.run t (Z.init x)) := by
  obtain ⟨t, ht, hhalt, hout, _⟩ :=
    BitMachineCompositionArithmetic.first_halt Z (CodeDZeroEntryV2.outputs x)
  have h := BitMachineStackEmbedding.outputs zeroStack (copyBank x)
    (fun l : Fin Z.labelCount => (Sum.inr (Sum.inl l) : Label))
    zeroControl (fun v : Control => v.1.2)
    (by intro v; rfl)
    (some (.inr (.inr (.inr .afterTest))))
    Z.program program (by intro l; rfl)
    (Z.init x) t hhalt
  obtain ⟨u, hu, hrun⟩ := h
  refine ⟨t, ht, u, hu, hhalt, hout, ?_⟩
  simpa [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, zero_initial] using hrun

private theorem writer_initial (x : List Bool)
    (S : Fin Z.stackCount → List Bool) :
    BitMachineStackEmbedding.bank writerStack
      (BitMachineStackEmbedding.bank zeroStack (copyBank x) S)
      (W.init x).stk =
    BitMachineStackEmbedding.bank zeroStack (copyBank x) S := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  have hout : ¬ ∃ j : Fin Z.stackCount,
      zeroStack j = writerStack k := by
    intro h
    obtain ⟨j,hj⟩ := h
    cases hj
  rw [BitMachineStackEmbedding.bank_outside zeroStack _ _ _ hout]
  simp [copyBank, writerStack, BitMachine.Machine.init]

private theorem writer_phase (x : List Bool)
    (S : Fin Z.stackCount → List Bool) :
    ∃ t ≤ ((UnaryBinaryEncoding.coefficient+7)*(x.length+1)^2),
      ∃ u ≤ t,
        (W.run t (W.init x)).l = none ∧
        (W.run t (W.init x)).stk W.output =
          SourceListMachineWriter.result true x ∧
        ((advance program)^[u])
          (⟨some (.inr (.inr (.inl W.start))),
            writerControl W.initial,
            BitMachineStackEmbedding.bank zeroStack (copyBank x) S⟩ :
            TM2.Cfg (fun _ : Stack => Bool) Label Control) =
          BitMachineStackEmbedding.cfg writerStack
            (BitMachineStackEmbedding.bank zeroStack (copyBank x) S)
            (fun l : Fin W.labelCount =>
              (Sum.inr (Sum.inr (Sum.inl l)) : Label)) writerControl
            none (W.run t (W.init x)) := by
  obtain ⟨t, ht, hhalt, hout, _⟩ :=
    BitMachineCompositionArithmetic.first_halt W
      (SourceListMachineWriter.outputs true x)
  have h := BitMachineStackEmbedding.outputs writerStack
    (BitMachineStackEmbedding.bank zeroStack (copyBank x) S)
    (fun l : Fin W.labelCount =>
      (Sum.inr (Sum.inr (Sum.inl l)) : Label))
    writerControl (fun v : Control => v.2.1)
    (by intro v; rfl) none
    W.program program (by intro l; rfl)
    (W.init x) t hhalt
  obtain ⟨u, hu, hrun⟩ := h
  refine ⟨t, ht, u, hu, hhalt, hout, ?_⟩
  simpa [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, writer_initial] using hrun

private theorem writer_input_ne_output : W.input ≠ W.output := by
  intro h
  simp [W, SourceListMachineWriter.framingMachine,
    SourceListMachineWriter.machine, BitMachineEncoding.ofFinite] at h

private theorem zeroBank_writer_output (x : List Bool)
    (S : Fin Z.stackCount → List Bool) :
    (BitMachineStackEmbedding.bank zeroStack (copyBank x) S)
      (.inr (.inl W.output)) = [] := by
  have hout : ¬ ∃ j : Fin Z.stackCount,
      zeroStack j = (Sum.inr (Sum.inl W.output) : Stack) := by
    intro h
    obtain ⟨j,hj⟩ := h
    cases hj
  rw [BitMachineStackEmbedding.bank_outside zeroStack _ _ _ hout]
  simp [copyBank, writer_input_ne_output.symm]

private theorem writerBank_output (x : List Bool)
    (S : Fin Z.stackCount → List Bool)
    (T : Fin W.stackCount → List Bool) :
    (BitMachineStackEmbedding.bank writerStack
      (BitMachineStackEmbedding.bank zeroStack (copyBank x) S) T)
      (.inr (.inl W.output)) = T W.output := by
  have h := BitMachineStackEmbedding.bank_at writerStack
    (BitMachineStackEmbedding.bank zeroStack (copyBank x) S) T W.output
  simpa [writerStack] using h

private theorem after_test_zero (x : List Bool)
    (v : Fin Z.controlCount) (S : Fin Z.stackCount → List Bool)
    (hS : S Z.output = [true]) :
    advance program
      (⟨some (.inr (.inr (.inr .afterTest))), zeroControl v,
        BitMachineStackEmbedding.bank zeroStack (copyBank x) S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, ((none,v),(W.initial,some true)),
        BitMachineStackEmbedding.bank zeroStack (copyBank x) S⟩ := by
  have hflag : (BitMachineStackEmbedding.bank zeroStack (copyBank x) S)
      (.inl Z.output) = [true] := by
    simpa [zeroStack] using
      (BitMachineStackEmbedding.bank_at zeroStack (copyBank x) S Z.output).trans hS
  simp [advance, TM2.step, program, TM2.stepAux, zeroControl, hflag]

private theorem after_test_keep (x : List Bool)
    (v : Fin Z.controlCount) (S : Fin Z.stackCount → List Bool)
    (hS : S Z.output = [false]) :
    advance program
      (⟨some (.inr (.inr (.inr .afterTest))), zeroControl v,
        BitMachineStackEmbedding.bank zeroStack (copyBank x) S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (.inr (.inr (.inl W.start))), writerControl W.initial,
        BitMachineStackEmbedding.bank zeroStack (copyBank x) S⟩ := by
  have hflag : (BitMachineStackEmbedding.bank zeroStack (copyBank x) S)
      (.inl Z.output) = [false] := by
    simpa [zeroStack] using
      (BitMachineStackEmbedding.bank_at zeroStack (copyBank x) S Z.output).trans hS
  simp [advance, TM2.step, program, TM2.stepAux, zeroControl,
    writerControl, hflag]

noncomputable def clock (x : List Bool) : Nat :=
  2*x.length+2 + 1 + CodeDZeroEntryV2.clock x + 1 +
    (UnaryBinaryEncoding.coefficient+7)*(x.length+1)^2

private theorem initial_eq (x : List Bool) :
    rawInit (.inl Z.input : Stack) (.inl .scan : Label)
      (copyControl none) x =
    (⟨some (.inl .scan), copyControl none, initialBank x⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control) := by
  simp only [rawInit]
  congr 1

theorem zero_result_flag (x : List Bool) :
    CodeDZeroEntryV2.result x = [true] ∨
      CodeDZeroEntryV2.result x = [false] := by
  cases h : !((CodeDZeroEntryV2.numeratorWord x).any id) <;>
    simp [CodeDZeroEntryV2.result, h]

theorem outputs (x : List Bool) :
    machine.OutputsWithin x (result x) (clock x) := by
  obtain ⟨tc, htc, hcopy⟩ := copy_phase x
  obtain ⟨tz, htz, uz, huz, hzhalt, hzout, hzrun⟩ := zero_phase x
  rcases zero_result_flag x with hzero | hkeep
  · have hstep := after_test_zero x (Z.run tz (Z.init x)).var
      (Z.run tz (Z.init x)).stk (hzout.trans hzero)
    have hrun : ((advance program)^[tc+1+uz+1])
        (rawInit (.inl Z.input : Stack) (.inl .scan : Label)
          (copyControl none) x) =
        ⟨none,
          ((none,(Z.run tz (Z.init x)).var), (W.initial,some true)),
          BitMachineStackEmbedding.bank zeroStack (copyBank x)
            (Z.run tz (Z.init x)).stk⟩ := by
      rw [initial_eq]
      rw [show tc+1+uz+1 = 1+uz+1+tc by omega,
        Function.iterate_add_apply, hcopy,
        Function.iterate_add_apply, Function.iterate_one,
        after_copy_step,
        show 1+uz=uz+1 by omega,
        Function.iterate_succ_apply', hzrun,
        show BitMachineStackEmbedding.cfg zeroStack (copyBank x)
          (fun l : Fin Z.labelCount => (Sum.inr (Sum.inl l) : Label))
          zeroControl (some (.inr (.inr (.inr .afterTest))))
          (Z.run tz (Z.init x)) =
          ⟨some (.inr (.inr (.inr .afterTest))),
            zeroControl (Z.run tz (Z.init x)).var,
            BitMachineStackEmbedding.bank zeroStack (copyBank x)
              (Z.run tz (Z.init x)).stk⟩ by
            simp [BitMachineStackEmbedding.cfg,
              BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hzhalt],
        hstep]
    apply outputsWithin_of_raw_run (.inl Z.input : Stack)
      (.inr (.inl W.output) : Stack) (.inl .scan : Label)
      (copyControl none) program x (result x) (tc+1+uz+1)
      (clock x) (by unfold clock; omega)
    · rw [hrun]
    · rw [hrun]
      simp [result, hzero, zeroBank_writer_output]
  · have hstep := after_test_keep x (Z.run tz (Z.init x)).var
      (Z.run tz (Z.init x)).stk (hzout.trans hkeep)
    have hpre : ((advance program)^[tc+1+uz+1])
        (rawInit (.inl Z.input : Stack) (.inl .scan : Label)
          (copyControl none) x) =
        ⟨some (.inr (.inr (.inl W.start))), writerControl W.initial,
          BitMachineStackEmbedding.bank zeroStack (copyBank x)
            (Z.run tz (Z.init x)).stk⟩ := by
      rw [initial_eq]
      rw [show tc+1+uz+1 = 1+uz+1+tc by omega,
        Function.iterate_add_apply, hcopy,
        Function.iterate_add_apply, Function.iterate_one,
        after_copy_step,
        show 1+uz=uz+1 by omega,
        Function.iterate_succ_apply', hzrun,
        show BitMachineStackEmbedding.cfg zeroStack (copyBank x)
          (fun l : Fin Z.labelCount => (Sum.inr (Sum.inl l) : Label))
          zeroControl (some (.inr (.inr (.inr .afterTest))))
          (Z.run tz (Z.init x)) =
          ⟨some (.inr (.inr (.inr .afterTest))),
            zeroControl (Z.run tz (Z.init x)).var,
            BitMachineStackEmbedding.bank zeroStack (copyBank x)
              (Z.run tz (Z.init x)).stk⟩ by
            simp [BitMachineStackEmbedding.cfg,
              BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hzhalt],
        hstep]
    obtain ⟨tw, htw, uw, huw, hwhalt, hwout, hwrun⟩ :=
      writer_phase x (Z.run tz (Z.init x)).stk
    have hrun : ((advance program)^[tc+1+uz+1+uw])
        (rawInit (.inl Z.input : Stack) (.inl .scan : Label)
          (copyControl none) x) =
        BitMachineStackEmbedding.cfg writerStack
          (BitMachineStackEmbedding.bank zeroStack (copyBank x)
            (Z.run tz (Z.init x)).stk)
          (fun l : Fin W.labelCount =>
            (Sum.inr (Sum.inr (Sum.inl l)) : Label)) writerControl
          none (W.run tw (W.init x)) := by
      rw [show tc+1+uz+1+uw = uw+(tc+1+uz+1) by omega,
        Function.iterate_add_apply, hpre, hwrun]
    apply outputsWithin_of_raw_run (.inl Z.input : Stack)
      (.inr (.inl W.output) : Stack) (.inl .scan : Label)
      (copyControl none) program x (result x) (tc+1+uz+1+uw)
      (clock x) (by unfold clock; omega)
    · rw [hrun]
      simp [BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hwhalt]
    · rw [hrun]
      change (BitMachineStackEmbedding.bank writerStack
        (BitMachineStackEmbedding.bank zeroStack (copyBank x)
          (Z.run tz (Z.init x)).stk)
        (W.run tw (W.init x)).stk) (.inr (.inl W.output)) = result x
      rw [writerBank_output, hwout]
      simp [result, hkeep]

#print axioms outputs

end CurrentAdditive.CodeDKeepEntryV2
