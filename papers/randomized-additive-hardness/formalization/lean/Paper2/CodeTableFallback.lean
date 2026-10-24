import Paper2.CodeFullRunConsumer
import EthInapproximability.CurrentPaper.MatrixTableWriter
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import Mathlib.Tactic

/-! A physical false-cell instance of the row-major table writer. -/

namespace Paper2.CodeTableFallback

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.MatrixTableWriter
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineClearBank
open EthInapproximability.CurrentPaper.BitMachineStackGrowth

noncomputable section

abbrev CellStack := MatrixTableWriter.CellStack 0
abbrev CellLabel := Unit
abbrev CellControl := Unit

def falseCell : CellLabel → TM2.Stmt (fun _ : CellStack => Bool) CellLabel CellControl
  | () => push (.inr 2) (fun _ => false) halt

def emptyBank : Fin 0 → List Bool := Fin.elim0

theorem falseCell_run (x y : Nat) :
    ((advance falseCell)^[1])
      (MatrixTableWriter.cellCfg (some ()) () emptyBank x y []) =
      MatrixTableWriter.cellCfg none () emptyBank x y [false] := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero,
    id_eq, advance, TM2.step, TM2.stepAux, falseCell,
    MatrixTableWriter.cellCfg, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => exact k.elim0
  | inr k => fin_cases k <;> rfl

theorem falseCell_entryRuns (r c : Nat) :
    MatrixTableWriter.EntryRuns falseCell () () emptyBank r c 1
      (fun _ _ => false) := by
  intro x hx y hy
  exact ⟨1, le_refl _, (), falseCell_run x y⟩

theorem write_zero_table (r c : Nat) :
    ∃ t ≤ MatrixTableWriter.writerBound r c 1, ∃ v,
      MatrixTableWriter.run falseCell () () t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) ((), none)
          (MatrixTableWriter.ready emptyBank r c 0 0 0 0 [] [])) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready emptyBank r c 0 0 0 0 []
          (MatrixMaterialization.rowMajor (fun (_ : Fin r) (_ : Fin c) => false))) := by
  simpa using MatrixTableWriter.write_rowMajor falseCell () () emptyBank
    r c 1 (fun _ _ => false) (fun _ _ => false)
    (by intro x y; rfl) (falseCell_entryRuns r c) []

/-- The ambient includes the whole generator interpreter, a disjoint table
writer with retained public dimensions, and a finite status bit. -/
abbrev WriterStack := MatrixTableWriter.Stack 0
abbrev WriterLabel := MatrixTableWriter.Label CellLabel
abbrev WriterControl := MatrixTableWriter.Control CellControl
abbrev Stack := CodeFullPadding.Stack ⊕ WriterStack
noncomputable instance : DecidableEq Stack := instDecidableEqSum
def interpreterIndex : CodeFullPadding.Stack ↪ Stack := Function.Embedding.inl
def writerIndex : WriterStack ↪ Stack := Function.Embedding.inr

inductive Admin where
  | route | clearOutput | handoff
  deriving DecidableEq, Fintype

abbrev Label := CodeFullPadding.Label ⊕ (Admin ⊕ WriterLabel)
abbrev Control := ((CodeFullPadding.Control × WriterControl) × Bool) × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def embedInterpreter (v : CodeFullPadding.Control) : Control :=
  (((v, ((), none)), true), none)

def embedWriter (v : WriterControl) : Control :=
  (((CodeFullRepeat.entryControl, v), false), none)

def writerStart : WriterLabel := .inr (.copy .rows)
def outputSlot : Stack := .inl CodeHeaderDraw.output

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      interpreterIndex Sum.inl embedInterpreter (fun v => v.1.1.1)
      (some (.inr (.inl .route))) (CodeFullPadding.program l)
  | .inr (.inl .route) =>
      branch (fun v => CodeFullPadding.doneStatus v.1.1.1)
        halt (goto (fun _ => .inr (.inl .clearOutput)))
  | .inr (.inl .clearOutput) =>
      clearStep outputSlot (.inr (.inl .clearOutput)) (.inr (.inl .handoff))
  | .inr (.inl .handoff) =>
      load (fun _ => embedWriter ((), none))
        (goto (fun _ => .inr (.inr writerStart)))
  | .inr (.inr l) => BitMachineStackEmbedding.stmt
      writerIndex (fun w => .inr (.inr w)) embedWriter
      (fun v => v.1.1.2) none
      (MatrixTableWriter.program falseCell () () l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def writerData (r c : Nat) : MatrixTableWriter.Data 0 :=
  MatrixTableWriter.ready emptyBank r c 0 0 0 0 [] []

def initial (s : GeneratorCode.State) (tape : List Bool)
    (B R mX mY : Nat) : Config :=
  let a := CodeFullPadding.start s tape B R
  BitMachineStackEmbedding.cfg interpreterIndex
    (Sum.elim a.stk (writerData mX mY).contents)
    Sum.inl embedInterpreter (some (.inr (.inl .route))) a

def routeCfg (v : CodeFullPadding.Control) (S : Stack → List Bool) : Config :=
  ⟨some (.inr (.inl .route)), embedInterpreter v, S⟩

private theorem run_add (a b : Nat) (c : Config) :
    run (a+b) c = run b (run a c) := by
  unfold run
  rw [Nat.add_comm a b, Function.iterate_add_apply]

private theorem bank_inl (S U : CodeFullPadding.Stack → List Bool)
    (T : WriterStack → List Bool) :
    BitMachineStackEmbedding.bank interpreterIndex
      (Sum.elim S T) U = Sum.elim U T := by
  funext j
  cases j with
  | inl k =>
      simpa only [interpreterIndex, Sum.elim_inl] using
        (BitMachineStackEmbedding.bank_at interpreterIndex (Sum.elim S T) U k)
  | inr k =>
      simpa only [Sum.elim_inr] using
        (BitMachineStackEmbedding.bank_outside
          interpreterIndex (Sum.elim S T) U (Sum.inr k : Stack)
          (by intro h; obtain ⟨x,hx⟩ := h
              change Sum.inl x = Sum.inr k at hx
              cases hx))

private theorem bank_inr (S : CodeFullPadding.Stack → List Bool)
    (T U : WriterStack → List Bool) :
    BitMachineStackEmbedding.bank writerIndex
      (Sum.elim S T) U = Sum.elim S U := by
  funext j
  cases j with
  | inl k =>
      simpa only [Sum.elim_inl] using
        (BitMachineStackEmbedding.bank_outside
          writerIndex (Sum.elim S T) U (Sum.inl k : Stack)
          (by intro h; obtain ⟨x,hx⟩ := h
              change Sum.inr x = Sum.inl k at hx
              cases hx))
  | inr k =>
      simpa only [writerIndex, Sum.elim_inr] using
        (BitMachineStackEmbedding.bank_at writerIndex (Sum.elim S T) U k)

theorem interpreter_to_route (s : GeneratorCode.State) (tape : List Bool)
    (B R mX mY t : Nat) (c : CodeFullPadding.Config)
    (h : CodeFullPadding.run t (CodeFullPadding.start s tape B R) = c)
    (hc : c.l = none) :
    ∃ u ≤ t, run u (initial s tape B R mX mY) =
      routeCfg c.var (Sum.elim c.stk (writerData mX mY).contents) := by
  let a := CodeFullPadding.start s tape B R
  let D := writerData mX mY
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs
    interpreterIndex (Sum.elim a.stk D.contents)
    Sum.inl embedInterpreter (fun v => v.1.1.1)
    (by intro v; rfl) (some (.inr (.inl .route)))
    CodeFullPadding.program program (by intro l; rfl) a t
    (by simpa [CodeFullPadding.run,a] using (congrArg TM2.Cfg.l h).trans hc)
  refine ⟨u,hu,?_⟩
  change ((advance program)^[u]) (initial s tape B R mX mY) = _
  change ((advance program)^[u]) (initial s tape B R mX mY) =
    BitMachineStackEmbedding.cfg interpreterIndex
      (Sum.elim a.stk D.contents) Sum.inl embedInterpreter
      (some (.inr (.inl .route)))
      (CodeFullPadding.run t a) at he
  rw [h] at he
  simpa only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,hc,bank_inl,routeCfg,a,D] using he

theorem route_success (v : CodeFullPadding.Control) (S : Stack → List Bool)
    (hv : CodeFullPadding.doneStatus v = true) :
    run 1 (routeCfg v S) = ⟨none,embedInterpreter v,S⟩ := by
  simp only [run,Function.iterate_succ_apply',Function.iterate_zero,id_eq]
  simp [routeCfg,program,advance,TM2.step,TM2.stepAux,
    embedInterpreter,hv]

theorem route_failure (v : CodeFullPadding.Control) (S : Stack → List Bool)
    (hv : CodeFullPadding.doneStatus v = false) :
    run 1 (routeCfg v S) =
      ⟨some (.inr (.inl .clearOutput)),embedInterpreter v,S⟩ := by
  simp only [run,Function.iterate_succ_apply',Function.iterate_zero,id_eq]
  simp [routeCfg,program,advance,TM2.step,TM2.stepAux,
    embedInterpreter,hv]

theorem handoff_step (S : Stack → List Bool)
    (v : Control) :
    run 1 ⟨some (.inr (.inl .handoff)),v,S⟩ =
      ⟨some (.inr (.inr writerStart)),embedWriter ((),none),S⟩ := by
  simp [run,program,advance,TM2.step,TM2.stepAux]

theorem writer_from_handoff (S : CodeFullPadding.Stack → List Bool)
    (r c : Nat) :
    ∃ t ≤ MatrixTableWriter.writerBound r c 1, ∃ v,
      run t ⟨some (.inr (.inr writerStart)),
          embedWriter ((),none),Sum.elim S (writerData r c).contents⟩ =
        ⟨none,embedWriter v,
          Sum.elim S (MatrixTableWriter.ready emptyBank r c 0 0 0 0 []
            (MatrixMaterialization.rowMajor
              (fun (_ : Fin r) (_ : Fin c) => false))).contents⟩ := by
  obtain ⟨bound,hbound,v,hwrite⟩ := write_zero_table r c
  let d := writerData r c
  let e := MatrixTableWriter.ready emptyBank r c 0 0 0 0 []
    (MatrixMaterialization.rowMajor (fun (_ : Fin r) (_ : Fin c) => false))
  let a : MatrixTableWriter.Config 0 CellLabel CellControl :=
    MatrixTableWriter.cfg (some writerStart) ((),none) d
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs
    writerIndex (Sum.elim S d.contents) (fun l => .inr (.inr l))
    embedWriter (fun v => v.1.1.2) (by intro v; rfl) none
    (MatrixTableWriter.program falseCell () ()) program (by intro l; rfl)
    a bound (by simpa [MatrixTableWriter.run,a,d] using congrArg TM2.Cfg.l hwrite)
  refine ⟨t,ht.trans hbound,v,?_⟩
  change ((advance program)^[t])
      (BitMachineStackEmbedding.cfg writerIndex (Sum.elim S d.contents)
        (fun l => .inr (.inr l)) embedWriter none a) =
    BitMachineStackEmbedding.cfg writerIndex (Sum.elim S d.contents)
      (fun l => .inr (.inr l)) embedWriter none
      (MatrixTableWriter.run falseCell () () bound a) at he
  change MatrixTableWriter.run falseCell () () bound a =
    MatrixTableWriter.cfg none v e at hwrite
  rw [hwrite] at he
  simpa only [run,BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,
    bank_inr,MatrixTableWriter.cfg,a,d,e,writerStart] using he

theorem failure_from_route (v : CodeFullPadding.Control)
    (S : CodeFullPadding.Stack → List Bool) (r c : Nat)
    (hv : CodeFullPadding.doneStatus v = false) :
    ∃ t ≤ (S CodeHeaderDraw.output).length +
        MatrixTableWriter.writerBound r c 1 + 3, ∃ w,
      run t (routeCfg v (Sum.elim S (writerData r c).contents)) =
        ⟨none,embedWriter w,
          Sum.elim (Function.update S CodeHeaderDraw.output [])
            (MatrixTableWriter.ready emptyBank r c 0 0 0 0 []
              (MatrixMaterialization.rowMajor
                (fun (_ : Fin r) (_ : Fin c) => false))).contents⟩ := by
  let D := writerData r c
  let S₀ : Stack → List Bool := Sum.elim S D.contents
  let S₁ := Function.update S₀ outputSlot []
  let Sleft := Function.update S CodeHeaderDraw.output []
  have hroute := route_failure v S₀ hv
  have hclear := BitMachineClearBank.clear_one_run program outputSlot
    (.inr (.inl .clearOutput)) (.inr (.inl .handoff)) rfl
    (((v,((),none)),true) : (CodeFullPadding.Control × WriterControl) × Bool) S₀
  change run ((S₀ outputSlot).length+1)
      ⟨some (.inr (.inl .clearOutput)),embedInterpreter v,S₀⟩ =
    ⟨some (.inr (.inl .handoff)),embedInterpreter v,S₁⟩ at hclear
  have hS₁ : S₁ = Sum.elim Sleft D.contents := by
    simpa only [S₁,S₀,Sleft,outputSlot] using
      (BitMachineComposition.sum_update S D.contents CodeHeaderDraw.output [])
  obtain ⟨tw,htw,w,hwriter⟩ := writer_from_handoff Sleft r c
  refine ⟨1 + ((S₀ outputSlot).length+1) + 1 + tw,?_,w,?_⟩
  · simp only [S₀,outputSlot,Sum.elim_inl] at *
    omega
  · rw [run_add (1 + ((S₀ outputSlot).length+1) + 1) tw,
      run_add (1 + ((S₀ outputSlot).length+1)) 1,
      run_add 1 ((S₀ outputSlot).length+1),hroute,hclear,
      handoff_step,hS₁,hwriter]

theorem failure_from_initial (s : GeneratorCode.State) (tape : List Bool)
    (B R r c t : Nat) (d : CodeFullPadding.Config)
    (h : CodeFullPadding.run t (CodeFullPadding.start s tape B R) = d)
    (hd : d.l = none)
    (hf : CodeFullPadding.doneStatus d.var = false) :
    ∃ clock ≤ t + (d.stk CodeHeaderDraw.output).length +
        MatrixTableWriter.writerBound r c 1 + 3, ∃ w,
      run clock (initial s tape B R r c) =
        ⟨none,embedWriter w,
          Sum.elim (Function.update d.stk CodeHeaderDraw.output [])
            (MatrixTableWriter.ready emptyBank r c 0 0 0 0 []
              (MatrixMaterialization.rowMajor
                (fun (_ : Fin r) (_ : Fin c) => false))).contents⟩ := by
  obtain ⟨u,hu,hr⟩ := interpreter_to_route s tape B R r c t d h hd
  obtain ⟨v,hv,w,hw⟩ := failure_from_route d.var d.stk r c hf
  refine ⟨u+v,by omega,w,?_⟩
  rw [run_add,hr,hw]

theorem success_from_initial (s : GeneratorCode.State) (tape : List Bool)
    (B R r c t : Nat) (d : CodeFullPadding.Config)
    (h : CodeFullPadding.run t (CodeFullPadding.start s tape B R) = d)
    (hd : d.l = none)
    (hs : CodeFullPadding.doneStatus d.var = true) :
    ∃ clock ≤ t+1,
      run clock (initial s tape B R r c) =
        ⟨none,embedInterpreter d.var,
          Sum.elim d.stk (writerData r c).contents⟩ := by
  obtain ⟨u,hu,hr⟩ := interpreter_to_route s tape B R r c t d h hd
  refine ⟨u+1,by omega,?_⟩
  rw [run_add,hr,route_success d.var _ hs]

theorem observed_none_status (d : CodeFullPadding.Config)
    (h : CodeFullRun.observed d = none) :
    CodeFullPadding.doneStatus d.var = false := by
  unfold CodeFullRun.observed at h
  cases hs : CodeFullPadding.doneStatus d.var <;> simp_all

theorem observed_some_status (d : CodeFullPadding.Config)
    (bytes : List Bool) (h : CodeFullRun.observed d = some bytes) :
    CodeFullPadding.doneStatus d.var = true := by
  unfold CodeFullRun.observed at h
  cases hs : CodeFullPadding.doneStatus d.var <;> simp_all

/-- A source-level capped failure causes this same fixed ambient program to
print the dimensioned zero table. The partial sampled-label word is consumed
before the writer starts. The old interpreter bank, including its residual
random tape, is retained except for that cleared output stack. -/
theorem source_failure_prints_zero (root : GeneratorCode.Code)
    (M B R N r c : Nat) (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (s : GeneratorCode.BoundedState M)
    (hp : GeneratorPositive.PositiveState s.val)
    (ht : GeneratorStateSize.Trace root s.val)
    (tape : CappedSampler.Adaptive.Tape B R N)
    (hf : GeneratorCode.capped B R hMB N s tape = none) :
    ∃ clock₀ ≤ (GeneratorSerialization.codeSize root+1) *
        CodeFullRepeatPublic.repeatStepCap root B R,
      let d := CodeFullPadding.run clock₀
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N tape).val B R)
      ∃ clock ≤ clock₀ + (d.stk CodeHeaderDraw.output).length +
          MatrixTableWriter.writerBound r c 1 + 3,
        ∃ w, run clock
          (initial s.val (RecursiveSamplingTape.writeTape B R N tape).val
            B R r c) =
          ⟨none,embedWriter w,
            Sum.elim (Function.update d.stk CodeHeaderDraw.output [])
              (MatrixTableWriter.ready emptyBank r c 0 0 0 0 []
                (MatrixMaterialization.rowMajor
                  (fun (_ : Fin r) (_ : Fin c) => false))).contents⟩ := by
  obtain ⟨clock₀,hclock₀,hdone,hobs,_⟩ :=
    CodeFullRun.capped_failure_observed root M B R hMB hR N s hp ht tape hf []
  refine ⟨clock₀,hclock₀,?_⟩
  exact failure_from_initial s.val
    (RecursiveSamplingTape.writeTape B R N tape).val B R r c clock₀ _
    rfl hdone (observed_none_status _ hobs)

/-- The source-facing failure hypothesis is the actual `GeneratorCode.run`,
not a supplied capped-branch choice or an already prepared machine bank. -/
theorem source_run_failure_prints_zero (root : GeneratorCode.Code)
    (M B R N r c : Nat) (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (s : GeneratorCode.BoundedState M)
    (hp : GeneratorPositive.PositiveState s.val)
    (ht : GeneratorStateSize.Trace root s.val)
    (hN : (GeneratorCode.semantic s).val.maxDraws ≤ N)
    (tape : CappedSampler.Adaptive.Tape B R N)
    (hf : GeneratorCode.run B R hMB N s tape = none) :
    ∃ clock₀ ≤ (GeneratorSerialization.codeSize root+1) *
        CodeFullRepeatPublic.repeatStepCap root B R,
      let d := CodeFullPadding.run clock₀
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N tape).val B R)
      ∃ clock ≤ clock₀ + (d.stk CodeHeaderDraw.output).length +
          MatrixTableWriter.writerBound r c 1 + 3,
        ∃ w, run clock
          (initial s.val (RecursiveSamplingTape.writeTape B R N tape).val
            B R r c) =
          ⟨none,embedWriter w,
            Sum.elim (Function.update d.stk CodeHeaderDraw.output [])
              (MatrixTableWriter.ready emptyBank r c 0 0 0 0 []
                (MatrixMaterialization.rowMajor
                  (fun (_ : Fin r) (_ : Fin c) => false))).contents⟩ := by
  exact source_failure_prints_zero root M B R N r c hMB hR s hp ht tape
    ((CodeFullRunConsumer.run_none_iff_capped M B R N hMB s hN tape).mp hf)

private noncomputable instance : Fintype CodeFullPadding.Label := by
  classical
  exact Fintype.ofFinite _

def interpreterPushBound : Nat := perStep CodeFullPadding.program

theorem interpreter_output_growth (s : GeneratorCode.State)
    (tape : List Bool) (B R t : Nat) (d : CodeFullPadding.Config)
    (h : CodeFullPadding.run t (CodeFullPadding.start s tape B R) = d) :
    (d.stk CodeHeaderDraw.output).length ≤
      ((CodeFullPadding.start s tape B R).stk CodeHeaderDraw.output).length +
        interpreterPushBound * t := by
  have hg := BitMachineStackGrowth.run_growth CodeFullPadding.program
    (CodeFullPadding.start s tape B R) t CodeHeaderDraw.output
  change ((CodeFullPadding.run t
    (CodeFullPadding.start s tape B R)).stk CodeHeaderDraw.output).length ≤
    ((CodeFullPadding.start s tape B R).stk CodeHeaderDraw.output).length +
      interpreterPushBound * t at hg
  rw [h] at hg
  exact hg

theorem interpreter_start_output (s : GeneratorCode.State)
    (tape : List Bool) (B R : Nat) :
    (CodeFullPadding.start s tape B R).stk CodeHeaderDraw.output =
      s.output.reverse := by
  change (BitMachineStackEmbedding.bank CodeAdminDraw.adminSlot
    (CodeAdminDraw.foreign tape B R)
    (CodeAdminNormalization.stateCfg s).stk) CodeHeaderDraw.output = _
  rw [← show CodeAdminDraw.adminSlot (.inr 0) = CodeHeaderDraw.output by rfl,
    BitMachineStackEmbedding.bank_at]
  rfl

theorem interpreter_output_public (root : GeneratorCode.Code)
    (s : GeneratorCode.State) (ht : GeneratorStateSize.Trace root s)
    (tape : List Bool) (B R t : Nat) (d : CodeFullPadding.Config)
    (h : CodeFullPadding.run t (CodeFullPadding.start s tape B R) = d) :
    (d.stk CodeHeaderDraw.output).length ≤
      GeneratorSerialization.codeSize root + interpreterPushBound*t := by
  have hg := interpreter_output_growth s tape B R t d h
  rw [interpreter_start_output,List.length_reverse] at hg
  have hs := GeneratorStateSize.trace_output_length_le root s ht
  omega

def sourceFailureCap (root : GeneratorCode.Code)
    (B R r c : Nat) : Nat :=
  let core := (GeneratorSerialization.codeSize root+1) *
    CodeFullRepeatPublic.repeatStepCap root B R
  core + GeneratorSerialization.codeSize root +
    interpreterPushBound*core + MatrixTableWriter.writerBound r c 1 + 3

theorem source_run_failure_public (root : GeneratorCode.Code)
    (M B R N r c : Nat) (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (s : GeneratorCode.BoundedState M)
    (hp : GeneratorPositive.PositiveState s.val)
    (ht : GeneratorStateSize.Trace root s.val)
    (hN : (GeneratorCode.semantic s).val.maxDraws ≤ N)
    (tape : CappedSampler.Adaptive.Tape B R N)
    (hf : GeneratorCode.run B R hMB N s tape = none) :
    ∃ clock ≤ sourceFailureCap root B R r c,
      ∃ (d : CodeFullPadding.Config) (w : WriterControl),
        run clock (initial s.val
          (RecursiveSamplingTape.writeTape B R N tape).val B R r c) =
        ⟨none,embedWriter w,
          Sum.elim (Function.update d.stk CodeHeaderDraw.output [])
            (MatrixTableWriter.ready emptyBank r c 0 0 0 0 []
              (MatrixMaterialization.rowMajor
                (fun (_ : Fin r) (_ : Fin c) => false))).contents⟩ ∧
        ∃ clock₀ ≤ (GeneratorSerialization.codeSize root+1) *
            CodeFullRepeatPublic.repeatStepCap root B R,
          d = CodeFullPadding.run clock₀
            (CodeFullPadding.start s.val
              (RecursiveSamplingTape.writeTape B R N tape).val B R) := by
  obtain ⟨clock₀,hclock₀,clock,hclock,w,hr⟩ :=
    source_run_failure_prints_zero root M B R N r c hMB hR
      s hp ht hN tape hf
  let d := CodeFullPadding.run clock₀
    (CodeFullPadding.start s.val
      (RecursiveSamplingTape.writeTape B R N tape).val B R)
  have hout := interpreter_output_public root s.val ht
    (RecursiveSamplingTape.writeTape B R N tape).val B R clock₀ d rfl
  have hmul := Nat.mul_le_mul_left interpreterPushBound hclock₀
  refine ⟨clock,?_,d,w,hr,clock₀,hclock₀,rfl⟩
  change clock ≤ clock₀ + (d.stk CodeHeaderDraw.output).length +
    MatrixTableWriter.writerBound r c 1 + 3 at hclock
  dsimp [sourceFailureCap]
  omega

#print axioms source_run_failure_public

theorem scheduled_failure_public {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat)
    (activity : SourceConstruction.Items (SourceProfileParameters.width L)
      (Fin n) → Fin (SourceProfileParameters.outerWidth L) →
      Option (Fin (SourceProfileParameters.width L)))
    (ξ : RecursiveEntries.Tails (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ))
    (k mX mY : Nat)
    (tape : CappedSampler.Adaptive.Tape
      (Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ))
      (Paper2.rejectionAttemptCap
        (CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY))
      (CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY))
    (hf :
      let root := GeneratorFullSample.scheduledSampleCode n m L Δ γ k mX mY
      let M := CodeFullRunConsumer.scheduledM n m L Δ γ
      let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
      let B := Nat.clog 2 M
      let R := Paper2.rejectionAttemptCap N
      let hM := CodeFullRunConsumer.scheduled_sample_code_alphabet_cap
        L Δ γ activity ξ k mX mY
      let s := GeneratorStateSize.initialBounded root hM
      GeneratorCode.run B R le_rfl N s tape = none) :
    let root := GeneratorFullSample.scheduledSampleCode n m L Δ γ k mX mY
    let M := CodeFullRunConsumer.scheduledM n m L Δ γ
    let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
    let B := Nat.clog 2 M
    let R := Paper2.rejectionAttemptCap N
    ∃ clock ≤ sourceFailureCap root B R mX mY,
      ∃ (d : CodeFullPadding.Config) (w : WriterControl),
        run clock (initial (GeneratorCode.initial root)
          (RecursiveSamplingTape.writeTape B R N tape).val
          B R mX mY) =
          ⟨none,embedWriter w,
            Sum.elim (Function.update d.stk CodeHeaderDraw.output [])
              (MatrixTableWriter.ready emptyBank mX mY 0 0 0 0 []
                (MatrixMaterialization.rowMajor
                  (fun (_ : Fin mX) (_ : Fin mY) => false))).contents⟩ := by
  let root := GeneratorFullSample.scheduledSampleCode n m L Δ γ k mX mY
  let M := CodeFullRunConsumer.scheduledM n m L Δ γ
  let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
  let B := Nat.clog 2 M
  let R := Paper2.rejectionAttemptCap N
  let hM := CodeFullRunConsumer.scheduled_sample_code_alphabet_cap
    L Δ γ activity ξ k mX mY
  let s := GeneratorStateSize.initialBounded root hM
  have hN : (GeneratorCode.semantic s).val.maxDraws ≤ N := by
    rw [CodeFullRunConsumer.initial_semantic_draws]
    exact CodeFullRunConsumer.scheduled_sample_code_draw_cap
      L Δ γ k mX mY
  have hp : GeneratorPositive.PositiveState s.val := by
    exact GeneratorPositive.positive_initial root
      (GeneratorPositive.positive_scheduledSampleCode L Δ γ k mX mY)
  have hR : 0 < R := CodeFullRun.scheduled_attempts_pos N
  obtain ⟨clock,hclock,d,w,hr,_⟩ :=
    source_run_failure_public root M B R N mX mY le_rfl hR
      s hp GeneratorStateSize.Trace.initial hN tape hf
  refine ⟨clock,hclock,d,w,?_⟩
  simpa only [s,GeneratorStateSize.initialBounded] using hr

#print axioms scheduled_failure_public

#print axioms interpreter_output_public

#print axioms source_run_failure_prints_zero

#print axioms source_failure_prints_zero

#print axioms failure_from_route
#print axioms failure_from_initial
#print axioms success_from_initial

#print axioms falseCell_run
#print axioms falseCell_entryRuns
#print axioms write_zero_table

end
end Paper2.CodeTableFallback
