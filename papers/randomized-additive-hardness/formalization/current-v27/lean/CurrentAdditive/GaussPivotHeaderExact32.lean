import CurrentAdditive.GaussStepPivotAppendExactRun32

/-! Exact endpoint of the checked count-header worker, exposing context. -/

namespace CurrentAdditive.GaussPivotHeaderExact32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

private noncomputable abbrev W :=
  SourceListMachineWriter.framingMachine false
abbrev Stack := Fin 32

def workerResult (unary : List Bool) (S : Stack → List Bool)
    (c : W.Config) : Stack → List Bool :=
  (BitMachineStackEmbedding.cfg GaussPivotFraming32.locate
    (GaussPivotHeader32.afterIn unary S)
    GaussPivotHeader32.Label.writer
    (fun v => (((),none),v)) (some .resetOut) c :
      GaussPivotHeader32.Config).stk

theorem worker_out (unary : List Bool) (S : Stack → List Bool)
    (c : W.Config)
    (hout : c.stk W.output = SourceListMachineWriter.result false unary) :
    workerResult unary S c GaussPivotHeader32.outputSlot =
      SourceListMachineWriter.result false unary := by
  exact (BitMachineStackEmbedding.bank_at
    GaussPivotFraming32.locate (GaussPivotHeader32.afterIn unary S)
    c.stk W.output).trans hout

theorem worker31 (unary : List Bool) (S : Stack → List Bool)
    (c : W.Config) : workerResult unary S c 31 = [] := by
  change (BitMachineStackEmbedding.bank GaussPivotFraming32.locate
    (GaussPivotHeader32.afterIn unary S) c.stk) 31 = []
  rw [BitMachineStackEmbedding.bank_outside
    GaussPivotFraming32.locate _ _ 31 (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      fin_cases j <;> simp [GaussPivotFraming32.locate] at hv)]
  exact SourceClausePreservingBroadcast.temp_empty
    (5 : Stack) 31 [GaussPivotHeader32.inputSlot] unary S

theorem physical_exact (unary : List Bool)
    (S : Stack → List Bool)
    (h5 : S 5 = unary) (h31 : S 31 = [])
    (h30 : S 30 = [])
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (2*unary.length+3)+
        (UnaryBinaryEncoding.coefficient+7)*(unary.length+1)^2+1+
        (2*(SourceListMachineWriter.result false unary).length+3),
      ∃ c : W.Config,
        GaussPivotHeader32.run t
          ⟨some (.copyIn .scan),(((),none),W.initial),S⟩ =
        ⟨some .done,(((),none),W.initial),
          GaussPivotHeader32.afterOut
            (SourceListMachineWriter.result false unary)
            (workerResult unary S c)⟩ := by
  let payload := SourceListMachineWriter.result false unary
  obtain ⟨a,ha,hcopy⟩ :=
    GaussPivotHeader32.physical_copy_in unary S h5 h31
  obtain ⟨b,hb,c,hhalt,hout,hwriter⟩ :=
    GaussPivotHeader32.physical_writer_cfg unary S hempty
  let S2 := workerResult unary S c
  have hS2out : S2 GaussPivotHeader32.outputSlot = payload :=
    worker_out unary S c hout
  have hS231 : S2 31 = [] := worker31 unary S c
  have hwrite : GaussPivotHeader32.run b
      ⟨some (.writer W.start),(((),none),W.initial),
        GaussPivotHeader32.afterIn unary S⟩ =
      ⟨some .resetOut,(((),none),c.var),S2⟩ := by
    rw [hwriter]
    cases c with
    | mk l v stk =>
      cases l with
      | none => rfl
      | some l => cases hhalt
  have hreset : GaussPivotHeader32.run 1
      ⟨some .resetOut,(((),none),c.var),S2⟩ =
      ⟨some (.copyOut .scan),(((),none),W.initial),S2⟩ :=
    GaussPivotHeader32.reset_step S2 c.var
  obtain ⟨d,hd,houtcopy⟩ :=
    GaussPivotHeader32.physical_copy_out payload S2 hS2out hS231
  refine ⟨a+b+1+d,by dsimp [payload] at hd ⊢; omega,c,?_⟩
  rw [show a+b+1+d = ((a+b)+1)+d by omega]
  exact (GaussPivotHeader32.run_add
    ((GaussPivotHeader32.run_add hcopy b).trans hwrite) 1
    |>.trans hreset
    |> fun h => GaussPivotHeader32.run_add h d).trans houtcopy

theorem final_preserves (unary : List Bool)
    (S : Stack → List Bool) (c : W.Config) (j : Stack)
    (hj : j.val < 8 ∨ 16 ≤ j.val)
    (h5 : j ≠ 5) (h30 : j ≠ 30) (h31 : j ≠ 31) :
    GaussPivotHeader32.afterOut
      (SourceListMachineWriter.result false unary)
      (workerResult unary S c) j = S j := by
  have hin : j ≠ GaussPivotHeader32.inputSlot := by
    intro h
    have hv := congrArg Fin.val h
    have hh : W.input.val < 8 := W.input.isLt
    change j.val = W.input.val + 8 at hv
    rcases hj with hlow | hhigh <;> omega
  have hout : j ≠ GaussPivotHeader32.outputSlot := by
    intro h
    have hv := congrArg Fin.val h
    have hh : W.output.val < 8 := W.output.isLt
    change j.val = W.output.val + 8 at hv
    rcases hj with hlow | hhigh <;> omega
  unfold GaussPivotHeader32.afterOut
  rw [SourceClausePreservingBroadcast.other_preserved
    GaussPivotHeader32.outputSlot 31 [30]
    (SourceListMachineWriter.result false unary)
    (workerResult unary S c) j hout h31 (by simpa using h30)]
  change (BitMachineStackEmbedding.bank
    GaussPivotFraming32.locate
    (GaussPivotHeader32.afterIn unary S) c.stk) j = S j
  rw [BitMachineStackEmbedding.bank_outside
    GaussPivotFraming32.locate _ _ j (by
      rintro ⟨q,hq⟩
      have hv := congrArg Fin.val hq
      have hq' : q.val < 8 := q.isLt
      simp [GaussPivotFraming32.locate] at hv
      rcases hj with hlow | hhigh <;> omega)]
  exact SourceClausePreservingBroadcast.other_preserved
    (5 : Stack) 31 [GaussPivotHeader32.inputSlot]
    unary S j h5 h31 (by simpa using hin)

theorem final31_empty (unary : List Bool)
    (S : Stack → List Bool) (c : W.Config) :
    GaussPivotHeader32.afterOut
      (SourceListMachineWriter.result false unary)
      (workerResult unary S c) 31 = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

theorem final30 (unary : List Bool)
    (S : Stack → List Bool) (c : W.Config)
    (h30 : S 30 = []) :
    GaussPivotHeader32.afterOut
      (SourceListMachineWriter.result false unary)
      (workerResult unary S c) 30 =
        SourceListMachineWriter.result false unary := by
  have hworker : workerResult unary S c 30 = [] := by
    change (BitMachineStackEmbedding.bank GaussPivotFraming32.locate
      (GaussPivotHeader32.afterIn unary S) c.stk) 30 = []
    rw [BitMachineStackEmbedding.bank_outside
      GaussPivotFraming32.locate _ _ 30 (by
        rintro ⟨q,hq⟩
        have hv := congrArg Fin.val hq
        have hq' : q.val < 8 := q.isLt
        simp [GaussPivotFraming32.locate] at hv
        omega)]
    have h := SourceClausePreservingBroadcast.other_preserved
      (5 : Stack) 31 [GaussPivotHeader32.inputSlot]
      unary S 30 (by decide) (by decide) (by
        simp only [List.mem_singleton]
        intro he
        have hv := congrArg Fin.val he
        change (30:Nat) = W.input.val+8 at hv
        have hh : W.input.val < 8 := W.input.isLt
        omega)
    exact h.trans h30
  have ht := SourceClausePreservingBroadcast.target_written
    GaussPivotHeader32.outputSlot 31 [30]
    (by decide)
    (by
      simp only [List.mem_singleton]
      intro he
      have hv := congrArg Fin.val he
      change W.output.val+8 = (30:Nat) at hv
      have hh : W.output.val < 8 := W.output.isLt
      omega)
    (by
      intro he
      have hv := congrArg Fin.val he
      change W.output.val+8 = (31:Nat) at hv
      have hh : W.output.val < 8 := W.output.isLt
      omega)
    (SourceListMachineWriter.result false unary)
    (workerResult unary S c) 30 (by simp)
  change SourceClausePreservingBroadcast.result
    GaussPivotHeader32.outputSlot 31 [30]
      (SourceListMachineWriter.result false unary)
      (workerResult unary S c) 30 = _
  rw [ht,hworker]
  simp

#print axioms physical_exact
#print axioms final_preserves
#print axioms final31_empty
#print axioms final30

end
end CurrentAdditive.GaussPivotHeaderExact32
