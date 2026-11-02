import CurrentAdditive.GaussStepPivotHeaderExactRun32

/-! Exact endpoint of the checked pair-framing worker. -/

namespace CurrentAdditive.GaussPivotPayloadExact32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

private noncomputable abbrev W :=
  SourceListMachineWriter.framingMachine true
abbrev Stack := Fin 32

def workerResult (pair : List Bool) (S : Stack → List Bool)
    (c : W.Config) : Stack → List Bool :=
  (BitMachineStackEmbedding.cfg GaussPivotFraming32.locate
    (GaussPivotPayload32.afterIn pair S)
    GaussPivotPayload32.Label.writer
    (fun v => (((),none),v)) (some .resetOut) c :
      GaussPivotPayload32.Config).stk

theorem worker_out (pair : List Bool) (S : Stack → List Bool)
    (c : W.Config)
    (hout : c.stk W.output = SourceListMachineWriter.result true pair) :
    workerResult pair S c GaussPivotPayload32.outputSlot =
      SourceListMachineWriter.result true pair := by
  exact (BitMachineStackEmbedding.bank_at
    GaussPivotFraming32.locate (GaussPivotPayload32.afterIn pair S)
    c.stk W.output).trans hout

theorem worker31 (pair : List Bool) (S : Stack → List Bool)
    (c : W.Config) : workerResult pair S c 31 = [] := by
  change (BitMachineStackEmbedding.bank GaussPivotFraming32.locate
    (GaussPivotPayload32.afterIn pair S) c.stk) 31 = []
  rw [BitMachineStackEmbedding.bank_outside
    GaussPivotFraming32.locate _ _ 31 (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      fin_cases j <;> simp [GaussPivotFraming32.locate] at hv)]
  exact SourceClausePreservingBroadcast.temp_empty
    (28 : Stack) 31 [GaussPivotPayload32.inputSlot] pair S

theorem physical_exact (pair : List Bool)
    (S : Stack → List Bool)
    (h28 : S 28 = pair) (h31 : S 31 = [])
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (2*pair.length+3)+
        (UnaryBinaryEncoding.coefficient+7)*(pair.length+1)^2+1+
        (2*(SourceListMachineWriter.result true pair).length+3),
      ∃ c : W.Config,
        GaussPivotPayload32.run t
          ⟨some (.copyIn .scan),(((),none),W.initial),S⟩ =
        ⟨some .done,(((),none),W.initial),
          GaussPivotPayload32.afterOut
            (SourceListMachineWriter.result true pair)
            (workerResult pair S c)⟩ := by
  let payload := SourceListMachineWriter.result true pair
  obtain ⟨a,ha,hcopy⟩ :=
    GaussPivotPayload32.physical_copy_in pair S h28 h31
  obtain ⟨b,hb,c,hhalt,hout,hwriter⟩ :=
    GaussPivotPayload32.physical_writer_cfg pair S hempty
  let S2 := workerResult pair S c
  have hS2out : S2 GaussPivotPayload32.outputSlot = payload :=
    worker_out pair S c hout
  have hS231 : S2 31 = [] := worker31 pair S c
  have hwrite : GaussPivotPayload32.run b
      ⟨some (.writer W.start),(((),none),W.initial),
        GaussPivotPayload32.afterIn pair S⟩ =
      ⟨some .resetOut,(((),none),c.var),S2⟩ := by
    rw [hwriter]
    cases c with
    | mk l v stk =>
      cases l with
      | none => rfl
      | some l => cases hhalt
  have hreset : GaussPivotPayload32.run 1
      ⟨some .resetOut,(((),none),c.var),S2⟩ =
      ⟨some (.copyOut .scan),(((),none),W.initial),S2⟩ :=
    GaussPivotPayload32.reset_step S2 c.var
  obtain ⟨d,hd,houtcopy⟩ :=
    GaussPivotPayload32.physical_copy_out payload S2 hS2out hS231
  refine ⟨a+b+1+d,by dsimp [payload] at hd ⊢; omega,c,?_⟩
  rw [show a+b+1+d = ((a+b)+1)+d by omega]
  exact (GaussPivotPayload32.run_add
    ((GaussPivotPayload32.run_add hcopy b).trans hwrite) 1
    |>.trans hreset
    |> fun h => GaussPivotPayload32.run_add h d).trans houtcopy

theorem final31_empty (pair : List Bool)
    (S : Stack → List Bool) (c : W.Config) :
    GaussPivotPayload32.afterOut
      (SourceListMachineWriter.result true pair)
      (workerResult pair S c) 31 = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

theorem final26 (pair : List Bool)
    (S : Stack → List Bool) (c : W.Config)
    (h26 : S 26 = []) :
    GaussPivotPayload32.afterOut
      (SourceListMachineWriter.result true pair)
      (workerResult pair S c) 26 =
        SourceListMachineWriter.result true pair := by
  have hworker : workerResult pair S c 26 = [] := by
    change (BitMachineStackEmbedding.bank GaussPivotFraming32.locate
      (GaussPivotPayload32.afterIn pair S) c.stk) 26 = []
    rw [BitMachineStackEmbedding.bank_outside
      GaussPivotFraming32.locate _ _ 26 (by
        rintro ⟨q,hq⟩
        have hv := congrArg Fin.val hq
        have hq' : q.val < 8 := q.isLt
        simp [GaussPivotFraming32.locate] at hv
        omega)]
    have h := SourceClausePreservingBroadcast.other_preserved
      (28 : Stack) 31 [GaussPivotPayload32.inputSlot]
      pair S 26 (by decide) (by decide) (by
        simp only [List.mem_singleton]
        intro he
        have hv := congrArg Fin.val he
        change (26:Nat) = W.input.val+8 at hv
        have hh : W.input.val < 8 := W.input.isLt
        omega)
    exact h.trans h26
  have ht := SourceClausePreservingBroadcast.target_written
    GaussPivotPayload32.outputSlot 31 [26]
    (by decide)
    (by
      simp only [List.mem_singleton]
      intro he
      have hv := congrArg Fin.val he
      change W.output.val+8 = (26:Nat) at hv
      have hh : W.output.val < 8 := W.output.isLt
      omega)
    (by
      intro he
      have hv := congrArg Fin.val he
      change W.output.val+8 = (31:Nat) at hv
      have hh : W.output.val < 8 := W.output.isLt
      omega)
    (SourceListMachineWriter.result true pair)
    (workerResult pair S c) 26 (by simp)
  change SourceClausePreservingBroadcast.result
    GaussPivotPayload32.outputSlot 31 [26]
      (SourceListMachineWriter.result true pair)
      (workerResult pair S c) 26 = _
  rw [ht,hworker]
  simp

theorem final_preserves (pair : List Bool)
    (S : Stack → List Bool) (c : W.Config) (j : Stack)
    (hj : j.val < 8 ∨ 16 ≤ j.val)
    (h28 : j ≠ 28) (h26 : j ≠ 26) (h31 : j ≠ 31) :
    GaussPivotPayload32.afterOut
      (SourceListMachineWriter.result true pair)
      (workerResult pair S c) j = S j := by
  have hin : j ≠ GaussPivotPayload32.inputSlot := by
    intro h
    have hv := congrArg Fin.val h
    have hh : W.input.val < 8 := W.input.isLt
    change j.val = W.input.val+8 at hv
    rcases hj with hlow | hhigh <;> omega
  have hout : j ≠ GaussPivotPayload32.outputSlot := by
    intro h
    have hv := congrArg Fin.val h
    have hh : W.output.val < 8 := W.output.isLt
    change j.val = W.output.val+8 at hv
    rcases hj with hlow | hhigh <;> omega
  unfold GaussPivotPayload32.afterOut
  rw [SourceClausePreservingBroadcast.other_preserved
    GaussPivotPayload32.outputSlot 31 [26]
    (SourceListMachineWriter.result true pair)
    (workerResult pair S c) j hout h31 (by simpa using h26)]
  change (BitMachineStackEmbedding.bank
    GaussPivotFraming32.locate
    (GaussPivotPayload32.afterIn pair S) c.stk) j = S j
  rw [BitMachineStackEmbedding.bank_outside
    GaussPivotFraming32.locate _ _ j (by
      rintro ⟨q,hq⟩
      have hv := congrArg Fin.val hq
      have hq' : q.val < 8 := q.isLt
      simp [GaussPivotFraming32.locate] at hv
      rcases hj with hlow | hhigh <;> omega)]
  exact SourceClausePreservingBroadcast.other_preserved
    (28 : Stack) 31 [GaussPivotPayload32.inputSlot]
    pair S j h28 h31 (by simpa using hin)

#print axioms physical_exact
#print axioms final31_empty
#print axioms final26
#print axioms final_preserves

end
end CurrentAdditive.GaussPivotPayloadExact32
