import CurrentAdditive.GaussPivotFraming32

/-!
The updated unary row cursor on bank 5 is copied into a fixed eight-stack
header writer on ambient banks 8--15. After the worker writes the canonical
count header, another source-preserving copy places it on bank 30 for joining
with the pivot-list body.
All three subprograms are fixed TM2 code and all copies are charged.
-/

namespace CurrentAdditive.GaussPivotHeader32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

private noncomputable abbrev W := SourceListMachineWriter.framingMachine false
abbrev Stack := Fin 32
abbrev Control := (Unit × Option Bool) × Fin W.controlCount

inductive Label where
  | copyIn (l : SourceClausePreservingBroadcast.Label)
  | writer (l : Fin W.labelCount)
  | resetOut
  | copyOut (l : SourceClausePreservingBroadcast.Label)
  | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable def inputSlot : Stack := GaussPivotFraming32.locate W.input
noncomputable def outputSlot : Stack := GaussPivotFraming32.locate W.output

private theorem mapped_ne (j : Fin W.stackCount) (n : Nat)
    (hn : n < 8 ∨ 16 ≤ n) (hn' : n < 32) :
    GaussPivotFraming32.locate j ≠ (⟨n, hn'⟩ : Stack) := by
  intro h
  have hv := congrArg Fin.val h
  have hj : j.val < 8 := by
    simpa only [show W.stackCount = 8 by rfl] using j.isLt
  change j.val + 8 = n at hv
  omega

private theorem input_ne5 : inputSlot ≠ 5 := by
  exact mapped_ne W.input 5 (by omega) (by omega)
private theorem input_ne31 : inputSlot ≠ 31 := by
  exact mapped_ne W.input 31 (by omega) (by omega)
private theorem output_ne31 : outputSlot ≠ 31 := by
  exact mapped_ne W.output 31 (by omega) (by omega)
private theorem output_ne30 : outputSlot ≠ 30 := by
  exact mapped_ne W.output 30 (by omega) (by omega)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copyIn l => BitMachineInline.stmt Label.copyIn
      (fun v => (v, W.initial)) Prod.fst (some (.writer W.start))
      (SourceClausePreservingBroadcast.program (5 : Stack) 31 [inputSlot] l)
  | .writer l => BitMachineStackEmbedding.stmt GaussPivotFraming32.locate
      Label.writer (fun v => (((), none), v)) Prod.snd
      (some .resetOut) (W.program l)
  | .resetOut => .load (fun _ => (((),none),W.initial))
      (.goto (fun _ => .copyOut .scan))
  | .copyOut l => BitMachineInline.stmt Label.copyOut
      (fun v => (v, W.initial)) Prod.fst (some .done)
      (SourceClausePreservingBroadcast.program outputSlot 31 [30] l)
  | .done => .halt

noncomputable def run (t : Nat) (c : Config) : Config :=
  ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (u : Nat) :
    run (n+u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

noncomputable def afterIn (pair : List Bool) (S : Stack → List Bool) :=
  SourceClausePreservingBroadcast.result (5 : Stack) 31 [inputSlot] pair S

theorem physical_copy_in (pair : List Bool) (S : Stack → List Bool)
    (hpair : S 5 = pair) (h31 : S 31 = []) :
    ∃ t ≤ 2*pair.length+3,
      run t ⟨some (.copyIn .scan), (((),none),W.initial),S⟩ =
        ⟨some (.writer W.start), (((),none),W.initial),afterIn pair S⟩ := by
  have hs : (5 : Stack) ≠ 31 := by decide
  have hi : (5 : Stack) ∉ [inputSlot] := by simpa using input_ne5.symm
  have ht : (31 : Stack) ∉ [inputSlot] := by simpa using input_ne31.symm
  have hcore := SourceClausePreservingBroadcast.run_halt
    (5 : Stack) 31 [inputSlot] hs (by simp) hi ht pair S hpair h31
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    Label.copyIn (fun v => (v,W.initial)) Prod.fst
    (by intro v; rfl) (some (.writer W.start))
    (SourceClausePreservingBroadcast.program (5 : Stack) 31 [inputSlot])
    program (by intro l; rfl)
    (⟨some .scan, ((),none),S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (2*pair.length+3) (by rw [hcore])
  refine ⟨u,hu,?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa [afterIn, BitMachineInline.cfg] using hr

theorem input_ready (pair : List Bool) (S : Stack → List Bool)
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∀ j : Fin W.stackCount,
      afterIn pair S (GaussPivotFraming32.locate j) =
        (W.init pair).stk j := by
  intro j
  by_cases hj : j = W.input
  · subst j
    have ht := SourceClausePreservingBroadcast.target_written
      (5 : Stack) 31 [inputSlot] (by simpa using input_ne31.symm)
      (by simpa using input_ne5.symm)
      (by decide) pair S inputSlot (by simp)
    simpa [afterIn, inputSlot, BitMachine.Machine.init, hempty] using ht
  · have hloc : GaussPivotFraming32.locate j ≠ inputSlot := by
      intro he
      exact hj (GaussPivotFraming32.locate.injective he)
    have ht := SourceClausePreservingBroadcast.other_preserved
      (5 : Stack) 31 [inputSlot] pair S
      (GaussPivotFraming32.locate j)
      (by simpa using (mapped_ne j 5 (by omega) (by omega)))
      (by simpa using (mapped_ne j 31 (by omega) (by omega)))
      (by simpa using hloc)
    simpa [afterIn, BitMachine.Machine.init, hj, hempty j] using ht

theorem writer_start (pair : List Bool) (S : Stack → List Bool)
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    (BitMachineStackEmbedding.cfg GaussPivotFraming32.locate
      (afterIn pair S) Label.writer (fun v => (((),none),v))
      (some .resetOut) (W.init pair) : Config) =
    ⟨some (.writer W.start), (((),none),W.initial),afterIn pair S⟩ := by
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    BitMachine.Machine.init]
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro j
  exact (input_ready pair S hempty j).symm

theorem physical_writer (pair : List Bool) (S : Stack → List Bool)
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (UnaryBinaryEncoding.coefficient+7)*(pair.length+1)^2,
      (run t ⟨some (.writer W.start), (((),none),W.initial),
        afterIn pair S⟩).l = some .resetOut ∧
      (run t ⟨some (.writer W.start), (((),none),W.initial),
        afterIn pair S⟩).stk outputSlot =
        SourceListMachineWriter.result false pair := by
  obtain ⟨t,ht,hh,ho,_⟩ := BitMachineCompositionArithmetic.first_halt W
    (SourceListMachineWriter.outputs false pair)
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    GaussPivotFraming32.locate (afterIn pair S)
    Label.writer (fun v => (((),none),v)) Prod.snd
    (by intro v; rfl) (some .resetOut)
    W.program program (by intro l; rfl) (W.init pair) t hh
  have hstart := writer_start pair S hempty
  change run u (BitMachineStackEmbedding.cfg GaussPivotFraming32.locate
      (afterIn pair S) Label.writer (fun v => (((),none),v))
      (some .resetOut) (W.init pair)) =
    BitMachineStackEmbedding.cfg GaussPivotFraming32.locate
      (afterIn pair S) Label.writer (fun v => (((),none),v))
      (some .resetOut) (W.run t (W.init pair)) at hr
  refine ⟨u,hu.trans ht,?_,?_⟩
  · rw [← hstart, hr]
    simp [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh]
  · rw [← hstart, hr]
    exact (BitMachineStackEmbedding.bank_at
      GaussPivotFraming32.locate (afterIn pair S) _ W.output).trans ho

theorem physical_writer_cfg (pair : List Bool) (S : Stack → List Bool)
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (UnaryBinaryEncoding.coefficient+7)*(pair.length+1)^2,
      ∃ c : W.Config,
        c.l = none ∧
        c.stk W.output = SourceListMachineWriter.result false pair ∧
        run t ⟨some (.writer W.start), (((),none),W.initial),
          afterIn pair S⟩ =
          BitMachineStackEmbedding.cfg GaussPivotFraming32.locate
            (afterIn pair S) Label.writer (fun v => (((),none),v))
            (some .resetOut) c := by
  obtain ⟨t,ht,hh,ho,_⟩ := BitMachineCompositionArithmetic.first_halt W
    (SourceListMachineWriter.outputs false pair)
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    GaussPivotFraming32.locate (afterIn pair S)
    Label.writer (fun v => (((),none),v)) Prod.snd
    (by intro v; rfl) (some .resetOut)
    W.program program (by intro l; rfl) (W.init pair) t hh
  refine ⟨u,hu.trans ht,W.run t (W.init pair),hh,ho,?_⟩
  change run u (BitMachineStackEmbedding.cfg GaussPivotFraming32.locate
      (afterIn pair S) Label.writer (fun v => (((),none),v))
      (some .resetOut) (W.init pair)) = _ at hr
  rw [writer_start pair S hempty] at hr
  exact hr

noncomputable def afterOut (payload : List Bool) (S : Stack → List Bool) :=
  SourceClausePreservingBroadcast.result outputSlot 31 [30] payload S

theorem physical_copy_out (payload : List Bool) (S : Stack → List Bool)
    (hpayload : S outputSlot = payload) (h31 : S 31 = []) :
    ∃ t ≤ 2*payload.length+3,
      run t ⟨some (.copyOut .scan), (((),none),W.initial),S⟩ =
        ⟨some .done, (((),none),W.initial),afterOut payload S⟩ := by
  have hcore := SourceClausePreservingBroadcast.run_halt
    outputSlot 31 [30] output_ne31 (by simp)
    (by simpa using output_ne30) (by simp) payload S hpayload h31
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    Label.copyOut (fun v => (v,W.initial)) Prod.fst
    (by intro v; rfl) (some .done)
    (SourceClausePreservingBroadcast.program outputSlot 31 [30])
    program (by intro l; rfl)
    (⟨some .scan, ((),none),S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (2*payload.length+3) (by rw [hcore])
  refine ⟨u,hu,?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa [afterOut, BitMachineInline.cfg] using hr

theorem afterOut_30 (payload : List Bool) (S : Stack → List Bool)
    (h30 : S 30 = []) : afterOut payload S 30 = payload := by
  have h := SourceClausePreservingBroadcast.target_written
    outputSlot 31 [30] (by simp) (by simpa using output_ne30)
    output_ne31 payload S 30 (by simp)
  simpa [afterOut,h30] using h

theorem reset_step (S : Stack → List Bool) (v : Fin W.controlCount) :
    run 1 ⟨some .resetOut, (((),none),v), S⟩ =
      ⟨some (.copyOut .scan), (((),none),W.initial), S⟩ := rfl

private theorem afterIn_30 (pair : List Bool) (S : Stack → List Bool) :
    afterIn pair S 30 = S 30 := by
  exact SourceClausePreservingBroadcast.other_preserved
    (5 : Stack) 31 [inputSlot] pair S 30
    (by decide) (by decide) (by simpa using (mapped_ne W.input 30
      (by omega) (by omega)).symm)

private theorem afterIn_31 (pair : List Bool) (S : Stack → List Bool) :
    afterIn pair S 31 = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

theorem physical_payload (pair : List Bool) (S : Stack → List Bool)
    (hpair : S 5 = pair) (h31 : S 31 = [])
    (h30 : S 30 = [])
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (2*pair.length+3) +
        (UnaryBinaryEncoding.coefficient+7)*(pair.length+1)^2 + 1 +
        (2*(SourceListMachineWriter.result false pair).length+3),
      (run t ⟨some (.copyIn .scan), (((),none),W.initial),S⟩).l =
        some .done ∧
      (run t ⟨some (.copyIn .scan), (((),none),W.initial),S⟩).stk 30 =
        SourceListMachineWriter.result false pair := by
  let payload := SourceListMachineWriter.result false pair
  obtain ⟨a,ha,hcopy⟩ := physical_copy_in pair S hpair h31
  obtain ⟨b,hb,c,hhalt,hout,hwriter⟩ :=
    physical_writer_cfg pair S hempty
  let S2 := ((BitMachineStackEmbedding.cfg GaussPivotFraming32.locate
    (afterIn pair S) Label.writer (fun v => (((),none),v))
    (some .resetOut) c : Config).stk)
  have hS2out : S2 outputSlot = payload := by
    exact (BitMachineStackEmbedding.bank_at
      GaussPivotFraming32.locate (afterIn pair S) c.stk W.output).trans hout
  have hS226 : S2 30 = [] := by
    change (BitMachineStackEmbedding.bank GaussPivotFraming32.locate
      (afterIn pair S) c.stk) 30 = []
    rw [BitMachineStackEmbedding.bank_outside
      GaussPivotFraming32.locate _ _ 30 (by
        rintro ⟨j,hj⟩
        exact mapped_ne j 30 (by omega) (by omega) hj)]
    exact (afterIn_30 pair S).trans h30
  have hS231 : S2 31 = [] := by
    change (BitMachineStackEmbedding.bank GaussPivotFraming32.locate
      (afterIn pair S) c.stk) 31 = []
    rw [BitMachineStackEmbedding.bank_outside
      GaussPivotFraming32.locate _ _ 31 (by
        rintro ⟨j,hj⟩
        exact mapped_ne j 31 (by omega) (by omega) hj)]
    exact afterIn_31 pair S
  have hwrite : run b
      ⟨some (.writer W.start), (((),none),W.initial),afterIn pair S⟩ =
      ⟨some .resetOut, (((),none),c.var),S2⟩ := by
    rw [hwriter]
    cases c with
    | mk l v stk =>
        cases l with
        | none => rfl
        | some l => cases hhalt
  have hreset : run 1
      ⟨some .resetOut, (((),none),c.var),S2⟩ =
      ⟨some (.copyOut .scan), (((),none),W.initial),S2⟩ :=
    reset_step S2 c.var
  obtain ⟨d,hd,houtcopy⟩ :=
    physical_copy_out payload S2 hS2out hS231
  have hall : run (a+b+1+d)
      ⟨some (.copyIn .scan), (((),none),W.initial),S⟩ =
      ⟨some .done, (((),none),W.initial),afterOut payload S2⟩ := by
    rw [show a+b+1+d = ((a+b)+1)+d by omega]
    exact (run_add ((run_add hcopy b).trans hwrite) 1 |>.trans hreset
      |> fun h => run_add h d).trans houtcopy
  refine ⟨a+b+1+d,by dsimp [payload] at hd ⊢; omega,?_,?_⟩
  · rw [hall]
  · rw [hall]
    exact afterOut_30 payload S2 hS226

#print axioms physical_copy_in
#print axioms input_ready
#print axioms physical_writer
#print axioms physical_payload

end
end CurrentAdditive.GaussPivotHeader32
