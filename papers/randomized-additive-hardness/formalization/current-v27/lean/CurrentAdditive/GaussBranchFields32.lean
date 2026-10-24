import CurrentAdditive.GaussParsedState32
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-!
Physical branch preparation on the agreed Fin32 bank layout. Banks 16--19
hold parsed old state fields, bank 20 holds one pivot/no-pivot tag bit, bank 22
holds the rewritten matrix for a pivot. Prepared state fields are banks 4--7.
The outer controller selects terminal versus active; this program reads the
active branch bit itself. Pivot-list update follows the common copy phase.
-/

namespace CurrentAdditive.GaussBranchFields32

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 32
abbrev Control := Unit × Option Bool

inductive Branch where
  | halted | noPivot | pivot
  deriving DecidableEq, Fintype

inductive Label where
  | active
  | copy (b : Branch) (p : Fin 4)
      (l : SourceClausePreservingBroadcast.Label)
  | adjust (b : Branch)
  | pivotAppend
  | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def source (b : Branch) (p : Fin 4) : Stack :=
  if b = .pivot ∧ p = 0 then 22 else ⟨p.val + 16, by omega⟩
def dest (p : Fin 4) : Stack := ⟨p.val + 4, by omega⟩
def temp : Stack := 31

def next (b : Branch) (p : Fin 4) : Option Label :=
  if h : p.val < 3 then some (.copy b ⟨p.val + 1, by omega⟩ .scan)
  else some (.adjust b)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .active => pop 20 (fun v bit => (v.1, bit))
      (branch (fun v => v.2.getD false)
        (load (fun _ => ((), none))
          (goto (fun _ => .copy .pivot 0 .scan)))
        (load (fun _ => ((), none))
          (goto (fun _ => .copy .noPivot 0 .scan))))
  | .copy b p l =>
      BitMachineInline.stmt (Label.copy b p) id id (next b p)
        (SourceClausePreservingBroadcast.program (source b p) temp [dest p] l)
  | .adjust .halted => goto (fun _ => .done)
  | .adjust .noPivot => push 6 (fun _ => true) (goto (fun _ => .done))
  | .adjust .pivot =>
      push 5 (fun _ => true)
        (push 6 (fun _ => true) (goto (fun _ => .pivotAppend)))
  | .pivotAppend => goto (fun _ => .done)
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (u : Nat) :
    run (n + u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

theorem active_tag (S : Stack → List Bool) (tag : Bool) :
    run 1 ⟨some .active, ((), none), Function.update S 20 [tag]⟩ =
      ⟨some (.copy (if tag then .pivot else .noPivot) 0 .scan),
        ((), none), Function.update S 20 []⟩ := by
  cases tag <;> simp [run, program, advance, TM2.step,
    TM2.stepAux, Function.update]

theorem copy_phase (b : Branch) (p : Fin 4)
    (bits : List Bool) (S : Stack → List Bool)
    (hbits : S (source b p) = bits) (htemp : S temp = []) :
    ∃ t ≤ 2 * bits.length + 3,
      run t ⟨some (.copy b p .scan), ((), none), S⟩ =
        ⟨next b p, ((), none),
          SourceClausePreservingBroadcast.result
            (source b p) temp [dest p] bits S⟩ := by
  have hst : source b p ≠ temp := by
    intro h
    have hv := congrArg (fun j : Stack => j.val) h
    fin_cases p <;> cases b <;> simp [source, temp] at hv <;> omega
  have hs : source b p ∉ [dest p] := by
    simp only [List.mem_singleton]
    intro h
    have hv := congrArg (fun j : Stack => j.val) h
    fin_cases p <;> cases b <;> simp [source, dest] at hv <;> omega
  have ht : temp ∉ [dest p] := by
    simp only [List.mem_singleton]
    intro h
    have hv := congrArg (fun j : Stack => j.val) h
    simp [temp, dest] at hv
    omega
  have hcore := SourceClausePreservingBroadcast.run_halt
    (source b p) temp [dest p] hst (by simp) hs ht bits S hbits htemp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Label.copy b p) id id (by intro v; rfl) (next b p)
    (SourceClausePreservingBroadcast.program (source b p) temp [dest p])
    program (by intro l; rfl)
    (⟨some .scan, ((), none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2 * bits.length + 3) (by rw [hcore])
  refine ⟨u, hu, ?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa only [BitMachineInline.cfg] using hr

def after0 (b : Branch) (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (source b 0) temp [dest 0]
    (S (source b 0)) S
def after1 (b : Branch) (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (source b 1) temp [dest 1]
    (S (source b 1)) (after0 b S)
def after2 (b : Branch) (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (source b 2) temp [dest 2]
    (S (source b 2)) (after1 b S)
def after3 (b : Branch) (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (source b 3) temp [dest 3]
    (S (source b 3)) (after2 b S)

private theorem after0_source1 (b : Branch) (S : Stack → List Bool) :
    after0 b S (source b 1) = S (source b 1) := by
  cases b <;> simp [after0, source, dest, temp,
    SourceClausePreservingBroadcast.result, BitMachineBroadcast.prepend]

private theorem after1_source2 (b : Branch) (S : Stack → List Bool) :
    after1 b S (source b 2) = S (source b 2) := by
  cases b <;> simp [after1, after0, source, dest, temp,
    SourceClausePreservingBroadcast.result, BitMachineBroadcast.prepend]

private theorem after2_source3 (b : Branch) (S : Stack → List Bool) :
    after2 b S (source b 3) = S (source b 3) := by
  cases b <;> simp [after2, after1, after0, source, dest, temp,
    SourceClausePreservingBroadcast.result, BitMachineBroadcast.prepend]

private theorem after0_temp (b : Branch) (S : Stack → List Bool) :
    after0 b S temp = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
private theorem after1_temp (b : Branch) (S : Stack → List Bool) :
    after1 b S temp = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
private theorem after2_temp (b : Branch) (S : Stack → List Bool) :
    after2 b S temp = [] :=
  SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

def copyClock (b : Branch) (S : Stack → List Bool) : Nat :=
  (2 * (S (source b 0)).length + 3) +
  (2 * (S (source b 1)).length + 3) +
  (2 * (S (source b 2)).length + 3) +
  (2 * (S (source b 3)).length + 3)

theorem physical_copy_fields (b : Branch) (S : Stack → List Bool)
    (htemp : S temp = []) :
    ∃ t ≤ copyClock b S,
      run t ⟨some (.copy b 0 .scan), ((), none), S⟩ =
        ⟨some (.adjust b), ((), none), after3 b S⟩ := by
  obtain ⟨t0, h0, hr0⟩ := copy_phase b 0 (S (source b 0)) S rfl htemp
  have hs0 : run t0 ⟨some (.copy b 0 .scan), ((), none), S⟩ =
      ⟨some (.copy b 1 .scan), ((), none), after0 b S⟩ := by
    simpa [next, after0] using hr0
  obtain ⟨t1, h1, hr1⟩ := copy_phase b 1 (S (source b 1))
    (after0 b S) (after0_source1 b S) (after0_temp b S)
  have hs1 : run t1 ⟨some (.copy b 1 .scan), ((), none), after0 b S⟩ =
      ⟨some (.copy b 2 .scan), ((), none), after1 b S⟩ := by
    simpa [next, after1] using hr1
  obtain ⟨t2, h2, hr2⟩ := copy_phase b 2 (S (source b 2))
    (after1 b S) (after1_source2 b S) (after1_temp b S)
  have hs2 : run t2 ⟨some (.copy b 2 .scan), ((), none), after1 b S⟩ =
      ⟨some (.copy b 3 .scan), ((), none), after2 b S⟩ := by
    simpa [next, after2] using hr2
  obtain ⟨t3, h3, hr3⟩ := copy_phase b 3 (S (source b 3))
    (after2 b S) (after2_source3 b S) (after2_temp b S)
  have hs3 : run t3 ⟨some (.copy b 3 .scan), ((), none), after2 b S⟩ =
      ⟨some (.adjust b), ((), none), after3 b S⟩ := by
    simpa [next, after3] using hr3
  refine ⟨t0 + t1 + t2 + t3, ?_, ?_⟩
  · unfold copyClock
    omega
  · rw [show t0 + t1 + t2 + t3 = ((t0 + t1) + t2) + t3 by omega]
    exact (((run_add hs0 t1).trans hs1 |> fun h => run_add h t2).trans hs2
      |> fun h => run_add h t3).trans hs3

theorem copied_field (b : Branch) (S : Stack → List Bool) (p : Fin 4)
    (hDest : ∀ q : Fin 4, S (dest q) = []) :
    after3 b S (dest p) = S (source b p) := by
  have h0 : S 4 = [] := by simpa [dest] using hDest 0
  have h1 : S 5 = [] := by simpa [dest] using hDest 1
  have h2 : S 6 = [] := by simpa [dest] using hDest 2
  have h3 : S 7 = [] := by simpa [dest] using hDest 3
  fin_cases p <;> cases b <;>
    simp [after3, after2, after1, after0, source, dest, temp,
      SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend, h0, h1, h2, h3]

theorem adjust_halted (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some (.adjust .halted), v, S⟩ =
      ⟨some .done, v, S⟩ := rfl

theorem adjust_noPivot (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some (.adjust .noPivot), v, S⟩ =
      ⟨some .done, v, Function.update S 6 (true :: S 6)⟩ := rfl

theorem adjust_pivot (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some (.adjust .pivot), v, S⟩ =
      ⟨some .pivotAppend, v,
        Function.update (Function.update S 5 (true :: S 5)) 6
          (true :: S 6)⟩ := by
  rfl

def preparedBank (S : Stack → List Bool) : Fin 4 → List Bool :=
  fun p => S (dest p)

structure ParsedState {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (S : Stack → List Bool) : Prop where
  matrix : S 16 = CurrentAdditive.GaussPhysical.encodeTypedMatrix s.B
  row : S 17 = List.replicate s.r true
  column : S 18 = List.replicate s.c true
  pivots : S 19 = CurrentAdditive.GaussControlTrace.pivotsPacket s.pivots
  destinations : ∀ p : Fin 4, S (dest p) = []
  scratch : S temp = []

def noPivotState {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k) :
    CurrentAdditive.GaussControlTrace.State m k :=
  ⟨s.B, s.r, s.c + 1, s.pivots⟩

theorem halted_prepared_bank {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (S : Stack → List Bool) (h : ParsedState s S) :
    preparedBank (after3 .halted S) =
      CurrentAdditive.GaussControlTrace.stateBank s := by
  funext p
  rw [preparedBank, copied_field .halted S p h.destinations]
  fin_cases p <;>
    simp [source, CurrentAdditive.GaussControlTrace.stateBank,
      h.matrix, h.row, h.column, h.pivots]

theorem noPivot_prepared_bank {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (S : Stack → List Bool) (h : ParsedState s S) :
    preparedBank (Function.update (after3 .noPivot S) 6
      (true :: (after3 .noPivot S) 6)) =
      CurrentAdditive.GaussControlTrace.stateBank (noPivotState s) := by
  have h0 := copied_field .noPivot S 0 h.destinations
  have h1 := copied_field .noPivot S 1 h.destinations
  have h2 := copied_field .noPivot S 2 h.destinations
  have h3 := copied_field .noPivot S 3 h.destinations
  funext p
  fin_cases p
  · simpa [preparedBank, dest, noPivotState,
      CurrentAdditive.GaussControlTrace.stateBank, source] using
      h0.trans h.matrix
  · simpa [preparedBank, dest, noPivotState,
      CurrentAdditive.GaussControlTrace.stateBank, source] using
      h1.trans h.row
  · have hc := congrArg (List.cons true) (h2.trans h.column)
    simpa [preparedBank, dest, noPivotState,
      CurrentAdditive.GaussControlTrace.stateBank, source,
      List.replicate_succ] using hc
  · simpa [preparedBank, dest, noPivotState,
      CurrentAdditive.GaussControlTrace.stateBank, source] using
      h3.trans h.pivots

theorem physical_halted {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (S : Stack → List Bool) (h : ParsedState s S) :
    ∃ t ≤ copyClock .halted S + 1,
      (run t ⟨some (.copy .halted 0 .scan), ((), none), S⟩).l =
        some .done ∧
      preparedBank
        (run t ⟨some (.copy .halted 0 .scan), ((), none), S⟩).stk =
        CurrentAdditive.GaussControlTrace.stateBank s := by
  obtain ⟨t, ht, hr⟩ := physical_copy_fields .halted S h.scratch
  refine ⟨t + 1, by omega, ?_, ?_⟩
  · rw [run_add hr 1, adjust_halted]
  · rw [run_add hr 1, adjust_halted]
    exact halted_prepared_bank s S h

theorem physical_noPivot {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (S : Stack → List Bool) (h : ParsedState s S) :
    ∃ t ≤ copyClock .noPivot S + 1,
      (run t ⟨some (.copy .noPivot 0 .scan), ((), none), S⟩).l =
        some .done ∧
      preparedBank
        (run t ⟨some (.copy .noPivot 0 .scan), ((), none), S⟩).stk =
        CurrentAdditive.GaussControlTrace.stateBank (noPivotState s) := by
  obtain ⟨t, ht, hr⟩ := physical_copy_fields .noPivot S h.scratch
  refine ⟨t + 1, by omega, ?_, ?_⟩
  · rw [run_add hr 1, adjust_noPivot]
  · rw [run_add hr 1, adjust_noPivot]
    exact noPivot_prepared_bank s S h

#print axioms active_tag
#print axioms copy_phase
#print axioms adjust_halted
#print axioms adjust_noPivot
#print axioms adjust_pivot
#print axioms physical_halted
#print axioms physical_noPivot

end CurrentAdditive.GaussBranchFields32
