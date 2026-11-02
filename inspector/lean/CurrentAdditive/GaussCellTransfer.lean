import CurrentAdditive.GaussNestedGetterRun
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
Physical final transfer for a selected matrix cell. Bank 18 holds the cell,
bank 6 holds the obsolete selected row, and bank 14 is empty after the nested
getter. This machine clears bank 6 and then copies bank 18 to bank 6 while
restoring bank 18. All other banks, including matrix bank 8, are untouched.
-/

namespace CurrentAdditive.GaussCellTransfer

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 22

inductive Label where
  | clear6
  | broadcast : SourceClausePreservingBroadcast.Label → Label
  | done
  deriving DecidableEq, Fintype

abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .clear6 => BitMachineClearBank.clearStep (6 : Stack)
      .clear6 (.broadcast .scan)
  | .broadcast l => BitMachineInline.stmt Label.broadcast id id
      (some .done)
      (SourceClausePreservingBroadcast.program (18 : Stack) 14 [6] l)
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat}
    (h : run n c = c') (m : Nat) : run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem clear_run (S : Stack → List Bool) :
    run ((S 6).length + 1) ⟨some .clear6, ((), none), S⟩ =
      ⟨some (.broadcast .scan), ((), none), Function.update S 6 []⟩ := by
  exact BitMachineClearBank.clear_one_run program 6 .clear6
    (.broadcast .scan) rfl () S

theorem broadcast_run (S : Stack → List Bool)
    (cell : List Bool) (hcell : S 18 = cell) (htemp : S 14 = []) :
    ∃ t ≤ 2 * cell.length + 3,
      run t ⟨some (.broadcast .scan), ((), none), S⟩ =
        ⟨some .done, ((), none),
          SourceClausePreservingBroadcast.result (18 : Stack) 14 [6] cell S⟩ := by
  have hh := SourceClausePreservingBroadcast.run_halt
    (18 : Stack) 14 [6] (by decide) (by decide) (by decide)
    (by decide) cell S hcell htemp
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs
    Label.broadcast id id (by intro v; rfl) (some .done)
    (SourceClausePreservingBroadcast.program (18 : Stack) 14 [6])
    program (by intro l; rfl)
    (⟨some .scan, ((), none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2 * cell.length + 3) (by rw [hh])
  refine ⟨u, hu, ?_⟩
  change run u _ = _ at he
  rw [hh] at he
  simpa only [BitMachineInline.cfg] using he

theorem transfer (S : Stack → List Bool)
    (cell : List Bool) (hcell : S 18 = cell) (htemp : S 14 = []) :
    ∃ t ≤ (S 6).length + 1 + (2 * cell.length + 3),
      ∃ S' : Stack → List Bool,
        run t ⟨some .clear6, ((), none), S⟩ =
          ⟨some .done, ((), none), S'⟩ ∧
        S' 6 = cell ∧ S' 18 = cell ∧ S' 8 = S 8 := by
  let C := Function.update S (6 : Stack) []
  have hc := clear_run S
  have hcellC : C 18 = cell := by simpa [C] using hcell
  have htempC : C 14 = [] := by simpa [C] using htemp
  obtain ⟨u, hu, hr⟩ := broadcast_run C cell hcellC htempC
  have he := (run_add hc u).trans hr
  let S' := SourceClausePreservingBroadcast.result (18 : Stack) 14 [6] cell C
  refine ⟨(S 6).length + 1 + u, by omega, S', he, ?_, ?_, ?_⟩
  · have ht := SourceClausePreservingBroadcast.target_written
      (18 : Stack) 14 [6] (by decide) (by decide) (by decide)
      cell C 6 (by simp)
    simpa [S', C] using ht
  · exact SourceClausePreservingBroadcast.source_restored
      (18 : Stack) 14 [6] (by decide) cell C
  · have ho := SourceClausePreservingBroadcast.other_preserved
      (18 : Stack) 14 [6] cell C 8 (by decide) (by decide)
        (by decide)
    simpa [S', C] using ho

#print axioms transfer

end CurrentAdditive.GaussCellTransfer
