import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-!
A physical fixed-stack fanout for the pivot packet. This is one component
of indexed context preparation: it copies a source word into three callback
work stacks, restores the source, and has a linear exact TM2 clock. It does
not iterate over a variable-length matrix.
-/

namespace CurrentAdditive.GaussListContext.PivotFanout

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 5

def targets : List Stack := [2, 3, 4]

def initial (bits : List Bool) : Stack → List Bool :=
  ![bits, [], [], [], []]

def program := SourceClausePreservingBroadcast.program
  (0 : Stack) (1 : Stack) targets

def result (bits : List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result
    (0 : Stack) (1 : Stack) targets bits (initial bits)

theorem physical_run (bits : List Bool) :
    ((advance program)^[2 * bits.length + 3])
      (⟨some .scan, ((), none), initial bits⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          SourceClausePreservingBroadcast.Label (Unit × Option Bool)) =
      ⟨none, ((), none), result bits⟩ := by
  exact SourceClausePreservingBroadcast.run_halt
    (0 : Stack) (1 : Stack) targets
    (by decide) (by decide) (by decide) (by decide)
    bits (initial bits) rfl rfl

theorem source_preserved (bits : List Bool) : result bits 0 = bits := by
  exact SourceClausePreservingBroadcast.source_restored
    (0 : Stack) (1 : Stack) targets (by decide) bits (initial bits)

theorem target_written (bits : List Bool) (j : Stack)
    (hj : j ∈ targets) : result bits j = bits := by
  have h := SourceClausePreservingBroadcast.target_written
    (0 : Stack) (1 : Stack) targets
    (by decide) (by decide) (by decide)
    bits (initial bits) j hj
  have hinit : initial bits j = [] := by
    fin_cases j <;> simp_all [targets, initial]
  simpa [hinit] using h

theorem temp_empty (bits : List Bool) : result bits 1 = [] := by
  exact SourceClausePreservingBroadcast.temp_empty
    (0 : Stack) (1 : Stack) targets bits (initial bits)

#print axioms physical_run
#print axioms source_preserved
#print axioms target_written

end CurrentAdditive.GaussListContext.PivotFanout
