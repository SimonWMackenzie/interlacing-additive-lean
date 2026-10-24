import CurrentAdditive.GaussGetterReset64

/-! Charged source-preserving copy between two Fin64 registers using bank 63
as an empty temporary. This is used to load getter indices and save each
selected operand before clearing getter work banks. -/

namespace CurrentAdditive.GaussGetterCopy64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64
abbrev Label := SourceClausePreservingBroadcast.Label
abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program (source target : Stack) :
    Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  SourceClausePreservingBroadcast.program source 63 [target]

def run (source target : Stack) (t : Nat) (c : Config) : Config :=
  ((advance (program source target))^[t]) c

theorem copy_word (source target : Stack)
    (hsource : source ≠ 63) (htarget : target ≠ source)
    (htemp : target ≠ 63)
    (word : List Bool) (S : Stack → List Bool)
    (hword : S source = word) (hemptyTemp : S 63 = [])
    (hemptyTarget : S target = []) :
    run source target (2 * word.length + 3)
      ⟨some .scan, ((), none), S⟩ =
      ⟨none, ((), none),
       SourceClausePreservingBroadcast.result source 63 [target] word S⟩ ∧
    (SourceClausePreservingBroadcast.result source 63 [target] word S)
      target = word ∧
    (SourceClausePreservingBroadcast.result source 63 [target] word S)
      source = word ∧
    (SourceClausePreservingBroadcast.result source 63 [target] word S)
      63 = [] := by
  have hr := SourceClausePreservingBroadcast.run_halt source 63 [target]
    hsource (by simp) (by simp [Ne.symm htarget])
    (by simp [Ne.symm htemp]) word S hword hemptyTemp
  have ht := SourceClausePreservingBroadcast.target_written
    source 63 [target] (by simp [Ne.symm htemp])
    (by simp [Ne.symm htarget]) hsource word S target (by simp)
  have hs := SourceClausePreservingBroadcast.source_restored
    source 63 [target] hsource word S
  have he := SourceClausePreservingBroadcast.temp_empty
    source 63 [target] word S
  refine ⟨hr, ?_, hs, he⟩
  simpa [hemptyTarget] using ht

theorem copy_preserves_other (source target j : Stack)
    (word : List Bool) (S : Stack → List Bool)
    (hjSource : j ≠ source) (hjTemp : j ≠ 63)
    (hjTarget : j ≠ target) :
    (SourceClausePreservingBroadcast.result source 63 [target] word S)
      j = S j := by
  exact SourceClausePreservingBroadcast.other_preserved
    source 63 [target] word S j hjSource hjTemp (by simpa using hjTarget)

#print axioms copy_word
#print axioms copy_preserves_other

end CurrentAdditive.GaussGetterCopy64
