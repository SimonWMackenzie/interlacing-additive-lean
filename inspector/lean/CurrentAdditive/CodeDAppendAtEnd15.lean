import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-! A fixed six-phase stack program that appends one variable-length word to
the end of an existing output.  Source and payload lengths are charged. -/

namespace CurrentAdditive.CodeDAppendAtEnd15

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBroadcast
open Turing BitMachineEncoding

abbrev Stack := Fin 15

inductive Label
  | saveScan | saveRestore | payloadScan | payloadRestore
  | outputScan | outputRestore | done
  deriving DecidableEq, Fintype

abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .saveScan => scanStep 9 14 .saveScan .saveRestore
  | .saveRestore => restoreStep 14 [11] .saveRestore .payloadScan
  | .payloadScan => scanStep 5 14 .payloadScan .payloadRestore
  | .payloadRestore => restoreStep 14 [9] .payloadRestore .outputScan
  | .outputScan => scanStep 11 14 .outputScan .outputRestore
  | .outputRestore => restoreStep 14 [9] .outputRestore .done
  | .done => .halt

def run (n : Nat) (c : Config) := ((advance program)^[n]) c

def initialBank (foreign : Stack → List Bool) (output payload : List Bool) :
    Stack → List Bool :=
  Function.update (Function.update foreign 9 output) 5 payload

theorem append_run (foreign : Stack → List Bool) (output payload : List Bool)
    (h11 : foreign 11 = []) (h14 : foreign 14 = []) :
    run (4 * output.length + 2 * payload.length + 6)
      ⟨some .saveScan, ((), none), initialBank foreign output payload⟩ =
    ⟨some .done, ((), none),
      Function.update
        (Function.update
          (Function.update (initialBank foreign output payload) 9 []) 5 [])
        9 (output ++ payload)⟩ := by
  let S := initialBank foreign output payload
  have h9 : S 9 = output := by simp [S, initialBank]
  have h5 : S 5 = payload := by simp [S, initialBank]
  have h11' : S 11 = [] := by simpa [S, initialBank] using h11
  have h14' : S 14 = [] := by simpa [S, initialBank] using h14
  have hs := broadcast_run program (9 : Stack) 14 (by decide) [11]
    (by decide) (by decide) (by decide)
    .saveScan .saveRestore .payloadScan rfl rfl () none output S h9 h14'
  have hsBank : copied (9 : Stack) 14 [11] output S =
      Function.update (Function.update S 9 []) 11 output := by
    funext k
    fin_cases k <;> simp [copied, S, initialBank, h11, h14]
  rw [hsBank] at hs
  let S1 := Function.update (Function.update S 9 []) 11 output
  have h5' : S1 5 = payload := by simp [S1, h5]
  have h14'' : S1 14 = [] := by simp [S1, h14']
  have hp := broadcast_run program (5 : Stack) 14 (by decide) [9]
    (by decide) (by decide) (by decide)
    .payloadScan .payloadRestore .outputScan rfl rfl () none payload S1 h5' h14''
  have hpBank : copied (5 : Stack) 14 [9] payload S1 =
      Function.update (Function.update S1 5 []) 9 payload := by
    funext k
    fin_cases k <;> simp [copied, S1, h14']
  rw [hpBank] at hp
  let S2 := Function.update (Function.update S1 5 []) 9 payload
  have h11'' : S2 11 = output := by simp [S2, S1]
  have h14''' : S2 14 = [] := by simp [S2, S1, h14']
  have ho := broadcast_run program (11 : Stack) 14 (by decide) [9]
    (by decide) (by decide) (by decide)
    .outputScan .outputRestore .done rfl rfl () none output S2 h11'' h14'''
  have hoBank : copied (11 : Stack) 14 [9] output S2 =
      Function.update (Function.update S2 11 []) 9 (output ++ payload) := by
    funext k
    fin_cases k <;> simp [copied, S2, S1, h14']
  rw [hoBank] at ho
  have hj := (run_add program hs (2 * payload.length + 2)).trans hp
  have hk := (run_add program hj (2 * output.length + 2)).trans ho
  have hfinal : Function.update (Function.update S2 11 []) 9 (output ++ payload) =
      Function.update
        (Function.update
          (Function.update (initialBank foreign output payload) 9 []) 5 [])
        9 (output ++ payload) := by
    funext k
    fin_cases k <;> simp [S2, S1, S, initialBank, h11, h14]
  rw [hfinal] at hk
  have htime : 4 * output.length + 2 * payload.length + 6 =
      2 * output.length + 2 + (2 * payload.length + 2) +
        (2 * output.length + 2) := by omega
  rw [htime]
  exact hk

#print axioms append_run

end CurrentAdditive.CodeDAppendAtEnd15
