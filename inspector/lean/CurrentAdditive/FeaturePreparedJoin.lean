import EthInapproximability.CurrentPaper.BitMachineBroadcast
import Mathlib.Tactic

/-! Physical concatenation of a prepared count header, framed pair, and old tail. -/

namespace CurrentAdditive.FeaturePreparedJoin

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 5
abbrev Control := Unit × Option Bool

inductive Label where
  | suffixScan | suffixRestore
  | pairScan | pairRestore
  | headerScan | headerRestore
  | done
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .suffixScan => BitMachineBroadcast.scanStep 2 3 .suffixScan .suffixRestore
  | .suffixRestore => BitMachineBroadcast.restoreStep 3 [4]
      .suffixRestore .pairScan
  | .pairScan => BitMachineBroadcast.scanStep 1 3 .pairScan .pairRestore
  | .pairRestore => BitMachineBroadcast.restoreStep 3 [4]
      .pairRestore .headerScan
  | .headerScan => BitMachineBroadcast.scanStep 0 3 .headerScan .headerRestore
  | .headerRestore => BitMachineBroadcast.restoreStep 3 [4]
      .headerRestore .done
  | .done => halt

def initialBank (header pair suffix : List Bool) : Stack → List Bool :=
  ![header,pair,suffix,[],[]]

def afterSuffix (header pair suffix : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied (2 : Stack) 3 [4] suffix
    (initialBank header pair suffix)

def afterPair (header pair suffix : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied (1 : Stack) 3 [4] pair
    (afterSuffix header pair suffix)

def afterHeader (header pair suffix : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied (0 : Stack) 3 [4] header
    (afterPair header pair suffix)

def run (t : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem run_add (t u : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

theorem suffix_phase (header pair suffix : List Bool) :
    run (2*suffix.length+2)
      ⟨some .suffixScan,((),none),initialBank header pair suffix⟩ =
      ⟨some .pairScan,((),none),afterSuffix header pair suffix⟩ := by
  exact BitMachineBroadcast.broadcast_run program (2 : Stack) 3
    (by decide) [4] (by decide) (by decide) (by decide)
    .suffixScan .suffixRestore .pairScan rfl rfl
    () none suffix (initialBank header pair suffix)
    (by rfl) (by rfl)

theorem pair_phase (header pair suffix : List Bool) :
    run (2*pair.length+2)
      ⟨some .pairScan,((),none),afterSuffix header pair suffix⟩ =
      ⟨some .headerScan,((),none),afterPair header pair suffix⟩ := by
  exact BitMachineBroadcast.broadcast_run program (1 : Stack) 3
    (by decide) [4] (by decide) (by decide) (by decide)
    .pairScan .pairRestore .headerScan rfl rfl
    () none pair (afterSuffix header pair suffix)
    (by simp [afterSuffix, initialBank, BitMachineBroadcast.copied])
    (by simp [afterSuffix, initialBank, BitMachineBroadcast.copied])

theorem header_phase (header pair suffix : List Bool) :
    run (2*header.length+2)
      ⟨some .headerScan,((),none),afterPair header pair suffix⟩ =
      ⟨some .done,((),none),afterHeader header pair suffix⟩ := by
  exact BitMachineBroadcast.broadcast_run program (0 : Stack) 3
    (by decide) [4] (by decide) (by decide) (by decide)
    .headerScan .headerRestore .done rfl rfl
    () none header (afterPair header pair suffix)
    (by simp [afterPair, afterSuffix, initialBank, BitMachineBroadcast.copied])
    (by simp [afterPair, afterSuffix, initialBank, BitMachineBroadcast.copied])

theorem output_bank (header pair suffix : List Bool) :
    afterHeader header pair suffix 4 = header ++ pair ++ suffix := by
  simp [afterHeader, afterPair, afterSuffix, initialBank,
    BitMachineBroadcast.copied, List.append_assoc]

theorem prepared_run (header pair suffix : List Bool) :
    let t := 2*suffix.length+2 + (2*pair.length+2) +
      (2*header.length+2) + 1
    let c := run t
      (⟨some .suffixScan,((),none),initialBank header pair suffix⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control)
    c.l = none ∧ c.stk 4 = header ++ pair ++ suffix := by
  let A := 2*suffix.length+2
  let B := 2*pair.length+2
  let C := 2*header.length+2
  let startCfg : TM2.Cfg (fun _ : Stack => Bool) Label Control :=
    ⟨some .suffixScan,((),none),initialBank header pair suffix⟩
  have hsplit : A+B+C+1 = A+(B+(C+1)) := by omega
  change (run (A+B+C+1) startCfg).l = none ∧
    (run (A+B+C+1) startCfg).stk 4 = header ++ pair ++ suffix
  rw [hsplit, run_add A (B+(C+1)) startCfg]
  have hs : run A startCfg =
      ⟨some .pairScan,((),none),afterSuffix header pair suffix⟩ :=
    suffix_phase header pair suffix
  rw [hs, run_add B (C+1)
    (⟨some .pairScan,((),none),afterSuffix header pair suffix⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control)]
  have hp : run B
      (⟨some .pairScan,((),none),afterSuffix header pair suffix⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some .headerScan,((),none),afterPair header pair suffix⟩ :=
    pair_phase header pair suffix
  rw [hp, run_add C 1
    (⟨some .headerScan,((),none),afterPair header pair suffix⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control)]
  have hh : run C
      (⟨some .headerScan,((),none),afterPair header pair suffix⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some .done,((),none),afterHeader header pair suffix⟩ :=
    header_phase header pair suffix
  rw [hh]
  simpa [run, advance, TM2.step, TM2.stepAux, program,
    output_bank]

#print axioms prepared_run

end CurrentAdditive.FeaturePreparedJoin
