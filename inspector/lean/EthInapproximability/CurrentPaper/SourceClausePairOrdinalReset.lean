import EthInapproximability.CurrentPaper.SourceClausePairOrdinalLoader

/-! Physical ordinal drain between consecutive ordered pair occurrences. -/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairOrdinalReset

open Turing Turing.TM2.Stmt BitMachineEncoding
open scoped Classical

abbrev Stack := PairUnitLift.Stack

inductive Label where
  | drain | stop
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .drain => pop PairOrdinalLoader.ordinalCell (fun _ b => b)
      (branch Option.isSome (goto (fun _ => .drain))
        (goto (fun _ => .stop)))
  | .stop => load (fun _ => none) halt

noncomputable def run (steps : Nat) (c : Config) : Config :=
  ((advance program)^[steps]) c

private theorem ord_update (nw vw ow sw fresh a b c : List Bool) :
    Function.update (PairOrdinalLoader.frame nw vw ow sw a b c)
      PairOrdinalLoader.ordinalCell fresh =
      PairOrdinalLoader.frame nw vw fresh sw a b c := by
  funext x
  by_cases hx : x = PairOrdinalLoader.ordinalCell
  · subst x
    simp [PairOrdinalLoader.frame, PairOrdinalLoader.nCell,
      PairOrdinalLoader.vCell, PairOrdinalLoader.ordinalCell,
      PairUnitLift.vertexCell, PairUnitLift.pairOrdinalCell]
  · simp [PairOrdinalLoader.frame, hx]

private theorem ord_get (nw vw ow sw a b c : List Bool) :
    PairOrdinalLoader.frame nw vw ow sw a b c
      PairOrdinalLoader.ordinalCell = ow := by
  simp [PairOrdinalLoader.frame, PairOrdinalLoader.nCell,
    PairOrdinalLoader.vCell, PairOrdinalLoader.ordinalCell,
    PairUnitLift.vertexCell, PairUnitLift.pairOrdinalCell]

private theorem drain_cons (nw vw sw a b c : List Bool)
    (m : Nat) (ctl : Option Bool) :
    advance program
      (⟨some .drain, ctl,
        PairOrdinalLoader.frame nw vw (List.replicate (m+1) true) sw a b c⟩ : Config) =
      ⟨some .drain, some true,
        PairOrdinalLoader.frame nw vw (List.replicate m true) sw a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, ord_get,
    ord_update, List.replicate_succ]

private theorem drain_nil (nw vw sw a b c : List Bool) (ctl : Option Bool) :
    advance program
      (⟨some .drain, ctl,
        PairOrdinalLoader.frame nw vw [] sw a b c⟩ : Config) =
      ⟨some .stop, none,
        PairOrdinalLoader.frame nw vw [] sw a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, ord_get, ord_update]

private theorem stop_step (nw vw sw a b c : List Bool) :
    advance program
      (⟨some .stop, none,
        PairOrdinalLoader.frame nw vw [] sw a b c⟩ : Config) =
      ⟨none, none,
        PairOrdinalLoader.frame nw vw [] sw a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux]

private theorem drain_loop (nw vw sw a b c : List Bool) (m : Nat)
    (ctl : Option Bool) :
    run m
      (⟨some .drain, ctl,
        PairOrdinalLoader.frame nw vw (List.replicate m true) sw a b c⟩ : Config) =
      ⟨some .drain, (if m = 0 then ctl else some true),
        PairOrdinalLoader.frame nw vw [] sw a b c⟩ := by
  induction m generalizing ctl with
  | zero => simp [run]
  | succ m ih =>
    rw [run, show m+1 = m+1 by omega,
      Function.iterate_add_apply, Function.iterate_one, drain_cons]
    simpa [run] using ih (some true)

theorem frame_run (nw vw sw a b c : List Bool) (m : Nat) :
    run (m+2)
      (⟨some .drain, none,
        PairOrdinalLoader.frame nw vw (List.replicate m true) sw a b c⟩ : Config) =
      ⟨none, none, PairOrdinalLoader.frame nw vw [] sw a b c⟩ := by
  rw [show m+2 = (1+1)+m by omega, run, Function.iterate_add_apply]
  change (advance program)^[1+1]
    (run m ⟨some .drain, none,
      PairOrdinalLoader.frame nw vw (List.replicate m true) sw a b c⟩) = _
  rw [drain_loop]
  rw [Function.iterate_add_apply]
  simp only [Function.iterate_one]
  rw [drain_nil, stop_step]

theorem pairBank_run (n v ordinal : Nat)
    (saved output count : List Bool) :
    run (ordinal+2)
      (⟨some .drain, none,
        PairUnitLift.pairBank n v ordinal saved output count⟩ : Config) =
      ⟨none, none, PairUnitLift.pairBank n v 0 saved output count⟩ := by
  rw [← PairOrdinalLoader.frame_pairBank n v ordinal saved output count,
    ← PairOrdinalLoader.frame_pairBank n v 0 saved output count]
  exact frame_run _ _ _ _ _ _ ordinal

#print axioms pairBank_run

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairOrdinalReset
