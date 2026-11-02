import CurrentAdditive.TrialSearchCombinedRun
import CurrentAdditive.TrialInputPrepBridge

/-!
The input-preparation phase of the single combined program is an actual
execution of the checked seven-stack preparation instructions, with the
same produced divider words and no more than its checked clock.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPrep

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun
open CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine

theorem prepStack_injective : Function.Injective prepStack := by
  intro x y h
  apply Fin.ext
  simpa [prepStack] using congrArg Fin.val h

def initialStacks (candidate divisor shift : List Bool) : Fin 12 → List Bool :=
  fun k => if k = 0 then candidate else if k = 1 then divisor else
    if k = 2 then shift else []

theorem prepProjection (candidate divisor shift : List Bool) :
    (fun k : Fin 7 => initialStacks candidate divisor shift (prepStack k)) =
      TrialInputPrepMachine.bank candidate divisor shift [] [] [] [] := by
  funext k
  fin_cases k <;> rfl

def initialRegisters : Registers :=
  ⟨none, (false, none, none), (false, none), (false, true, none)⟩

theorem prep_halts_in_combined_program (candidate divisor shift : List Bool) :
    ∃ t ≤ 2 * (shift.length + candidate.length + divisor.length) + 6,
      let g := TrialSearchCombinedMachine.run t
        ⟨some (.prep .shiftScan), initialRegisters,
          initialStacks candidate divisor shift⟩
      g.l = some (.divide .next) ∧
      g.stk 0 = candidate ∧
      g.stk 1 = divisor ∧
      g.stk 2 = shift ∧
      g.stk 3 = true :: candidate.reverse ∧
      g.stk 4 = true :: divisor.reverse ++ List.replicate shift.length false ∧
      g.stk 5 = true :: List.replicate shift.length true ∧
      g.stk 6 = [] ∧ g.stk 7 = [] := by
  let n := 2 * (shift.length + candidate.length + divisor.length) + 6
  have hprogram (l : TrialInputPrepMachine.Label) :
      TrialSearchCombinedMachine.program (.prep l) =
      embedStmt prepStack Label.prep (.divide .next)
        (fun r => r.prep) (fun r v => {r with prep := v})
        (fun r => {r with divide := (false, none, none)})
        (TrialInputPrepMachine.program l) := rfl
  have hhalt :
      (TrialInputPrepMachine.run n
        (TrialInputPrepMachine.cfg (some .shiftScan) none
          candidate divisor shift [] [] [] [])).l = none := by
    rw [TrialInputPrepMachine.run_prepare]
    rfl
  have hlocal :
      ((((advance TrialInputPrepMachine.program)^[n])
        (⟨some TrialInputPrepMachine.Label.shiftScan,
          initialRegisters.prep,
          fun k => initialStacks candidate divisor shift (prepStack k)⟩ :
            TrialInputPrepMachine.Config)).l = none) := by
    simpa [TrialInputPrepMachine.run, initialRegisters, prepProjection] using hhalt
  obtain ⟨t, ht, hrel⟩ :=
    phaseRel_halts_within prepStack prepStack_injective
      Label.prep (.divide .next)
      (fun r => r.prep) (fun r v => {r with prep := v})
      (fun r => {r with divide := (false, none, none)})
      (by intro r v; rfl) (by intro r v w; rfl)
      (by intro r; cases r; rfl) (by intro r; rfl)
      TrialInputPrepMachine.program TrialSearchCombinedMachine.program
      hprogram initialRegisters (initialStacks candidate divisor shift)
      .shiftScan n hlocal
  refine ⟨t, ht, ?_⟩
  have hrun := TrialInputPrepMachine.run_prepare candidate divisor shift
  change ((advance TrialInputPrepMachine.program)^[n])
      (TrialInputPrepMachine.cfg (some .shiftScan) none
        candidate divisor shift [] [] [] []) = _ at hrun
  rw [show TrialInputPrepMachine.cfg (some .shiftScan) none candidate divisor shift
      [] [] [] [] =
      (⟨some TrialInputPrepMachine.Label.shiftScan, none,
        fun k => initialStacks candidate divisor shift (prepStack k)⟩ :
          TrialInputPrepMachine.Config) from by
        simp [TrialInputPrepMachine.cfg, prepProjection]] at hrun
  simp only [initialRegisters] at hrel
  rw [hrun] at hrel
  rcases hrel with ⟨hl, _, hs, hf⟩
  refine ⟨hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · exact hs 4
  · exact hs 5
  · exact hs 6
  · exact hf 7 (by
      intro k heq
      have hk := k.isLt
      have hv := congrArg Fin.val heq
      simp [prepStack] at hv
      omega)

#print axioms prep_halts_in_combined_program

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPrep
