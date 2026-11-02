import EthInapproximability.CurrentPaper.BinarySuccessorMachine

/-! # Explicit finite indices for the variable-width successor controller

This is a computable reindexing of the already proved two-label, three-control
successor program. The new machine has literal `Fin 2` stack/label indices and
literal `Fin 3` control indices; no `Fintype.equivFin` choice occurs in its
program definition. Renaming preserves each physical transition exactly.
-/

namespace EthInapproximability.CurrentPaper.BinarySuccessorLiteral

open Turing BitMachine BitMachineEncoding BinarySuccessorMachine

def labelEquiv : BinarySuccessorMachine.Label ≃ Fin 2 where
  toFun
    | .carry => 0
    | .restore => 1
  invFun j := if j = 0 then .carry else .restore
  left_inv l := by cases l <;> rfl
  right_inv j := by fin_cases j <;> rfl

def controlEquiv : Option Bool ≃ Fin 3 where
  toFun
    | none => 0
    | some false => 1
    | some true => 2
  invFun j := if j = 0 then none else if j = 1 then some false else some true
  left_inv v := by cases v with
    | none => rfl
    | some b => cases b <;> rfl
  right_inv j := by fin_cases j <;> rfl

def machine : BitMachine.Machine where
  stackCount := 2
  labelCount := 2
  controlCount := 3
  input := 0
  output := 0
  start := 0
  initial := 0
  program l := renameStmt (Equiv.refl (Fin 2)) labelEquiv controlEquiv
    (BinarySuccessorMachine.program (labelEquiv.symm l))

theorem initial_cfg (q : List Bool) :
    machine.init q = renameCfg (Equiv.refl (Fin 2)) labelEquiv controlEquiv
      (BinarySuccessorMachine.cfg (some .carry) none q []) := by
  rfl

theorem run_raw (q : List Bool) :
    machine.run (2 * BinarySuccessorMachine.carryCount q + 2)
      (machine.init q) =
      renameCfg (Equiv.refl (Fin 2)) labelEquiv controlEquiv
        (BinarySuccessorMachine.cfg none none
          (BinarySuccessorMachine.successor q) []) := by
  have h := rename_run (Equiv.refl (Fin 2)) labelEquiv controlEquiv
    BinarySuccessorMachine.program
    (BinarySuccessorMachine.cfg (some .carry) none q [])
    (2 * BinarySuccessorMachine.carryCount q + 2)
  have hraw := BinarySuccessorMachine.run_correct none q []
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil,
    List.nil_append] at hraw
  change ((advance BinarySuccessorMachine.program)^[2 * carryCount q + 2])
    (BinarySuccessorMachine.cfg (some .carry) none q []) = _ at hraw
  rw [hraw] at h
  simpa only [List.length_nil, Nat.add_zero, List.reverse_nil,
    List.nil_append, machine, Machine.run, Machine.step,
    initial_cfg, advance] using h

theorem outputs_all (q : List Bool) :
    machine.OutputsWithin q (BinarySuccessorMachine.successor q)
      (2*q.length+2) := by
  refine ⟨2*BinarySuccessorMachine.carryCount q+2, by
    have h := BinarySuccessorMachine.carryCount_le_length q
    omega, ?_, ?_⟩
  · rw [run_raw]
    rfl
  · rw [run_raw]
    rfl

end EthInapproximability.CurrentPaper.BinarySuccessorLiteral
