import Paper2.CodeAdminBranchJoin
import Paper2.CodeResultReset
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import Mathlib.Tactic

/-! Reset-clock bounds on the same actual raw controller run, without
reselecting an existential log-bank witness from a separate draw. -/

namespace Paper2.CodeUniformResetBound

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackGrowth
open GeneratorCode GeneratorSerialization GeneratorStateSize

noncomputable section

abbrev Stack := CodeInterpreterReset.Stack

private noncomputable instance : Fintype CodeAdminBranchJoin.Label := by
  classical
  letI : Fintype CodeAdminResultJoin.Label := inferInstance
  letI : Fintype (CodeAdminResultJoin.Control × CodeBranchAdapter.Label) :=
    inferInstance
  letI : Fintype (Unit ⊕ (CodeAdminResultJoin.Control × CodeBranchAdapter.Label)) :=
    inferInstance
  infer_instance

theorem start_clear_empty (s : State) (tape : List Bool) (B R : Nat)
    (k : Stack) (hk : ¬ CodeInterpreterReset.keep k) :
    (CodeAdminBranchJoin.start s tape B R).stk k = [] := by
  change (EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank
    CodeAdminDraw.adminSlot (CodeAdminDraw.foreign tape B R)
    (CodeAdminNormalization.stateCfg s).stk) k = []
  rcases k with k | k
  · have hn : ¬ ∃ x : CodeAdminMachine.Stack,
        CodeAdminDraw.adminSlot x = (Sum.inl k : Stack) := by
      simp [CodeAdminDraw.adminSlot]
    rw [EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_outside
      _ _ _ _ hn]
    rcases k with j | j
    · fin_cases j <;>
        simp_all [CodeAdminDraw.foreign,DrawParameterLoader.initialBank,
          DrawParameterLoader.mainBank,CodeInterpreterReset.keep]
    · simp [CodeAdminDraw.foreign,DrawParameterLoader.initialBank,
        DrawParameterLoader.mainBank]
  · rw [← show CodeAdminDraw.adminSlot k = (Sum.inr k : Stack) by rfl,
      EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_at]
    rcases k with j | j
    · fin_cases j <;>
        simp_all [CodeAdminNormalization.stateCfg,CodeAdminMachine.ready,
          CodeAdminMachine.cfg,CodeScanner.bank,CodeHeaderMachine.contents,
          CodeInterpreterReset.keep]
    · exact False.elim (hk (by simp [CodeInterpreterReset.keep]))

/-- The per-transition push constant belongs to the exact joined raw
administration/result/branch table, not a hypothetical earlier draw table. -/
def rawPushBound : Nat := perStep CodeAdminBranchJoin.program

def rawResetCap (t : Nat) : Nat :=
  CodeInterpreterReset.clearCount * (rawPushBound * t) +
    CodeInterpreterReset.clearCount + 2

/-- The same witnessed raw run bounds cleanup at its very own terminal bank.
There is no second existential draw/log witness in this theorem. -/
theorem raw_terminal_clock (s : State) (tape : List Bool) (B R t : Nat)
    (C : CodeAdminBranchJoin.Config)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = C) :
    CodeInterpreterReset.clock C.stk ≤ rawResetCap t := by
  have hslot (i : Fin CodeInterpreterReset.clearCount) :
      (C.stk (CodeInterpreterReset.slot i)).length ≤ rawPushBound * t := by
    have hg := run_growth CodeAdminBranchJoin.program
      (CodeAdminBranchJoin.start s tape B R) t
      (CodeInterpreterReset.slot i)
    change ((CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R)).stk
      (CodeInterpreterReset.slot i)).length ≤
      ((CodeAdminBranchJoin.start s tape B R).stk
        (CodeInterpreterReset.slot i)).length + rawPushBound * t at hg
    rw [hr,start_clear_empty s tape B R _
      (CodeInterpreterReset.slot_not_keep i)] at hg
    simpa using hg
  have hsum : (∑ i : Fin CodeInterpreterReset.clearCount,
      (C.stk (CodeInterpreterReset.slot i)).length) ≤
      CodeInterpreterReset.clearCount * (rawPushBound * t) := by
    calc
      _ ≤ ∑ _i : Fin CodeInterpreterReset.clearCount,
            rawPushBound * t := by
          apply Finset.sum_le_sum
          intro i _
          exact hslot i
      _ = _ := by simp [mul_comm]
  unfold CodeInterpreterReset.clock rawResetCap
  omega

theorem raw_terminal_clock_mono (s : State) (tape : List Bool)
    (B R t T : Nat) (C : CodeAdminBranchJoin.Config)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = C)
    (ht : t ≤ T) :
    CodeInterpreterReset.clock C.stk ≤ rawResetCap T := by
  have h := raw_terminal_clock s tape B R t C hr
  have hmul := Nat.mul_le_mul_left rawPushBound ht
  have hmul2 := Nat.mul_le_mul_left CodeInterpreterReset.clearCount hmul
  unfold rawResetCap at *
  omega

/-- The sampled branch index never appears in a public branch cost: it is
strictly smaller than its denominator, itself charged to the source code. -/
theorem branch_index_lt_codeSize (D a b : Nat) (f g h : Code)
    (q : Fin D) :
    q.val < codeSize (.branch3 D a b f g h) := by
  have hden : D ≤ codeSize (.branch3 D a b f g h) := by
    simp only [codeSize]
    omega
  omega

theorem branch_index_lt_root (root : Code) (s : State)
    (ht : Trace root s)
    (D a b : Nat) (f g h : Code) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.branch3 D a b f g h :: cs, outputWord.reverse⟩)
    (q : Fin D) : q.val < codeSize root := by
  have hi := branch_index_lt_codeSize D a b f g h q
  have hp : codeSize (.branch3 D a b f g h) ≤
      potential (GeneratorCode.normalize s) := by
    simp only [hstate,potential,codesSize,List.length_reverse]
    omega
  have hn := normalize_potential_le s
  have hr := trace_potential_le root s ht
  omega

#print axioms raw_terminal_clock
#print axioms branch_index_lt_codeSize
#print axioms branch_index_lt_root

end
end Paper2.CodeUniformResetBound
