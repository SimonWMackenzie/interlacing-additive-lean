import Paper2.CodeFullCleanStep
import Paper2.CodeUniformResetBound
import Mathlib.Tactic

/-! The fixed one-step machine's reset cost is bounded from the very same
raw run that reaches its terminal bank, not an independently chosen witness. -/

namespace Paper2.CodeFullCleanBound

open EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization

noncomputable section

def publicStepCap (T : Nat) : Nat :=
  T + CodeUniformResetBound.rawResetCap T

theorem raw_clean_public (s : State) (tape : List Bool) (B R : Nat)
    (d : CodeAdminBranchJoin.Config) (t T : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none) (ht : t ≤ T) :
    ∃ u ≤ publicStepCap T,
      CodeFullCleanStep.run u (CodeFullCleanStep.start s tape B R) =
        CodeFullCleanStep.resetCfg
          (CodeInterpreterReset.final d.var d.stk) := by
  obtain ⟨u,hu,hru⟩ := CodeFullCleanStep.raw_clean_from_reached
    s tape B R d t hr hd
  have hc := CodeUniformResetBound.raw_terminal_clock_mono
    s tape B R t T d hr ht
  refine ⟨u,?_,hru⟩
  unfold publicStepCap
  omega

#print axioms raw_clean_public

end
end Paper2.CodeFullCleanBound
