import Paper2.Y0TapeInput

/-! The inherited loader's program parameters are initial finite controls,
not encoded scalar inputs. Their values are independent of the basic unary
words. This licenses one fixed program for each fixed `t,lambda`. -/

namespace Paper2.YaoEntryControllerJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Paper2.YaoEntryParameterJoin
open Paper2.YaoParameterBank

noncomputable def fixedStageControl (t lambda : ℕ) :
    StageOneControl t lambda :=
  ((frameStart t lambda 0 0 0 0 0).var,())

noncomputable def fixedSelectorControl (t lambda : ℕ) :
    SelectorControl t lambda :=
  (selectorInitial t lambda 0 0 0 0 0).var

theorem frame_start_control_constant (t lambda e z g ell p : ℕ) :
    ((frameStart t lambda e z g ell p).var,()) =
      fixedStageControl t lambda := by
  rfl

theorem selector_start_control_constant (t lambda e z g ell p : ℕ) :
    (selectorInitial t lambda e z g ell p).var =
      fixedSelectorControl t lambda := by
  rfl

theorem routed_program_constant (t lambda e z g ell p : ℕ) :
    routedParameterProgram t lambda
      ((frameStart t lambda e z g ell p).var,())
      (selectorInitial t lambda e z g ell p).var =
    routedParameterProgram t lambda
      (fixedStageControl t lambda) (fixedSelectorControl t lambda) := by
  rw [frame_start_control_constant,selector_start_control_constant]

#print axioms frame_start_control_constant
#print axioms selector_start_control_constant
#print axioms routed_program_constant

end Paper2.YaoEntryControllerJoin
