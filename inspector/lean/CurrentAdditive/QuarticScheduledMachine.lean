import CurrentAdditive.QuarticUnschedLift
import CurrentAdditive.QuarticSuccessLift
import CurrentAdditive.QuarticProbeLift
import CurrentAdditive.QuarticNoneLift

/-! One fixed scheduled-branch program: physical generator probe followed by
the correct success or none output writer. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticScheduledMachine

open Turing
open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly Paper2.A3Assembly.Lift Paper2.A3Assembly.Lift3
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticDispatchAssembly
open Paper2.CurrentAdditive.QuarticProbeLift
open Paper2.CurrentAdditive.QuarticSuccessLift
open Paper2.CurrentAdditive.QuarticNoneLift

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- The fixed probe followed by a one-bit dispatch to the two fixed scheduled
writers. The stack layout and programs do not depend on the graph or tape. -/
noncomputable def scheduledProg27 :=
  Dispatch.seqDispatch (pProg FS) pCtl (flag₂ FS)
    (sProg FS) sStart (nProg FS)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (.inl ⟨0, by omega⟩))))) sCtl NoneOut.ctlN

/-- Actual one-program scheduled branch, from the v27 prepared bank and check
to the exact selected output word, with charged physical runtime and bank size. -/
theorem scheduled_branch_spec27 (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) :
    BranchSpec Δ γ (a FS) (scheduledProg27 FS)
      (BitMachineRawSequence.leftLabel pStart)
      (pCtl, ((none : Option Bool), (sCtl, NoneOut.ctlN)))
      (outJ FS)
      (fun g hg hn k t S =>
        QuarticLayout.Mid1_27 FS Δ γ CM EM g hg hn k t S ∧
          ChecksCond27 Δ γ g hg hn k t)
      (PC FS CM + SC FS (PC FS CM) + NC FS (PC FS CM) + 2)
      (max (PE EM) (max (SE (PE EM)) (max (PE EM) Paper2.A3Assembly.Clocks.EN))) := by
  have h := seq_dispatch_spec Δ γ (a FS)
    (pProg FS) pStart pCtl (flag₂ FS)
    (sProg FS) sStart sCtl
    (nProg FS)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (.inl ⟨0, by omega⟩))))) NoneOut.ctlN
    (outJ FS)
    (fun g hg hn k t S =>
      QuarticLayout.Mid1_27 FS Δ γ CM EM g hg hn k t S ∧
        ChecksCond27 Δ γ g hg hn k t)
    (Mid2C27 FS Δ γ (PC FS CM) (PE EM)) (Good27 Δ γ)
    (PC FS CM) (PE EM)
    (SC FS (PC FS CM)) (SE (PE EM))
    (NC FS (PC FS CM)) (max (PE EM) Paper2.A3Assembly.Clocks.EN)
    (hProbe_spec27 FS Δ γ CM EM)
    (hSucc_spec27 FS Δ γ (PC FS CM) (PE EM))
    (hNone_spec27 FS Δ γ (PC FS CM) (PE EM))
  simpa only [scheduledProg27, max_assoc] using h

#print axioms scheduled_branch_spec27

end Paper2.CurrentAdditive.QuarticScheduledMachine
