import CurrentAdditive.QuarticScheduledMachine
import CurrentAdditive.QuarticUnschedLift

/-! The v27 fixed input-to-output machine is now reduced to one explicit
physical front specification. All downstream physical branches are proved. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticFrontOnlyMachine

open Turing
open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly Paper2.A3Assembly.Lift Paper2.A3Assembly.Lift3
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticDispatchAssembly
open Paper2.CurrentAdditive.QuarticProbeLift
open Paper2.CurrentAdditive.QuarticSuccessLift
open Paper2.CurrentAdditive.QuarticNoneLift
open Paper2.CurrentAdditive.QuarticUnschedLift

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- One explicit remaining front obligation, with literal v27 input, quartic
prepared bank, and literal public-check bit. -/
def FrontSpec27 (Δ : ℕ) (γ : ℚ) {LF VF : Type}
    (front : LF → TM2.Stmt (fun _ : Fin (a FS + 3) => Bool) LF VF)
    (sF : LF) (vF : VF) (CM EM CF EF : ℕ) : Prop :=
  DecideSpec Δ γ (a FS) front sF vF (flag₁ FS)
    (IsInput27 Δ γ (a FS))
    (QuarticLayout.Mid1_27 FS Δ γ CM EM)
    (ChecksCond27 Δ γ) CF EF

/-- Conditional final assembly: all physical probe and branch programs are
concrete and checked; the only hypothesis is the actual front program's run. -/
theorem localRun_of_front27 (Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    {LF VF : Type}
    (front : LF → TM2.Stmt (fun _ : Fin (a FS + 3) => Bool) LF VF)
    (sF : LF) (vF : VF) (CM EM CF EF : ℕ)
    (hFront : FrontSpec27 FS Δ γ front sF vF CM EM CF EF) :
    LocalRun27 Δ γ (a FS)
      (program27 front vF (flag₁ FS)
        (pProg FS) pStart pCtl (flag₂ FS)
        (sProg FS) sStart sCtl
        (nProg FS) (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))) NoneOut.ctlN
        (uProg FS) uStart ((none : Option Bool), Unsched.ctlU))
      (BitMachineRawSequence.leftLabel sF)
      (vF, ((none : Option Bool),
        ((pCtl, ((none : Option Bool), (sCtl, NoneOut.ctlN))),
          ((none : Option Bool), Unsched.ctlU))))
      (outJ FS)
      (CF +
        (PC FS CM + SC FS (PC FS CM) + NC FS (PC FS CM) + 2) +
        UC27 FS Δ γ CM + 2)
      (max EF
        (max (max (PE EM)
            (max (SE (PE EM)) (max (PE EM) Paper2.A3Assembly.Clocks.EN)))
          (max EM 160))) := by
  exact localRun_program27 Δ γ (a FS)
    front sF vF (flag₁ FS)
    (pProg FS) pStart pCtl (flag₂ FS)
    (sProg FS) sStart sCtl
    (nProg FS) (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))) NoneOut.ctlN
    (uProg FS) uStart ((none : Option Bool), Unsched.ctlU)
    (outJ FS)
    (QuarticLayout.Mid1_27 FS Δ γ CM EM)
    (Mid2C27 FS Δ γ (PC FS CM) (PE EM))
    CF EF (PC FS CM) (PE EM)
    (SC FS (PC FS CM)) (SE (PE EM))
    (NC FS (PC FS CM)) (max (PE EM) Paper2.A3Assembly.Clocks.EN)
    (UC27 FS Δ γ CM) (max EM 160)
    hFront
    (hProbe_spec27 FS Δ γ CM EM)
    (hSucc_spec27 FS Δ γ (PC FS CM) (PE EM))
    (hNone_spec27 FS Δ γ (PC FS CM) (PE EM))
    (hUnsched_spec27 FS Δ γ hΔ hγ CM EM)

#print axioms localRun_of_front27

end Paper2.CurrentAdditive.QuarticFrontOnlyMachine
