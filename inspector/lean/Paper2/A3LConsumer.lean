import Paper2.A3LSuccSpec

/-!
# Consumer-shape check (not a requested segment): segments 1-2 plug into `A3H3Run.H_A3_R12`

Lane `owner:a-h-a3-lift-2` (private, 26 September 2026). Pure composition: with the frozen owner-1
`hUnsched_spec` and this lane's `hProbe_spec`, `hSucc_spec`, the production `Unit4Shell.Shells.H_A3 Δ γ` follows from
exactly two named premises, `hFront` (the front lane's DecideSpec onto Mid1) and `hNone` (the none branch from
`Mid2 ∧ ¬ Good`). Also checks that every finite-control instance `H_A3_R12` needs is found.
-/

set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 16384

namespace Paper2.A3Assembly.Lift

open Turing
open EthInapproximability.CurrentPaper
open Paper2

theorem H_A3_of_front_none (FS : Type) [Fintype FS] [DecidableEq FS] (Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) {LF VF LN VN : Type} [Fintype LF] [Fintype VF] [Fintype LN] [Fintype VN]
    (front : LF → TM2.Stmt (fun _ : Fin (a FS + 3) => Bool) LF VF) (sF : LF) (vF : VF)
    (none_ : LN → TM2.Stmt (fun _ : Fin (a FS + 3) => Bool) LN VN) (sN : LN) (vN : VN)
    (CF EF CN EN CM EM : ℕ)
    (hFront : Run.DecideSpec Δ γ (a FS) front sF vF (flag₁ FS) (Run.IsInput Δ γ (a FS))
      (Mid1 FS Δ γ CM EM) (Run.ChecksCond Δ γ) CF EF)
    (hNone : Run.BranchSpec Δ γ (a FS) none_ sN vN (outJ FS)
      (fun g hg hn k t S => Mid2C FS Δ γ (PC FS CM) (PE EM) g hg hn k t S ∧ ¬ Good Δ γ g hg hn k t)
      CN EN) :
    Unit4Shell.Shells.H_A3 Δ γ :=
  Run.H_A3_R12 Δ γ hΔ hγ (a FS) front sF vF (flag₁ FS) (pProg FS) pStart pCtl (flag₂ FS)
    (sProg FS) sStart sCtl none_ sN vN (uProg FS) uStart ((none : Option Bool), Unsched.ctlU) (outJ FS)
    (Mid1 FS Δ γ CM EM) (Mid2C FS Δ γ (PC FS CM) (PE EM)) (Good Δ γ)
    CF EF (PC FS CM) (PE EM) (SC FS (PC FS CM)) (SE (PE EM)) CN EN (UC FS Δ γ CM) (max EM 160)
    hFront (hProbe_spec FS Δ γ CM EM) (hSucc_spec FS Δ γ (PC FS CM) (PE EM)) hNone
    (fun hΔ hγ => hUnsched_spec FS Δ γ hΔ hγ CM EM)

end Paper2.A3Assembly.Lift

#print axioms Paper2.A3Assembly.Lift.H_A3_of_front_none
