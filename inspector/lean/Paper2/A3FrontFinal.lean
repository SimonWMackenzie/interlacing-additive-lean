import Paper2.FrontClockF

/-! Unit 3, lane a-success-table-13, segment (4) closed: the hFront `DecideSpec` of `A3H3Run.H_A3_R12` with no premise
beyond `0 < γ`, `0 < Δ` (both hypotheses of `H_A3_R12`), and its consumption by `H_A3_R12` checked by
instantiation (the other four table specifications stay named hypotheses; they are other lanes' units). -/

set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 16384
set_option synthInstance.maxHeartbeats 400000

namespace Paper2.FrontLift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open Paper2.A3Assembly

/-- **The hFront specification** (segments 1-4). -/
theorem hFront_final (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) :
    Run.DecideSpec Δ γ (Lift.a FS) (front Δ γ) (sF Δ γ) (vF Δ γ) (Lift.flag₁ FS)
      (Run.IsInput Δ γ (Lift.a FS))
      (Lift.Mid1 FS Δ γ (CM Δ γ 2) (EM (FrontClock13.cF Δ γ * 266 * 45)))
      (Run.ChecksCond Δ γ) 2 (FrontClock13.cF Δ γ * 266 * 45) :=
  hFront Δ γ hγ hΔ 2 _ (FrontClock13.frontClock Δ γ)

/-- Consumption check: `H_A3_R12` accepts `hFront_final` at `a = Lift.a FS`, `flag₁ = Lift.flag₁ FS`,
`Mid₁ = Lift.Mid1 FS …` (the label and control types of `front` are `Fintype`, found by instance search). -/
theorem H_A3_of_front (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    {LP VP LS VS LN VN LU VU : Type}
    [Fintype LP] [Fintype VP] [Fintype LS] [Fintype VS] [Fintype LN] [Fintype VN] [Fintype LU] [Fintype VU]
    (probe : LP → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) LP VP) (sP : LP) (vP : VP)
    (flag₂ : Fin (Lift.a FS + 3))
    (succ : LS → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) LS VS) (sS : LS) (vS : VS)
    (none_ : LN → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) LN VN) (sN : LN) (vN : VN)
    (unsched : LU → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) LU VU) (sU : LU) (vU : VU)
    (j : Fin (Lift.a FS + 3)) (Mid₂ : Run.Pred Δ γ (Lift.a FS)) (Good : Run.Cond Δ γ)
    (CP EP CS ES CN EN CU EU : ℕ)
    (hProbe : Run.DecideSpec Δ γ (Lift.a FS) probe sP vP flag₂
      (fun g hg hn k t S => Lift.Mid1 FS Δ γ (CM Δ γ 2) (EM (FrontClock13.cF Δ γ * 266 * 45)) g hg hn k t S ∧
        Run.ChecksCond Δ γ g hg hn k t) Mid₂ Good CP EP)
    (hSucc : Run.BranchSpec Δ γ (Lift.a FS) succ sS vS j
      (fun g hg hn k t S => Mid₂ g hg hn k t S ∧ Good g hg hn k t) CS ES)
    (hNone : Run.BranchSpec Δ γ (Lift.a FS) none_ sN vN j
      (fun g hg hn k t S => Mid₂ g hg hn k t S ∧ ¬ Good g hg hn k t) CN EN)
    (hUnsched : 0 < Δ → 0 < γ → Run.BranchSpec Δ γ (Lift.a FS) unsched sU vU j
      (fun g hg hn k t S => Lift.Mid1 FS Δ γ (CM Δ γ 2) (EM (FrontClock13.cF Δ γ * 266 * 45)) g hg hn k t S ∧
        ¬ Run.ChecksCond Δ γ g hg hn k t) CU EU) :
    Unit4Shell.Shells.H_A3 Δ γ :=
  Run.H_A3_R12 Δ γ hΔ hγ (Lift.a FS) (front Δ γ) (sF Δ γ) (vF Δ γ) (Lift.flag₁ FS)
    probe sP vP flag₂ succ sS vS none_ sN vN unsched sU vU j
    (Lift.Mid1 FS Δ γ (CM Δ γ 2) (EM (FrontClock13.cF Δ γ * 266 * 45))) Mid₂ Good
    2 (FrontClock13.cF Δ γ * 266 * 45) CP EP CS ES CN EN CU EU
    (hFront_final Δ γ hγ hΔ) hProbe hSucc hNone hUnsched

end

end Paper2.FrontLift

#print axioms Paper2.FrontLift.hFront_final
#print axioms Paper2.FrontLift.H_A3_of_front
