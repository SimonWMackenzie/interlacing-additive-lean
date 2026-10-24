import CurrentAdditive.QuarticDispatchSize

/-! A single fixed-program assembly theorem with literal v27 branch specifications.
The five physical branch specifications remain explicit premises. -/

namespace Paper2.CurrentAdditive.QuarticDispatchAssembly

open Turing
open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticDispatchSpec

/-- The selected capped generator produced bytes on the actual v27 schedule. -/
def Good27 (Δ : ℕ) (γ : ℚ) : Cond Δ γ := fun g hg hn k t =>
  ∃ hc : ChecksCond27 Δ γ g hg hn k t,
    (QuarticProbeOutcome.genOut27 Δ γ g hg hn k hc t).isSome = true

/-- Front schedule decision, generator probe, successful writer, none writer, fallback writer. -/
def program27 {a : ℕ} {LF VF LP VP LS VS LN VN LU VU : Type}
    (front : LF → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LF VF) (vF : VF) (flag₁ : Fin (a + 3))
    (probe : LP → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LP VP) (sP : LP) (vP : VP) (flag₂ : Fin (a + 3))
    (succ : LS → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LS VS) (sS : LS) (vS : VS)
    (none_ : LN → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LN VN) (sN : LN) (vN : VN)
    (unsched : LU → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LU VU) (sU : LU) (vU : VU) :=
  Dispatch.seqDispatch front vF flag₁
    (Dispatch.seqDispatch probe vP flag₂ succ sS none_ sN vS vN)
    (BitMachineRawSequence.leftLabel sP) unsched sU
    (vP, ((none : Option Bool), (vS, vN))) vU

/-- The exact v27 selected-word local run follows from physical specifications
for each of the five fixed tables. No branch existence is assumed implicitly. -/
theorem localRun_program27 (Δ : ℕ) (γ : ℚ) (a : ℕ)
    {LF VF LP VP LS VS LN VN LU VU : Type}
    (front : LF → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LF VF) (sF : LF) (vF : VF) (flag₁ : Fin (a + 3))
    (probe : LP → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LP VP) (sP : LP) (vP : VP) (flag₂ : Fin (a + 3))
    (succ : LS → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LS VS) (sS : LS) (vS : VS)
    (none_ : LN → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LN VN) (sN : LN) (vN : VN)
    (unsched : LU → TM2.Stmt (fun _ : Fin (a + 3) => Bool) LU VU) (sU : LU) (vU : VU)
    (j : Fin (a + 3)) (Mid₁ Mid₂ : Pred Δ γ a)
    (CF EF CP EP CS ES CN EN CU EU : ℕ)
    (hFront : DecideSpec Δ γ a front sF vF flag₁ (IsInput27 Δ γ a) Mid₁
      (ChecksCond27 Δ γ) CF EF)
    (hProbe : DecideSpec Δ γ a probe sP vP flag₂
      (fun g hg hn k t S => Mid₁ g hg hn k t S ∧ ChecksCond27 Δ γ g hg hn k t)
      Mid₂ (Good27 Δ γ) CP EP)
    (hSucc : BranchSpec Δ γ a succ sS vS j
      (fun g hg hn k t S => Mid₂ g hg hn k t S ∧ Good27 Δ γ g hg hn k t) CS ES)
    (hNone : BranchSpec Δ γ a none_ sN vN j
      (fun g hg hn k t S => Mid₂ g hg hn k t S ∧ ¬ Good27 Δ γ g hg hn k t) CN EN)
    (hUnsched : BranchSpec Δ γ a unsched sU vU j
      (fun g hg hn k t S => Mid₁ g hg hn k t S ∧ ¬ ChecksCond27 Δ γ g hg hn k t) CU EU) :
    LocalRun27 Δ γ a
      (program27 front vF flag₁ probe sP vP flag₂ succ sS vS none_ sN vN unsched sU vU)
      (BitMachineRawSequence.leftLabel sF)
      (vF, ((none : Option Bool), ((vP, ((none : Option Bool), (vS, vN))), vU))) j
      (CF + (CP + CS + CN + 2) + CU + 2)
      (max EF (max (max EP (max ES EN)) EU)) := by
  have hS := seq_dispatch_spec Δ γ a probe sP vP flag₂ succ sS vS none_ sN vN j
    (fun g hg hn k t S => Mid₁ g hg hn k t S ∧ ChecksCond27 Δ γ g hg hn k t)
    Mid₂ (Good27 Δ γ) CP EP CS ES CN EN hProbe hSucc hNone
  have hAll := seq_dispatch_spec Δ γ a front sF vF flag₁
    (Dispatch.seqDispatch probe vP flag₂ succ sS none_ sN vS vN)
    (BitMachineRawSequence.leftLabel sP) (vP, ((none : Option Bool), (vS, vN)))
    unsched sU vU j (IsInput27 Δ γ a) Mid₁ (ChecksCond27 Δ γ)
    CF EF (CP + CS + CN + 2) (max EP (max ES EN)) CU EU hFront hS hUnsched
  exact localRun27_of_spec Δ γ a _ _ _ j _ _ hAll

#print axioms localRun_program27

end Paper2.CurrentAdditive.QuarticDispatchAssembly
