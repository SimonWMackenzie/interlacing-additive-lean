import CurrentAdditive.RoundedCodeAdminBit
import CurrentAdditive.RoundedCodeHandle
import CurrentAdditive.RoundedCodeCanonical

/-! One fixed physical Code step: normalize, round a fresh block, consume the
ticket, and clear every nonpersistent bank. The final Boolean distinguishes
an exhausted code from a successful draw. The source-specific step theorems
must instantiate the component executions below; these composition lemmas
alone are not a whole-source execution theorem. -/

namespace EthInapproximability.CurrentPaper.RoundedCodeStep

open Turing Turing.TM2.Stmt BitMachineEncoding
noncomputable section

abbrev Stack := RoundedCodeDraw.Stack
abbrev Core := RoundedCodeAdmin.Control × (RoundedCodeHandle.Control × Bool)
abbrev Control := Core × Option Bool

def finalControl (done : Bool) : Control :=
  ((RoundedCodeAdmin.initial, (RoundedCodeHandle.initial, done)), none)
def initial : Control := finalControl false

def adminLift (v : RoundedCodeAdmin.Control) : Control :=
  ((v, (RoundedCodeHandle.initial, false)), none)

def handleLift (kind : Paper2.CodeHeaderMachine.Kind) (v : RoundedCodeHandle.Control) : Control :=
  (((RoundedCodeAdmin.kindControl kind, RoundedLoadedDraw.initial), (v, false)), none)

def kindOf (v : Control) : Option Paper2.CodeHeaderMachine.Kind := v.1.1.1.1.2

inductive Label where
  | admin (l : RoundedCodeAdmin.Label)
  | route
  | handle (kind : Paper2.CodeHeaderMachine.Kind) (l : RoundedCodeHandle.Label)
  | cleanup (l : RoundedCodeReset.Label)
  | finish
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .admin l => BitMachineInline.stmt Label.admin adminLift (fun v => v.1.1)
      (some .route) (RoundedCodeAdmin.program l)
  | .route =>
      branch (fun v => (kindOf v).isSome)
        (load (fun v => handleLift ((kindOf v).getD .emit) RoundedCodeHandle.initial)
          (goto (fun v => .handle ((kindOf v).getD .emit)
            (.route ((kindOf v).getD .emit)))))
        (load (fun _ => finalControl true) (goto (fun _ => .cleanup (.inl 0))))
  | .handle kind l => BitMachineInline.stmt (Label.handle kind) (handleLift kind)
      (fun v => v.1.2.1) (some (.cleanup (.inl 0))) (RoundedCodeHandle.program l)
  | .cleanup l => BitMachineInline.stmt Label.cleanup id id (some .finish)
      (RoundedCodeReset.program (Flag := Core) l)
  | .finish => load (fun v => finalControl v.1.2.2) halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def adminCfg (c : RoundedCodeAdmin.Config) : Config :=
  BitMachineInline.cfg Label.admin adminLift (some .route) c

def handleCfg (kind : Paper2.CodeHeaderMachine.Kind) (c : RoundedCodeHandle.Config) : Config :=
  BitMachineInline.cfg (Label.handle kind) (handleLift kind) (some (.cleanup (.inl 0))) c

def start (s : Paper2.GeneratorCode.State) (bits : List Bool) (b : ℕ) : Config :=
  adminCfg (RoundedCodeAdmin.start s bits b)

private theorem join_run {c d : Config} {u : ℕ} (h : run u c = d) (v : ℕ) :
    run (u + v) c = run v d := by
  rw [Nat.add_comm u v]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem admin_to_route (c d : RoundedCodeAdmin.Config) (t : ℕ)
    (hr : RoundedCodeAdmin.run t c = d) (hh : d.l = none) :
    ∃ u ≤ t, run u (adminCfg c) = ⟨some .route, adminLift d.var, d.stk⟩ := by
  have hhalt : (((advance RoundedCodeAdmin.program)^[t]) c).l = none := by
    change (RoundedCodeAdmin.run t c).l = none
    rw [hr]
    exact hh
  obtain ⟨u, hu, hur⟩ := BitMachineInline.outputs Label.admin adminLift (fun v => v.1.1)
    (by intro v; rfl) (some .route) RoundedCodeAdmin.program program (by intro l; rfl) c t hhalt
  change run u (adminCfg c) = BitMachineInline.cfg Label.admin adminLift (some .route)
    (RoundedCodeAdmin.run t c) at hur
  rw [hr] at hur
  exact ⟨u, hu, by simpa [BitMachineInline.cfg, hh] using hur⟩

theorem route_success (v : RoundedCodeAdmin.Control) (S : Stack → List Bool)
    (kind : Paper2.CodeHeaderMachine.Kind) (hk : v.1.1.2 = some kind) :
    run 1 ⟨some .route, adminLift v, S⟩ =
      handleCfg kind (RoundedCodeHandle.start kind S) := by
  simp [run, program, advance, TM2.step, TM2.stepAux, adminLift, handleLift,
    kindOf, hk, handleCfg, RoundedCodeHandle.start, BitMachineInline.cfg,
    RoundedCodeAdmin.kindControl]

theorem route_done (v : RoundedCodeAdmin.Control) (S : Stack → List Bool)
    (hk : v.1.1.2 = none) :
    run 1 ⟨some .route, adminLift v, S⟩ =
      ⟨some (.cleanup (.inl 0)), finalControl true, S⟩ := by
  simp [run, program, advance, TM2.step, TM2.stepAux, adminLift, kindOf, hk]

theorem handle_to_cleanup (kind : Paper2.CodeHeaderMachine.Kind)
    (c d : RoundedCodeHandle.Config) (t : ℕ)
    (hr : RoundedCodeHandle.run t c = d) (hh : d.l = none) :
    ∃ u ≤ t, run u (handleCfg kind c) =
      ⟨some (.cleanup (.inl 0)), handleLift kind d.var, d.stk⟩ := by
  have hhalt : (((advance RoundedCodeHandle.program)^[t]) c).l = none := by
    change (RoundedCodeHandle.run t c).l = none
    rw [hr]
    exact hh
  obtain ⟨u, hu, hur⟩ := BitMachineInline.outputs (Label.handle kind) (handleLift kind)
    (fun v => v.1.2.1) (by intro v; rfl) (some (.cleanup (.inl 0)))
    RoundedCodeHandle.program program (by intro l; rfl) c t hhalt
  change run u (handleCfg kind c) =
    BitMachineInline.cfg (Label.handle kind) (handleLift kind) (some (.cleanup (.inl 0)))
      (RoundedCodeHandle.run t c) at hur
  rw [hr] at hur
  exact ⟨u, hu, by simpa [BitMachineInline.cfg, hh] using hur⟩

theorem cleanup_to_end (core : Core) (S : Stack → List Bool) :
    ∃ u ≤ RoundedCodeReset.clock S + 1,
      run u ⟨some (.cleanup (.inl 0)), (core, none), S⟩ =
        ⟨none, finalControl core.2.2, RoundedCodeReset.resetBank S⟩ := by
  have hr := RoundedCodeReset.physical_reset core S
  have hh : (((advance (RoundedCodeReset.program (Flag := Core)))^[RoundedCodeReset.clock S])
      (⟨some (.inl 0), (core, none), S⟩ : RoundedCodeReset.Config Core)).l = none := by
    rw [hr]
  obtain ⟨u, hu, hur⟩ := BitMachineInline.outputs Label.cleanup id id (by intro v; rfl)
    (some .finish) (RoundedCodeReset.program (Flag := Core)) program (by intro l; rfl)
    (⟨some (.inl 0), (core, none), S⟩ : RoundedCodeReset.Config Core)
    (RoundedCodeReset.clock S) hh
  rw [hr] at hur
  change run u ⟨some (.cleanup (.inl 0)), (core, none), S⟩ =
    ⟨some .finish, (core, none), RoundedCodeReset.resetBank S⟩ at hur
  refine ⟨u + 1, by omega, ?_⟩
  rw [join_run hur 1]
  simp [run, advance, TM2.step, TM2.stepAux, program]

theorem compose_success (c d : RoundedCodeAdmin.Config) (ta : ℕ)
    (ha : RoundedCodeAdmin.run ta c = d) (hd : d.l = none)
    (kind : Paper2.CodeHeaderMachine.Kind) (hk : d.var.1.1.2 = some kind)
    (e : RoundedCodeHandle.Config) (th : ℕ)
    (hh : RoundedCodeHandle.run th (RoundedCodeHandle.start kind d.stk) = e)
    (he : e.l = none) :
    ∃ t ≤ ta + th + RoundedCodeReset.clock e.stk + 2,
      run t (adminCfg c) = ⟨none, finalControl false, RoundedCodeReset.resetBank e.stk⟩ := by
  obtain ⟨a, hat, har⟩ := admin_to_route c d ta ha hd
  have hr := route_success d.var d.stk kind hk
  obtain ⟨h, hht, hhr⟩ := handle_to_cleanup kind (RoundedCodeHandle.start kind d.stk) e th hh he
  obtain ⟨r, hrt, hrr⟩ := cleanup_to_end (handleLift kind e.var).1 e.stk
  refine ⟨a + 1 + h + r, by omega, ?_⟩
  exact (join_run ((join_run ((join_run har 1).trans hr) h).trans hhr) r).trans hrr

#print axioms cleanup_to_end
#print axioms compose_success

end
end EthInapproximability.CurrentPaper.RoundedCodeStep
