import CurrentAdditive.RoundedCodeReadback

/-! Physical administrative normalization and rounded draw dispatch. This
module reuses only the literal parser/administrative Code machine. It does
not call the old source generator or rejection sampler. -/

namespace EthInapproximability.CurrentPaper.RoundedCodeAdmin

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize
noncomputable section

abbrev Stack := RoundedCodeDraw.Stack
abbrev AdminControl := Paper2.CodeAdminMachine.Control
abbrev DrawControl := RoundedCodeDraw.Control
abbrev Control := AdminControl × DrawControl

def adminInitial : AdminControl := ((none, none), none)
def initial : Control := (adminInitial, RoundedLoadedDraw.initial)

inductive Label where
  | admin (l : Paper2.CodeAdminMachine.Label)
  | route
  | draw (kind : Paper2.CodeHeaderMachine.Kind) (l : RoundedCodeDraw.Label)
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def adminEmbed : Paper2.CodeAdminMachine.Stack ↪ Stack :=
  ⟨fun k => .inl (.inr k), by
    intro i j h; exact Sum.inr_injective (Sum.inl_injective h)⟩

def kindControl (kind : Paper2.CodeHeaderMachine.Kind) : AdminControl :=
  ((none, some kind), none)

def drawStart : RoundedCodeDraw.Label :=
  BitMachineRawSequence.leftLabel (.copy .fuel .scan)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .admin l => stmt adminEmbed Label.admin
      (fun v => (v, RoundedLoadedDraw.initial)) Prod.fst (some .route)
      (Paper2.CodeAdminMachine.program l)
  | .route =>
      branch (fun v => v.1.1.2.isSome)
        (branch (fun v => decide (v.1.1.2 = some .bit))
          (push (.inl RoundedCodeDraw.oldAlphabet) (fun _ => true)
            (push (.inl RoundedCodeDraw.oldAlphabet) (fun _ => true)
              (load (fun _ => (kindControl .bit, RoundedLoadedDraw.initial))
                (goto (fun _ => .draw .bit drawStart)))))
          (load (fun v => (kindControl (v.1.1.2.getD .ticket), RoundedLoadedDraw.initial))
            (goto (fun v => .draw (v.1.1.2.getD .ticket) drawStart))))
        halt
  | .draw kind l => BitMachineInline.stmt (Label.draw kind)
      (fun v => (kindControl kind, v)) Prod.snd none (RoundedCodeDraw.program l)

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def oldForeign (bits : List Bool) (b : ℕ) : RoundedCodeDraw.OldStack → List Bool :=
  Sum.elim (Paper2.DrawParameterLoader.initialBank bits 0 b 0) (fun _ => [])

def foreign (bits : List Bool) (b : ℕ) : Stack → List Bool :=
  RoundedCodeDraw.inputBank (oldForeign bits b)

def start (s : State) (bits : List Bool) (b : ℕ) : Config :=
  cfg adminEmbed (foreign bits b) Label.admin
    (fun v => (v, RoundedLoadedDraw.initial)) (some .route)
      (Paper2.CodeAdminNormalization.stateCfg s)

def readyOldBank (s : State) (bits : List Bool) (b : ℕ) :
    RoundedCodeDraw.OldStack → List Bool :=
  Sum.elim (Paper2.DrawParameterLoader.initialBank bits 0 b 0)
    (Paper2.CodeAdminReady.stopped s).stk

def ready (s : State) (bits : List Bool) (b : ℕ) : Config :=
  ⟨some .route, ((Paper2.CodeAdminReady.stopped s).var, RoundedLoadedDraw.initial),
    RoundedCodeDraw.inputBank (readyOldBank s bits b)⟩

theorem admin_bank (s : State) (bits : List Bool) (b : ℕ) :
    bank adminEmbed (foreign bits b) (Paper2.CodeAdminReady.stopped s).stk =
      RoundedCodeDraw.inputBank (readyOldBank s bits b) := by
  funext k
  rcases k with (k | k)
  · rcases k with (k | k)
    · rw [bank_outside]
      · rfl
      · rintro ⟨j, h⟩
        cases h
    · change bank adminEmbed _ _ (adminEmbed k) = _
      rw [bank_at]
      rfl
  · rw [bank_outside]
    · rfl
    · rintro ⟨j, h⟩
      cases h

theorem normalize_run (root : Code) (s : State) (hp : PositiveState s)
    (ht : Trace root s) (bits : List Bool) (b : ℕ) :
    ∃ t ≤ 13 * (codeSize root + 3) ^ 2,
      run t (start s bits b) = ready (Paper2.GeneratorCode.normalize s) bits b := by
  obtain ⟨t, htime, hr⟩ := Paper2.CodeAdminReady.physical_ready_trace root s hp ht
  have hh : (((advance Paper2.CodeAdminMachine.program)^[t])
      (Paper2.CodeAdminNormalization.stateCfg s)).l = none := by
    rw [hr]
    exact Paper2.CodeAdminReady.stopped_halted _
  obtain ⟨u, hu, hur⟩ := outputs adminEmbed (foreign bits b) Label.admin
    (fun v => (v, RoundedLoadedDraw.initial)) Prod.fst (by intro v; rfl)
    (some .route) Paper2.CodeAdminMachine.program program (by intro l; rfl)
    (Paper2.CodeAdminNormalization.stateCfg s) t hh
  rw [hr] at hur
  refine ⟨u, hu.trans htime, ?_⟩
  change run u (start s bits b) = _ at hur
  simpa only [cfg, stackCfg, BitMachineInline.cfg,
    Paper2.CodeAdminReady.stopped_halted, admin_bank, ready] using hur

def drawCfg (kind : Paper2.CodeHeaderMachine.Kind) (S : RoundedCodeDraw.OldStack → List Bool) :
    Config := ⟨some (.draw kind drawStart), (kindControl kind, RoundedLoadedDraw.initial),
      RoundedCodeDraw.inputBank S⟩

theorem draw_run (kind : Paper2.CodeHeaderMachine.Kind)
    (S : RoundedCodeDraw.OldStack → List Bool) (a b : ℕ) (ha : 0 < a)
    (bits : Fin b → Bool) (suffix : List Bool)
    (hA : S RoundedCodeDraw.oldAlphabet = List.replicate a true)
    (hB : S RoundedCodeDraw.oldWidth = List.replicate b true)
    (hT : S RoundedCodeDraw.oldTape = Paper2.CappedTicketMachine.ticketWord bits ++ suffix)
    (hO : S RoundedCodeDraw.oldResult = []) :
    ∃ t ≤ RoundedLoadedClock.coefficient * (a + b + 2) ^ 2,
      run t (drawCfg kind S) =
        ⟨none, (kindControl kind, RoundedLoadedDraw.initial),
          RoundedCodeDraw.resultBank S a b
            (Paper2.CappedTicketMachine.ticketWord bits ++ suffix) suffix
            ((Paper2.RecursiveLabelCodecScratch.finCodec a).encode
              (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
                (Paper2.CappedSampler.bitsTicketEquiv b bits)))⟩ := by
  obtain ⟨t, htime, hr⟩ := RoundedCodeDraw.physical_finCodec S a b ha bits suffix hA hB hT hO
  have hh : (((advance RoundedCodeDraw.program)^[t]) (RoundedCodeDraw.start S)).l = none := by
    change (RoundedCodeDraw.run t _).l = none
    rw [hr]
  obtain ⟨u, hu, hur⟩ := BitMachineInline.outputs (Label.draw kind)
    (fun v => (kindControl kind, v)) Prod.snd (by intro v; rfl) none
    RoundedCodeDraw.program program (by intro l; rfl) (RoundedCodeDraw.start S) t hh
  change ((advance RoundedCodeDraw.program)^[t]) _ = _ at hr
  rw [hr] at hur
  exact ⟨u, hu.trans htime, hur⟩

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem route_ticket (a : ℕ) (cs : List Code) (out bits : List Bool) (b : ℕ) :
    run 1 (ready ⟨.ticket a :: cs, out⟩ bits b) =
      drawCfg .ticket (readyOldBank ⟨.ticket a :: cs, out⟩ bits b) := by
  simp [run, ready, drawCfg, program, BitMachineEncoding.advance, TM2.step, TM2.stepAux,
    Paper2.CodeAdminReady.stopped, Paper2.CodeAdminMachine.cfg,
    Paper2.CodeHeaderMachine.headerKind, kindControl, drawStart]

theorem route_branch (a firstCut secondCut : ℕ) (first second third : Code)
    (cs : List Code) (out bits : List Bool) (b : ℕ) :
    run 1 (ready ⟨.branch3 a firstCut secondCut first second third :: cs, out⟩ bits b) =
      drawCfg .branch3 (readyOldBank
        ⟨.branch3 a firstCut secondCut first second third :: cs, out⟩ bits b) := by
  simp [run, ready, drawCfg, program, BitMachineEncoding.advance, TM2.step, TM2.stepAux,
    Paper2.CodeAdminReady.stopped, Paper2.CodeAdminMachine.cfg,
    Paper2.CodeHeaderMachine.headerKind, kindControl, drawStart]

#print axioms normalize_run
#print axioms draw_run

end
end EthInapproximability.CurrentPaper.RoundedCodeAdmin
