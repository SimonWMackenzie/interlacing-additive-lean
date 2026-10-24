import CurrentAdditive.TrialSearchCombinedRun

/-! Run lifting for the outer controller until a callback or terminal label. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterLift

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSimulation
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun

namespace Outer
export CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine
  (Label Config program run)
end Outer

def boundary : Outer.Label → Prop
  | .test | .success | .exhausted => True
  | _ => False

theorem boundary_advance_halts (c : Outer.Config)
    (h : ∃ l, c.l = some l ∧ boundary l) :
    (advance Outer.program c).l = none := by
  obtain ⟨l, hl, hb⟩ := h
  rcases c with ⟨cl, v, s⟩
  change cl = some l at hl
  subst cl
  cases l <;> simp [boundary] at hb <;>
    simp [advance, TM2.step, Outer.program, TM2.stepAux]

theorem boundary_only_at_end (q : Outer.Config) (n : Nat)
    (hfinal : ∃ l, (Outer.run n q).l = some l ∧ boundary l) :
    ∀ k < n, ¬ ∃ l, (Outer.run k q).l = some l ∧ boundary l := by
  intro k hk hbad
  have hnext : (Outer.run (k + 1) q).l = none := by
    simpa [Outer.run, Function.iterate_succ_apply'] using
      boundary_advance_halts (Outer.run k q) hbad
  have hstop := halted_run_stutters Outer.program q (k + 1) n (by omega) hnext
  obtain ⟨l, hl, _⟩ := hfinal
  have : (Outer.run n q).l = none := by
    rw [Outer.run, hstop]
    exact hnext
  rw [hl] at this
  cases this

theorem outer_program_agrees (l : Outer.Label) (h : ¬ boundary l) :
    program (.outer l) =
      embedStmt id Label.outer (.prep .shiftScan)
        (fun r => r.outer) (fun r v => {r with outer := v})
        (fun r => {r with prep := none}) (Outer.program l) := by
  cases l <;> simp [boundary] at h <;> rfl

theorem outer_step_rel
    (base : Registers) (S : Fin 12 → List Bool)
    (c : Outer.Config) (g : Config)
    (hl : ∃ l, c.l = some l ∧ ¬ boundary l)
    (hrel : phaseRel id Label.outer (.prep .shiftScan)
      (fun r v => {r with outer := v}) (fun r => {r with prep := none})
      base S c g) :
    phaseRel id Label.outer (.prep .shiftScan)
      (fun r v => {r with outer := v}) (fun r => {r with prep := none})
      base S (advance Outer.program c) (advance program g) := by
  obtain ⟨l, hc, hb⟩ := hl
  rcases c with ⟨cl, v, T⟩
  change cl = some l at hc
  subst cl
  rcases g with ⟨gl, gr, G⟩
  rcases hrel with ⟨hlabel, hvar, hs, hf⟩
  have hreg : gr = {base with outer := v} := by simpa using hvar
  have hget : gr.outer = v := by rw [hreg]
  have hstacks : G = T := by
    funext k
    exact hs k
  subst G
  have hstep := embed_stepAux_project id (by intro a b h; exact h)
    Label.outer (.prep .shiftScan) (fun r => r.outer)
    (fun r v => {r with outer := v}) (fun r => {r with prep := none})
    (by intros; rfl) (by intros; rfl) (Outer.program l) gr T
  have hregister := embed_stepAux_register id (by intro a b h; exact h)
    Label.outer (.prep .shiftScan) (fun r => r.outer)
    (fun r v => {r with outer := v}) (fun r => {r with prep := none})
    (by intros; rfl) (by intros; rfl) (by intro r; cases r; rfl)
    (Outer.program l) gr T
  simp only [hget] at hstep hregister
  have hglobalLabel : gl = some (.outer l) := hlabel
  subst gl
  simp only [advance, TM2.step, outer_program_agrees l hb,
    Option.getD_some] at hstep hregister ⊢
  rcases hstep with ⟨hl', hv', hs', hf'⟩
  refine ⟨hl', ?_, hs', ?_⟩
  · rw [hregister, hreg]
    rfl
  · intro m hm
    rw [hf' m hm]
    exact hf m hm

theorem active_before_boundary (q : Outer.Config) (n : Nat)
    (hfinal : ∃ l, (Outer.run n q).l = some l ∧ boundary l) :
    ∀ k < n, (Outer.run k q).l ≠ none := by
  intro k hk hstop
  have hstay := halted_run_stutters Outer.program q k n (by omega) hstop
  obtain ⟨l, hl, _⟩ := hfinal
  have : (Outer.run n q).l = none := by
    rw [Outer.run, hstay]
    exact hstop
  rw [hl] at this
  cases this

theorem outer_run_rel
    (base : Registers) (S : Fin 12 → List Bool)
    (start : Outer.Label) (n : Nat)
    (hactive : ∀ k < n,
      (Outer.run k ⟨some start, base.outer, S⟩).l ≠ none)
    (hnoBoundary : ∀ k < n,
      ¬ ∃ l, (Outer.run k ⟨some start, base.outer, S⟩).l = some l ∧ boundary l) :
    phaseRel id Label.outer (.prep .shiftScan)
      (fun r v => {r with outer := v}) (fun r => {r with prep := none})
      base S (Outer.run n ⟨some start, base.outer, S⟩)
      (run n ⟨some (.outer start), base, S⟩) := by
  induction n with
  | zero =>
    exact phaseRel_initial id Label.outer (.prep .shiftScan)
      (fun r => r.outer) (fun r v => {r with outer := v})
      (fun r => {r with prep := none}) (by intro r; cases r; rfl)
      base S start
  | succ n ih =>
    have hr := ih (fun k hk => hactive k (by omega))
      (fun k hk => hnoBoundary k (by omega))
    have hnactive := hactive n (by omega)
    obtain ⟨l, hl⟩ : ∃ l, (Outer.run n ⟨some start, base.outer, S⟩).l = some l := by
      cases h : (Outer.run n ⟨some start, base.outer, S⟩).l with
      | none => exact (hnactive h).elim
      | some l => exact ⟨l, rfl⟩
    have hnb : ¬ boundary l := by
      intro hb
      exact hnoBoundary n (by omega) ⟨l, hl, hb⟩
    have hstep := outer_step_rel base S
      (Outer.run n ⟨some start, base.outer, S⟩)
      (run n ⟨some (.outer start), base, S⟩)
      ⟨l, hl, hnb⟩ hr
    simpa [Outer.run, run, Function.iterate_succ_apply'] using hstep

theorem outer_run_to_boundary
    (base : Registers) (S : Fin 12 → List Bool)
    (start : Outer.Label) (n : Nat)
    (hfinal : ∃ l,
      (Outer.run n ⟨some start, base.outer, S⟩).l = some l ∧ boundary l) :
    phaseRel id Label.outer (.prep .shiftScan)
      (fun r v => {r with outer := v}) (fun r => {r with prep := none})
      base S (Outer.run n ⟨some start, base.outer, S⟩)
      (run n ⟨some (.outer start), base, S⟩) := by
  apply outer_run_rel base S start n
  · exact active_before_boundary _ n hfinal
  · exact boundary_only_at_end _ n hfinal

#print axioms outer_run_to_boundary

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterLift
