import CurrentAdditive.TrialSearchCombinedSimulation

/-! A run-level lifting theorem for an embedded physical phase. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSimulation

variable {K L V : Type*} [DecidableEq K]

def phaseRel (stack : K → Fin 12) (label : L → Label) (next : Label)
    (put : Registers → V → Registers) (finish : Registers → Registers)
    (base : Registers) (initialStacks : Fin 12 → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (g : Config) : Prop :=
  g.l = carriedLabel label next c.l ∧
  g.var = (if c.l.isNone then finish (put base c.var) else put base c.var) ∧
  (∀ k, g.stk (stack k) = c.stk k) ∧
  (∀ m, (∀ k, stack k ≠ m) → g.stk m = initialStacks m)

omit [DecidableEq K] in
theorem phaseRel_initial
    (stack : K → Fin 12) (label : L → Label) (next : Label)
    (get : Registers → V) (put : Registers → V → Registers)
    (finish : Registers → Registers)
    (hself : ∀ r, put r (get r) = r)
    (base : Registers) (S : Fin 12 → List Bool) (l : L) :
    phaseRel stack label next put finish base S
      ⟨some l, get base, fun k => S (stack k)⟩
      ⟨some (label l), base, S⟩ := by
  simp [phaseRel, carriedLabel, hself]

theorem phaseRel_step
    (stack : K → Fin 12) (hinj : Function.Injective stack)
    (label : L → Label) (next : Label)
    (get : Registers → V) (put : Registers → V → Registers)
    (finish : Registers → Registers)
    (hput : ∀ r v, get (put r v) = v)
    (hputput : ∀ r v w, put (put r v) w = put r w)
    (hself : ∀ r, put r (get r) = r)
    (hfinish : ∀ r, get (finish r) = get r)
    (Plocal : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Pglobal : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Registers)
    (hprogram : ∀ l, Pglobal (label l) =
      embedStmt stack label next get put finish (Plocal l))
    (base : Registers) (initialStacks : Fin 12 → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (g : Config)
    (hactive : c.l ≠ none)
    (hrel : phaseRel stack label next put finish base initialStacks c g) :
    phaseRel stack label next put finish base initialStacks
      (advance Plocal c) (advance Pglobal g) := by
  rcases c with ⟨l, v, T⟩
  cases l with
  | none => exact (hactive rfl).elim
  | some l =>
    rcases g with ⟨gl, gr, S⟩
    rcases hrel with ⟨hl, hv, hs, hf⟩
    have hvar : gr = put base v := by simpa using hv
    have hget : get gr = v := by
      rw [hvar]
      exact hput base v
    have hstacks : (fun k => S (stack k)) = T := by
      funext k
      exact hs k
    have hstep := embed_stepAux_project stack hinj label next get put finish
      hput hfinish (Plocal l) gr S
    have hreg := embed_stepAux_register stack hinj label next get put finish
      hput hputput hself (Plocal l) gr S
    simp only [hget, hstacks] at hstep hreg
    have hglobalLabel : gl = some (label l) := hl
    subst gl
    simp only [advance, TM2.step, hprogram,
      Option.getD_some] at hstep hreg ⊢
    rcases hstep with ⟨hl', hv', hs', hf'⟩
    refine ⟨hl', ?_, hs', ?_⟩
    · rw [hreg, hvar, hputput]
    · intro m hm
      rw [hf' m hm]
      exact hf m hm

theorem phaseRel_run
    (stack : K → Fin 12) (hinj : Function.Injective stack)
    (label : L → Label) (next : Label)
    (get : Registers → V) (put : Registers → V → Registers)
    (finish : Registers → Registers)
    (hput : ∀ r v, get (put r v) = v)
    (hputput : ∀ r v w, put (put r v) w = put r w)
    (hself : ∀ r, put r (get r) = r)
    (hfinish : ∀ r, get (finish r) = get r)
    (Plocal : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Pglobal : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Registers)
    (hprogram : ∀ l, Pglobal (label l) =
      embedStmt stack label next get put finish (Plocal l))
    (base : Registers) (initialStacks : Fin 12 → List Bool)
    (l : L) (n : Nat)
    (hactive : ∀ k < n,
      (((advance Plocal)^[k])
        (⟨some l, get base, fun k => initialStacks (stack k)⟩ :
          TM2.Cfg (fun _ : K => Bool) L V)).l ≠ none) :
    phaseRel stack label next put finish base initialStacks
      (((advance Plocal)^[n])
        (⟨some l, get base, fun k => initialStacks (stack k)⟩ :
          TM2.Cfg (fun _ : K => Bool) L V))
      (((advance Pglobal)^[n])
        (⟨some (label l), base, initialStacks⟩ : Config)) := by
  induction n with
  | zero => exact phaseRel_initial stack label next get put finish hself base initialStacks l
  | succ n ih =>
    have hr := ih (fun k hk => hactive k (by omega))
    have ha := hactive n (by omega)
    simpa only [Function.iterate_succ_apply'] using
      phaseRel_step stack hinj label next get put finish
        hput hputput hself hfinish Plocal Pglobal hprogram base initialStacks
        _ _ ha hr

#print axioms phaseRel_run

theorem halted_run_stutters
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V)
    (t n : Nat) (ht : t ≤ n)
    (hhalt : (((advance P)^[t]) c).l = none) :
    ((advance P)^[n]) c = ((advance P)^[t]) c := by
  let stopped := ((advance P)^[t]) c
  have hfix : advance P stopped = stopped := by
    change stopped.l = none at hhalt
    rcases stopped with ⟨l, v, S⟩
    cases l with
    | none => rfl
    | some l => cases hhalt
  have hiter (j : Nat) : ((advance P)^[j]) stopped = stopped := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hn : n = (n - t) + t := by omega
  rw [hn]
  simp only [Function.iterate_add_apply]
  exact hiter (n - t)

theorem firstHaltWithin
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (n : Nat)
    (hhalt : (((advance P)^[n]) c).l = none) :
    ∃ t ≤ n,
      (((advance P)^[t]) c).l = none ∧
      (∀ k < t, (((advance P)^[k]) c).l ≠ none) ∧
      ((advance P)^[t]) c = ((advance P)^[n]) c := by
  let p : Nat → Prop := fun t => (((advance P)^[t]) c).l = none
  let t := Nat.find (show ∃ t, p t from ⟨n, hhalt⟩)
  have ht : p t := Nat.find_spec _
  have hle : t ≤ n := Nat.find_min' _ hhalt
  refine ⟨t, hle, ht, ?_, ?_⟩
  · intro k hk hcontr
    exact Nat.find_min (show ∃ t, p t from ⟨n, hhalt⟩) hk hcontr
  · exact (halted_run_stutters P c t n hle ht).symm

#print axioms firstHaltWithin

theorem phaseRel_halts_within
    (stack : K → Fin 12) (hinj : Function.Injective stack)
    (label : L → Label) (next : Label)
    (get : Registers → V) (put : Registers → V → Registers)
    (finish : Registers → Registers)
    (hput : ∀ r v, get (put r v) = v)
    (hputput : ∀ r v w, put (put r v) w = put r w)
    (hself : ∀ r, put r (get r) = r)
    (hfinish : ∀ r, get (finish r) = get r)
    (Plocal : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Pglobal : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Registers)
    (hprogram : ∀ l, Pglobal (label l) =
      embedStmt stack label next get put finish (Plocal l))
    (base : Registers) (S : Fin 12 → List Bool) (l : L) (n : Nat)
    (hhalt : ((((advance Plocal)^[n])
      (⟨some l, get base, fun k => S (stack k)⟩ :
        TM2.Cfg (fun _ : K => Bool) L V)).l = none)) :
    ∃ t ≤ n,
      phaseRel stack label next put finish base S
        (((advance Plocal)^[n])
          (⟨some l, get base, fun k => S (stack k)⟩ :
            TM2.Cfg (fun _ : K => Bool) L V))
        (((advance Pglobal)^[t])
          (⟨some (label l), base, S⟩ : Config)) := by
  obtain ⟨t, ht, hstop, hactive, heq⟩ :=
    firstHaltWithin Plocal
      (⟨some l, get base, fun k => S (stack k)⟩ :
        TM2.Cfg (fun _ : K => Bool) L V) n hhalt
  refine ⟨t, ht, ?_⟩
  rw [← heq]
  exact phaseRel_run stack hinj label next get put finish
    hput hputput hself hfinish Plocal Pglobal hprogram
    base S l t hactive

#print axioms phaseRel_halts_within

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun
