import CurrentAdditive.TrialSearchCombinedMachine

/-!
Instruction-level simulation for embedding a physical Boolean-stack program
into the twelve shared stacks. It keeps each local stack exact and proves
that stacks outside the embedded bank are untouched. This is the reusable
step needed to transfer the already checked preparation/division/zero and
controller run theorems to the combined program.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSimulation

open Turing
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine

variable {K L V : Type*} [DecidableEq K]

def carriedLabel (label : L → Label) (next : Label) : Option L → Option Label
  | none => some next
  | some l => some (label l)

theorem project_update (stack : K → Fin 12) (hinj : Function.Injective stack)
    (S : Fin 12 → List Bool) (k : K) (bits : List Bool) :
    (fun j => (Function.update S (stack k) bits) (stack j)) =
      Function.update (fun j => S (stack j)) k bits := by
  funext j
  by_cases h : j = k
  · subst j; simp
  · have hs : stack j ≠ stack k := by
      intro heq
      exact h (hinj heq)
    simp [h, hs]

theorem embed_stepAux_project
    (stack : K → Fin 12) (hinj : Function.Injective stack)
    (label : L → Label) (next : Label)
    (get : Registers → V) (put : Registers → V → Registers)
    (finish : Registers → Registers)
    (hput : ∀ r v, get (put r v) = v)
    (hfinish : ∀ r, get (finish r) = get r)
    (q : TM2.Stmt (fun _ : K => Bool) L V)
    (r : Registers) (S : Fin 12 → List Bool) :
    let c := TM2.stepAux q (get r) (fun k => S (stack k))
    let g := TM2.stepAux (embedStmt stack label next get put finish q) r S
    g.l = carriedLabel label next c.l ∧
      get g.var = c.var ∧
      (∀ k, g.stk (stack k) = c.stk k) ∧
      (∀ m, (∀ k, stack k ≠ m) → g.stk m = S m) := by
  induction q generalizing r S with
  | push k f q ih =>
    have hi := ih r (Function.update S (stack k) (f (get r) :: S (stack k)))
    simp only [embedStmt, TM2.stepAux, project_update stack hinj] at hi ⊢
    rcases hi with ⟨hl, hv, hs, hf⟩
    refine ⟨hl, hv, hs, ?_⟩
    intro m hm
    rw [hf m hm]
    simp [Ne.symm (hm k)]
  | peek k f q ih =>
    simpa only [embedStmt, TM2.stepAux, hput] using
      ih (put r (f (get r) (S (stack k)).head?)) S
  | pop k f q ih =>
    have hi := ih (put r (f (get r) (S (stack k)).head?))
      (Function.update S (stack k) (S (stack k)).tail)
    simp only [embedStmt, TM2.stepAux, hput,
      project_update stack hinj] at hi ⊢
    rcases hi with ⟨hl, hv, hs, hf⟩
    refine ⟨hl, hv, hs, ?_⟩
    intro m hm
    rw [hf m hm]
    simp [Ne.symm (hm k)]
  | load f q ih =>
    simpa only [embedStmt, TM2.stepAux, hput] using
      ih (put r (f (get r))) S
  | branch f q s ihq ihs =>
    cases hf : f (get r) <;>
      simp only [embedStmt, TM2.stepAux, hf, cond_false, cond_true] <;>
      first | exact ihs r S | exact ihq r S
  | goto f =>
    simp [embedStmt, TM2.stepAux, carriedLabel]
  | halt =>
    simp [embedStmt, TM2.stepAux, carriedLabel, hfinish]

#print axioms embed_stepAux_project

theorem embed_stepAux_register
    (stack : K → Fin 12) (hinj : Function.Injective stack)
    (label : L → Label) (next : Label)
    (get : Registers → V) (put : Registers → V → Registers)
    (finish : Registers → Registers)
    (hput : ∀ r v, get (put r v) = v)
    (hputput : ∀ r v w, put (put r v) w = put r w)
    (hputself : ∀ r, put r (get r) = r)
    (q : TM2.Stmt (fun _ : K => Bool) L V)
    (r : Registers) (S : Fin 12 → List Bool) :
    let c := TM2.stepAux q (get r) (fun k => S (stack k))
    let g := TM2.stepAux (embedStmt stack label next get put finish q) r S
    g.var = if c.l.isNone then finish (put r c.var) else put r c.var := by
  induction q generalizing r S with
  | push k f q ih =>
    simpa only [embedStmt, TM2.stepAux, project_update stack hinj]
      using ih r (Function.update S (stack k) (f (get r) :: S (stack k)))
  | peek k f q ih =>
    simpa only [embedStmt, TM2.stepAux, hput, hputput] using
      ih (put r (f (get r) (S (stack k)).head?)) S
  | pop k f q ih =>
    simpa only [embedStmt, TM2.stepAux, hput, hputput,
      project_update stack hinj] using
      ih (put r (f (get r) (S (stack k)).head?))
        (Function.update S (stack k) (S (stack k)).tail)
  | load f q ih =>
    simpa only [embedStmt, TM2.stepAux, hput, hputput] using
      ih (put r (f (get r))) S
  | branch f q s ihq ihs =>
    cases hf : f (get r) <;>
      simp only [embedStmt, TM2.stepAux, hf, cond_false, cond_true] <;>
      first | exact ihs r S | exact ihq r S
  | goto f =>
    simp [embedStmt, TM2.stepAux, hputself]
  | halt =>
    simp [embedStmt, TM2.stepAux, hputself]

#print axioms embed_stepAux_register

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSimulation
