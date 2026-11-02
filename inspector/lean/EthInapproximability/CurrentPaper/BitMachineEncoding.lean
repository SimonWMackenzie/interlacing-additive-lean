import EthInapproximability.CurrentPaper.BitMachine

/-!
# Finite relabelling of Boolean-stack programs

Source: v8 `06-eth.tex`, fixed bit-machine convention. This is an operational
change of finite names, not a new unit-cost instruction. It lets explicit
programs use finite inductive labels and registers while the final machine
interface uses finite ordinals.
-/

namespace EthInapproximability.CurrentPaper.BitMachineEncoding

open Turing
open EthInapproximability.CurrentPaper.BitMachine

variable {K K' Λ Λ' σ σ' : Type*}

def renameStmt (ek : K ≃ K') (el : Λ ≃ Λ') (ev : σ ≃ σ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K' => Bool) Λ' σ'
  | .push k f q => .push (ek k) (fun v => f (ev.symm v)) (renameStmt ek el ev q)
  | .peek k f q => .peek (ek k) (fun v b => ev (f (ev.symm v) b)) (renameStmt ek el ev q)
  | .pop k f q => .pop (ek k) (fun v b => ev (f (ev.symm v) b)) (renameStmt ek el ev q)
  | .load f q => .load (fun v => ev (f (ev.symm v))) (renameStmt ek el ev q)
  | .branch f q r => .branch (fun v => f (ev.symm v))
      (renameStmt ek el ev q) (renameStmt ek el ev r)
  | .goto f => .goto (fun v => el (f (ev.symm v)))
  | .halt => .halt

def renameCfg (ek : K ≃ K') (el : Λ ≃ Λ') (ev : σ ≃ σ')
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) : TM2.Cfg (fun _ : K' => Bool) Λ' σ' :=
  ⟨c.l.map el, ev c.var, fun k => c.stk (ek.symm k)⟩

theorem rename_update [DecidableEq K] [DecidableEq K'] (ek : K ≃ K')
    (S : K → List Bool) (k : K) (bits : List Bool) :
    (fun j => (Function.update S k bits) (ek.symm j)) =
      Function.update (fun j => S (ek.symm j)) (ek k) bits := by
  funext j
  by_cases hj : j = ek k
  · subst j
    rw [Function.update_self]
    rw [show ek.symm (ek k) = k from ek.symm_apply_apply k]
    exact Function.update_self k bits S
  · have hk : ek.symm j ≠ k := by intro h; apply hj; rw [← h]; simp
    simp [hj, hk]

theorem rename_stepAux [DecidableEq K] [DecidableEq K']
    (ek : K ≃ K') (el : Λ ≃ Λ') (ev : σ ≃ σ')
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (S : K → List Bool) :
    TM2.stepAux (renameStmt ek el ev q) (ev v) (fun k => S (ek.symm k)) =
      renameCfg ek el ev (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [renameStmt, TM2.stepAux, Equiv.symm_apply_apply]
      rw [← rename_update]
      exact ih _ _
  | peek k f q ih => simpa only [renameStmt, TM2.stepAux, Equiv.symm_apply_apply] using ih _ _
  | pop k f q ih =>
      simp only [renameStmt, TM2.stepAux, Equiv.symm_apply_apply]
      rw [← rename_update]
      exact ih _ _
  | load f q ih => simpa only [renameStmt, TM2.stepAux, Equiv.symm_apply_apply] using ih _ _
  | branch f q r ihq ihr =>
      cases h : f v <;> simp [renameStmt, TM2.stepAux, h, ihq, ihr]
  | goto f => simp [renameStmt, TM2.stepAux, renameCfg]
  | halt => simp [renameStmt, TM2.stepAux, renameCfg]

def advance [DecidableEq K] (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) := (TM2.step P c).getD c

theorem rename_advance [DecidableEq K] [DecidableEq K']
    (ek : K ≃ K') (el : Λ ≃ Λ') (ev : σ ≃ σ')
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    advance (fun l => renameStmt ek el ev (P (el.symm l))) (renameCfg ek el ev c) =
      renameCfg ek el ev (advance P c) := by
  cases c with
  | mk l v S =>
      cases l with
      | none => rfl
      | some l =>
          simpa only [advance, renameCfg, Option.map_some, TM2.step,
            Option.getD_some, Equiv.symm_apply_apply] using rename_stepAux ek el ev (P l) v S

theorem rename_run [DecidableEq K] [DecidableEq K']
    (ek : K ≃ K') (el : Λ ≃ Λ') (ev : σ ≃ σ')
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (n : ℕ) :
    ((advance (fun l => renameStmt ek el ev (P (el.symm l))))^[n]) (renameCfg ek el ev c) =
      renameCfg ek el ev (((advance P)^[n]) c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, rename_advance]

noncomputable def ofFinite [Fintype K] [Fintype Λ] [Fintype σ]
    (input output : K) (start : Λ) (initial : σ)
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Machine where
  stackCount := Fintype.card K
  labelCount := Fintype.card Λ
  controlCount := Fintype.card σ
  input := Fintype.equivFin K input
  output := Fintype.equivFin K output
  start := Fintype.equivFin Λ start
  initial := Fintype.equivFin σ initial
  program := fun l => renameStmt (Fintype.equivFin K) (Fintype.equivFin Λ)
    (Fintype.equivFin σ) (P ((Fintype.equivFin Λ).symm l))

theorem ofFinite_run [Fintype K] [Fintype Λ] [Fintype σ] [DecidableEq K]
    (input output : K) (start : Λ) (initial : σ)
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (n : ℕ) :
    (ofFinite input output start initial P).run n
      (renameCfg (Fintype.equivFin K) (Fintype.equivFin Λ) (Fintype.equivFin σ) c) =
    renameCfg (Fintype.equivFin K) (Fintype.equivFin Λ) (Fintype.equivFin σ)
      (((advance P)^[n]) c) := by
  exact rename_run _ _ _ P c n

def rawInit [DecidableEq K] (input : K) (start : Λ) (initial : σ)
    (bits : List Bool) : TM2.Cfg (fun _ : K => Bool) Λ σ :=
  ⟨some start, initial, fun k => if k = input then bits else []⟩

theorem ofFinite_init [Fintype K] [Fintype Λ] [Fintype σ] [DecidableEq K]
    (input output : K) (start : Λ) (initial : σ)
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (bits : List Bool) :
    (ofFinite input output start initial P).init bits =
      renameCfg (Fintype.equivFin K) (Fintype.equivFin Λ) (Fintype.equivFin σ)
        (rawInit input start initial bits) := by
  simp only [Machine.init, ofFinite, renameCfg, rawInit, Option.map_some]
  congr 1
  funext k
  have hk : k = Fintype.equivFin K input ↔ (Fintype.equivFin K).symm k = input := by
    constructor
    · intro h; rw [h]; exact Equiv.symm_apply_apply _ _
    · intro h; rw [← h]; exact (Equiv.apply_symm_apply _ _).symm
  simp only [hk]

/-- A runtime proof for the literal finite-label program transports with
exactly the same transition count, not an unspecified simulation overhead. -/
theorem outputsWithin_of_raw_run [Fintype K] [Fintype Λ] [Fintype σ] [DecidableEq K]
    (input output : K) (start : Λ) (initial : σ)
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (bits result : List Bool) (n time : ℕ) (hn : n ≤ time)
    (hhalt : (((advance P)^[n]) (rawInit input start initial bits)).l = none)
    (hout : (((advance P)^[n]) (rawInit input start initial bits)).stk output = result) :
    (ofFinite input output start initial P).OutputsWithin bits result time := by
  let M := ofFinite input output start initial P
  have hi := ofFinite_init input output start initial P bits
  have hr := ofFinite_run input output start initial P (rawInit input start initial bits) n
  have hrun := (congrArg (M.run n) hi).trans hr
  refine ⟨n, hn, ?_, ?_⟩
  · simpa only [renameCfg, hhalt, Option.map_none] using congrArg (fun c => c.l) hrun
  · have hh := congrArg (fun c => c.stk M.output) hrun
    simpa only [renameCfg, M, ofFinite, Equiv.symm_apply_apply, hout] using hh

end EthInapproximability.CurrentPaper.BitMachineEncoding
