import EthInapproximability.CurrentPaper.MatrixStage4PayloadRead
import EthInapproximability.CurrentPaper.MatrixStage4ActiveRankMachine
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical vector bit and active rank from one literal table

The fixed controller first reads `vectors i α` from the literal row-major
table, preserving `i`, `α`, `q`, and the table; then it reuses those same
banks for the active-rank scan. The bit and rank remain in output stacks.
No duplicated coordinate, free accessor, or control-value oracle is used.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4VectorFlagRank

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 17
abbrev Label := MatrixTableLookup.Label ⊕
  (MatrixStage4ActiveRankMachine.Label ⊕ Unit)
abbrev Control := MatrixTableLookup.Control ×
  MatrixStage4ActiveRankMachine.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def lookupStart : Label := .inl MatrixTableLookup.start
def rankStart : Label := .inr (.inl MatrixStage4ActiveRankMachine.gatherStart)
def done : Label := .inr (.inr ())

def lookupStacks : Fin 10 ⊕ Fin 7 ≃ Stack := finSumFinEquiv

def rankPermutation : Stack ≃ Stack where
  toFun := ![2,10,11,6,12,13,14,0,1,15,3,4,5,7,8,9,16]
  invFun := ![7,8,0,10,11,12,3,13,14,15,1,2,4,5,6,9,16]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rankStacks : Fin 10 ⊕ Fin 7 ≃ Stack :=
  finSumFinEquiv.trans rankPermutation

def rankLabels : MatrixStage4ActiveRankMachine.Label ⊕
    (MatrixTableLookup.Label ⊕ Unit) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr u) => .inr (.inr u)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr u) => .inr (.inr u)
  left_inv l := by rcases l with l | (l | u) <;> rfl
  right_inv l := by rcases l with l | (l | u) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt lookupStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4ActiveRankMachine.gatherStart))
        (MatrixTableLookup.program l))
  | .inr (.inl l) => renameStmt rankStacks rankLabels (Equiv.prodComm _ _)
      (liftStmt (some (.inr ()))
        (MatrixStage4ActiveRankMachine.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def lookupFrame (c : MatrixTableLookup.Config) : Config :=
  renameCfg lookupStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4ActiveRankMachine.gatherStart))
      MatrixStage4ActiveRankMachine.initial
      (fun _ : Fin 7 => []) c)

theorem lookup_phase (c : MatrixTableLookup.Config)
    (bound : ℕ) (hhalt : (MatrixTableLookup.run bound c).l = none) :
    ∃ t ≤ bound, run t (lookupFrame c) =
      lookupFrame (MatrixTableLookup.run bound c) := by
  apply lift_outputs_renamed lookupStacks (Equiv.refl _) (Equiv.refl _)
    MatrixTableLookup.program program
    (some (.inl MatrixStage4ActiveRankMachine.gatherStart))
  · intro l
    rfl
  · exact hhalt

def rankFrame (foreign : Fin 7 → List Bool)
    (lookupControl : MatrixTableLookup.Control)
    (c : MatrixStage4ActiveRankMachine.Config) : Config :=
  renameCfg rankStacks rankLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) lookupControl foreign c)

theorem rank_phase (foreign : Fin 7 → List Bool)
    (lookupControl : MatrixTableLookup.Control)
    (c : MatrixStage4ActiveRankMachine.Config) (bound : ℕ)
    (hhalt : (MatrixStage4ActiveRankMachine.run bound c).l = none) :
    ∃ t ≤ bound, run t (rankFrame foreign lookupControl c) =
      rankFrame foreign lookupControl
        (MatrixStage4ActiveRankMachine.run bound c) := by
  apply lift_outputs_renamed rankStacks rankLabels (Equiv.prodComm _ _)
    MatrixStage4ActiveRankMachine.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def rankForeign (c : Config) : Fin 7 → List Bool :=
  fun j => c.stk (rankStacks (.inr j))

theorem bridge (row width column source : List Bool) (bit : Bool) :
    let lookupResult := MatrixTableLookup.cfg none MatrixTableLookup.initial
      row width column [] source [bit]
    lookupFrame lookupResult =
      rankFrame (rankForeign (lookupFrame lookupResult))
        MatrixTableLookup.initial
        (MatrixStage4ActiveRankMachine.cfg
          (some MatrixStage4ActiveRankMachine.gatherStart)
          MatrixStage4ActiveRankMachine.initial
          column source [] row width []) := by
  dsimp
  unfold lookupFrame rankFrame rankForeign renameCfg liftCfg
    MatrixTableLookup.cfg MatrixStage4ActiveRankMachine.cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem finish (c : Config) (hc : c.l = some done) :
    run 1 c = ⟨none,c.var,c.stk⟩ := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp at hc
    | some l =>
      have hl : l = done := Option.some.inj hc
      subst l
      simp [run,advance,done,program,TM2.step,TM2.stepAux]

open MatrixMaterialization Construction

theorem vector_flag_rank_run {n q : ℕ}
    (vectors : Fin n → Fin q → Bool) (i : Fin n) (α : Fin q) :
    let input := lookupFrame
      (MatrixTableLookup.cfg (some MatrixTableLookup.start)
        MatrixTableLookup.initial
        (List.replicate i.val true) (List.replicate q true)
        (List.replicate α.val true) [] (rowMajor vectors) [])
    ∃ t ≤ 32*(i.val+q+α.val+n*q+1)^2+
      i.val*(3*(α.val+i.val*q)+3*(n*q)+2*q+12)+i.val+4,
      (run t input).l = none ∧
      (run t input).stk 0 =
        List.replicate (activeRank vectors α i) true ∧
      (run t input).stk 7 = [vectors i α] := by
  dsimp
  let lookupInput := MatrixTableLookup.cfg (some MatrixTableLookup.start)
    MatrixTableLookup.initial
    (List.replicate i.val true) (List.replicate q true)
    (List.replicate α.val true) [] (rowMajor vectors) []
  obtain ⟨tl,htl,hl⟩ := MatrixStage4PayloadRead.vector_run
    vectors i α []
  have hlookup : (MatrixTableLookup.run tl lookupInput).l = none := by
    simpa only [lookupInput] using congrArg
      (fun c : MatrixTableLookup.Config => c.l) hl
  obtain ⟨t₁,ht₁,h₁⟩ := lookup_phase lookupInput tl hlookup
  rw [hl] at h₁
  let lookupResult := MatrixTableLookup.cfg none MatrixTableLookup.initial
    (List.replicate i.val true) (List.replicate q true)
    (List.replicate α.val true) [] (rowMajor vectors) [vectors i α]
  let foreign := rankForeign (lookupFrame lookupResult)
  let rankInput := MatrixStage4ActiveRankMachine.cfg
    (some MatrixStage4ActiveRankMachine.gatherStart)
    MatrixStage4ActiveRankMachine.initial
    (List.replicate α.val true) (rowMajor vectors) []
    (List.replicate i.val true) (List.replicate q true) []
  have hb : lookupFrame lookupResult =
      rankFrame foreign MatrixTableLookup.initial rankInput := by
    simpa only [lookupResult,foreign,rankInput] using
      bridge (List.replicate i.val true) (List.replicate q true)
        (List.replicate α.val true) (rowMajor vectors) (vectors i α)
  obtain ⟨tr,htr,hr⟩ := MatrixStage4ActiveRankMachine.active_rank_run
    vectors i α
  have hrank : (MatrixStage4ActiveRankMachine.run tr rankInput).l = none := by
    simpa only [rankInput] using congrArg
      (fun c : MatrixStage4ActiveRankMachine.Config => c.l) hr
  obtain ⟨t₂,ht₂,h₂⟩ := rank_phase foreign
    MatrixTableLookup.initial rankInput tr hrank
  let terminal := rankFrame foreign MatrixTableLookup.initial
    (MatrixStage4ActiveRankMachine.run tr rankInput)
  have hlabel : terminal.l = some done := by
    dsimp [terminal,rankFrame,renameCfg,liftCfg]
    rw [hrank]
    rfl
  have hfinal := finish terminal hlabel
  have h12 := run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := run_add h12 1
  rw [hfinal] at h123
  refine ⟨t₁+t₂+1,?_,?_,?_,?_⟩
  · omega
  · rw [h123]
  · rw [h123]
    have hout := congrArg
      (fun c : MatrixStage4ActiveRankMachine.Config => c.stk 7) hr
    simpa only [terminal,rankFrame,renameCfg,liftCfg,rankInput,
      MatrixStage4ActiveRankMachine.cfg] using hout
  · rw [h123]
    rfl

end EthInapproximability.CurrentPaper.MatrixStage4VectorFlagRank
