import EthInapproximability.CurrentPaper.MatrixStage4TailSourceRead
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Selected-power and tail-source-read physical composition

This fixed program computes the selected stride `cy^(s-j)` on a bank which
is then used by the actual raw-ordinal tail decoder and source-table read.
The source row, selected tail index, and other scalar powers are still input
banks. The stride is not an input bank and no source answer is supplied.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4PowerTailRead

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 41
abbrev Label := MatrixStage4SelectedPower.Label ⊕
  (MatrixStage4TailSourceRead.Label ⊕ Unit)
abbrev Control := MatrixStage4SelectedPower.Control ×
  MatrixStage4TailSourceRead.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def powerStart : Label := .inl MatrixStage4SelectedPower.cutStart
def readStart : Label := .inr (.inl MatrixStage4TailSourceRead.tailStart)
def done : Label := .inr (.inr ())

def powerPermutation : Stack ≃ Stack where
  toFun := ![2,31,32,33,34,35,36,37,38,39,40,
    0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  invFun := ![11,12,0,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,
    35,36,37,38,39,40,1,2,3,4,5,6,7,8,9,10]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def powerStacks : Fin 11 ⊕ Fin 30 ≃ Stack :=
  finSumFinEquiv.trans powerPermutation
def readStacks : Fin 31 ⊕ Fin 10 ≃ Stack := finSumFinEquiv

def readLabels : MatrixStage4TailSourceRead.Label ⊕
    (MatrixStage4SelectedPower.Label ⊕ Unit) ≃ Label where
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
  | .inl l => renameStmt powerStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4TailSourceRead.tailStart))
        (MatrixStage4SelectedPower.program l))
  | .inr (.inl l) => renameStmt readStacks readLabels
      (Equiv.prodComm _ _)
      (liftStmt (some (.inr ())) (MatrixStage4TailSourceRead.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def powerFrame (readControl : MatrixStage4TailSourceRead.Control)
    (foreign : Fin 30 → List Bool)
    (c : MatrixStage4SelectedPower.Config) : Config :=
  renameCfg powerStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4TailSourceRead.tailStart))
      readControl foreign c)

theorem power_phase (readControl : MatrixStage4TailSourceRead.Control)
    (foreign : Fin 30 → List Bool)
    (c : MatrixStage4SelectedPower.Config) (bound : ℕ)
    (hhalt : (MatrixStage4SelectedPower.run bound c).l = none) :
    ∃ t ≤ bound, run t (powerFrame readControl foreign c) =
      powerFrame readControl foreign
        (MatrixStage4SelectedPower.run bound c) := by
  apply lift_outputs_renamed powerStacks (Equiv.refl _) (Equiv.refl _)
    MatrixStage4SelectedPower.program program
    (some (.inl MatrixStage4TailSourceRead.tailStart))
  · intro l
    rfl
  · exact hhalt

def readFrame (foreign : Fin 10 → List Bool)
    (powerControl : MatrixStage4SelectedPower.Control)
    (c : MatrixStage4TailSourceRead.Config) : Config :=
  renameCfg readStacks readLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) powerControl foreign c)

theorem read_phase (foreign : Fin 10 → List Bool)
    (powerControl : MatrixStage4SelectedPower.Control)
    (c : MatrixStage4TailSourceRead.Config) (bound : ℕ)
    (hhalt : (MatrixStage4TailSourceRead.run bound c).l = none) :
    ∃ t ≤ bound, run t (readFrame foreign powerControl c) =
      readFrame foreign powerControl
        (MatrixStage4TailSourceRead.run bound c) := by
  apply lift_outputs_renamed readStacks readLabels (Equiv.prodComm _ _)
    MatrixStage4TailSourceRead.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def readForeign (c : Config) : Fin 10 → List Bool :=
  fun j => c.stk (readStacks (.inr j))

def readProjection (c : Config) : MatrixStage4TailSourceRead.Config :=
  ⟨some MatrixStage4TailSourceRead.tailStart,c.var.2,
    fun i => c.stk (readStacks (.inl i))⟩

theorem bridge (readControl : MatrixStage4TailSourceRead.Control)
    (foreign : Fin 30 → List Bool)
    (c : MatrixStage4SelectedPower.Config) (hc : c.l = none) :
    let finished := powerFrame readControl foreign c
    finished = readFrame (readForeign finished) c.var
      (readProjection finished) := by
  dsimp
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      unfold powerFrame readFrame readForeign readProjection
        renameCfg liftCfg
      congr 1
      funext k
      fin_cases k <;> rfl

def foreignFrom (target : MatrixStage4TailSourceRead.Config) :
    Fin 30 → List Bool :=
  fun i => target.stk ⟨(powerStacks (.inr i)).val,by
    fin_cases i <;> decide⟩

theorem projection_after_power (target : MatrixStage4TailSourceRead.Config)
    (c : MatrixStage4SelectedPower.Config) (hstride :
      c.stk 0 = target.stk 2) :
    readProjection
      (powerFrame target.var (foreignFrom target) c) =
      ⟨some MatrixStage4TailSourceRead.tailStart,target.var,target.stk⟩ := by
  cases target with
  | mk l v S =>
    unfold readProjection powerFrame foreignFrom renameCfg liftCfg
    congr 1
    funext k
    fin_cases k <;> first | exact hstride | rfl

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

open MatrixStage4Codes MatrixStage4Digits Construction MatrixMaterialization

theorem power_tail_source_run {a s q rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (j : Fin (s+1))
    (x : Fin rx) (out : List Bool) :
    let y := ((rawColumnCode a s q cy).symm code).1 j
    let target := MatrixStage4TailSourceRead.tailFrame
      (List.replicate x.val true) (List.replicate cy true)
      (rowMajor R) out (MatrixStage4TailSourceRead.tailInput code j)
    let input := powerFrame target.var (foreignFrom target)
      (MatrixStage4SelectedPower.cutFrame (List.replicate cy true)
        (MatrixUnaryCut.cfg (some .scan) (false,true)
          (List.replicate s true) (List.replicate j.val true) [] []))
    ∃ t ≤ 3*j.val+4+
      MatrixWeightedPower.powerBound cy (s-j.val)+
      MatrixStage4TailSourceRead.tailBudget code j+
      32*(x.val+cy+y.val+rx*cy+1)^2+5,
      (run t input).l = none ∧ (run t input).stk 28 = R x y :: out := by
  dsimp
  let target := MatrixStage4TailSourceRead.tailFrame
    (List.replicate x.val true) (List.replicate cy true)
    (rowMajor R) out (MatrixStage4TailSourceRead.tailInput code j)
  let powerInput := MatrixStage4SelectedPower.cutFrame
    (List.replicate cy true)
    (MatrixUnaryCut.cfg (some .scan) (false,true)
      (List.replicate s true) (List.replicate j.val true) [] [])
  obtain ⟨tp,htp,hpl,hps⟩ :=
    MatrixStage4SelectedPower.selected_power_run cy s j
  obtain ⟨t₁,ht₁,h₁⟩ := power_phase target.var
    (foreignFrom target) powerInput tp
    (by simpa only [powerInput] using hpl)
  let powerResult := MatrixStage4SelectedPower.run tp powerInput
  have hb := bridge target.var (foreignFrom target)
    powerResult (by simpa only [powerResult,powerInput] using hpl)
  have hprojection : readProjection
      (powerFrame target.var (foreignFrom target) powerResult) = target := by
    have hh := projection_after_power target powerResult
      (by
        have hs : powerResult.stk 0 =
            List.replicate (cy^(s-j.val)) true := by
          simpa only [powerResult,powerInput] using hps
        simpa only [target,MatrixStage4TailSourceRead.tailFrame,
          MatrixStage4TailSourceRead.tailInput,
          MatrixStage4TailFromOrdinal.splitFrame,renameCfg,liftCfg] using hs)
    simpa only [target] using hh
  dsimp at hb
  rw [hprojection] at hb
  let foreign := readForeign
    (powerFrame target.var (foreignFrom target) powerResult)
  obtain ⟨tr,htr,hrl,hro⟩ :=
    MatrixStage4TailSourceRead.source_after_tail_run R code j x out
  have hhalt : (MatrixStage4TailSourceRead.run tr target).l = none := by
    simpa only [target] using hrl
  obtain ⟨t₂,ht₂,h₂⟩ := read_phase foreign powerResult.var target tr hhalt
  let terminal := readFrame foreign powerResult.var
    (MatrixStage4TailSourceRead.run tr target)
  have hlabel : terminal.l = some done := by
    dsimp [terminal,readFrame,renameCfg,liftCfg]
    rw [hhalt]
    rfl
  have hfinal := finish terminal hlabel
  have h12 := run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := run_add h12 1
  rw [hfinal] at h123
  refine ⟨t₁+t₂+1,?_,?_,?_⟩
  · omega
  · rw [h123]
  · rw [h123]
    simpa only [terminal,readFrame,renameCfg,liftCfg,target] using hro

end EthInapproximability.CurrentPaper.MatrixStage4PowerTailRead
