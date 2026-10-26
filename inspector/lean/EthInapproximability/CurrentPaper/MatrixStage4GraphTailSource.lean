import EthInapproximability.CurrentPaper.MatrixStage4PowerTailRead
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical graph-tail source path

The fixed selector chooses a unary active rank or the inactive tail index,
then the fixed selected-power/tail/source reader consumes that *computed*
index. The theorem identifies the resulting source bit with the frozen
`Construction.graphEntry`. Alignment, vector-bit and active-rank production,
source-row resolution, remaining scalar bases, and the raw writer remain
separate stages; this is not a complete raw-B entry callback.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4GraphTailSource

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 43
abbrev Label := Unit ⊕
  (MatrixStage4PowerTailRead.Label ⊕ Unit)
abbrev Control := MatrixStage4GraphChoose.Control ×
  MatrixStage4PowerTailRead.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def chooseStart : Label := .inl ()
def readStart : Label := .inr (.inl MatrixStage4PowerTailRead.powerStart)
def done : Label := .inr (.inr ())

def choosePermutation : Stack ≃ Stack where
  toFun := ![41,42,37,
    0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,
    22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,38,39,40]
  invFun := ![3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,
    26,27,28,29,30,31,32,33,34,35,36,37,38,39,2,40,41,42,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def chooseStacks : Fin 3 ⊕ Fin 40 ≃ Stack :=
  finSumFinEquiv.trans choosePermutation
def readStacks : Fin 41 ⊕ Fin 2 ≃ Stack := finSumFinEquiv

def readLabels : MatrixStage4PowerTailRead.Label ⊕
    (Unit ⊕ Unit) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl u) => .inl u
    | .inr (.inr u) => .inr (.inr u)
  invFun
    | .inl u => .inr (.inl u)
    | .inr (.inl l) => .inl l
    | .inr (.inr u) => .inr (.inr u)
  left_inv l := by rcases l with l | (u | u) <;> rfl
  right_inv l := by rcases l with u | (l | u) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt chooseStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4PowerTailRead.powerStart))
        (MatrixStage4GraphChoose.program l))
  | .inr (.inl l) => renameStmt readStacks readLabels
      (Equiv.prodComm _ _)
      (liftStmt (some (.inr ())) (MatrixStage4PowerTailRead.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def chooseFrame (readControl : MatrixStage4PowerTailRead.Control)
    (foreign : Fin 40 → List Bool)
    (c : MatrixStage4GraphChoose.Config) : Config :=
  renameCfg chooseStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4PowerTailRead.powerStart))
      readControl foreign c)

theorem choose_phase (readControl : MatrixStage4PowerTailRead.Control)
    (foreign : Fin 40 → List Bool)
    (c : MatrixStage4GraphChoose.Config) (bound : ℕ)
    (hhalt : (MatrixStage4GraphChoose.run bound c).l = none) :
    ∃ t ≤ bound, run t (chooseFrame readControl foreign c) =
      chooseFrame readControl foreign
        (MatrixStage4GraphChoose.run bound c) := by
  apply lift_outputs_renamed chooseStacks (Equiv.refl _) (Equiv.refl _)
    MatrixStage4GraphChoose.program program
    (some (.inl MatrixStage4PowerTailRead.powerStart))
  · intro l
    rfl
  · exact hhalt

def readFrame (foreign : Fin 2 → List Bool)
    (chooseControl : MatrixStage4GraphChoose.Control)
    (c : MatrixStage4PowerTailRead.Config) : Config :=
  renameCfg readStacks readLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) chooseControl foreign c)

theorem read_phase (foreign : Fin 2 → List Bool)
    (chooseControl : MatrixStage4GraphChoose.Control)
    (c : MatrixStage4PowerTailRead.Config) (bound : ℕ)
    (hhalt : (MatrixStage4PowerTailRead.run bound c).l = none) :
    ∃ t ≤ bound, run t (readFrame foreign chooseControl c) =
      readFrame foreign chooseControl
        (MatrixStage4PowerTailRead.run bound c) := by
  apply lift_outputs_renamed readStacks readLabels (Equiv.prodComm _ _)
    MatrixStage4PowerTailRead.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def readForeign (c : Config) : Fin 2 → List Bool :=
  fun j => c.stk (readStacks (.inr j))

def readProjection (c : Config) : MatrixStage4PowerTailRead.Config :=
  ⟨some MatrixStage4PowerTailRead.powerStart,c.var.2,
    fun i => c.stk (readStacks (.inl i))⟩

theorem bridge (readControl : MatrixStage4PowerTailRead.Control)
    (foreign : Fin 40 → List Bool)
    (c : MatrixStage4GraphChoose.Config) (hc : c.l = none) :
    let finished := chooseFrame readControl foreign c
    finished = readFrame (readForeign finished) c.var
      (readProjection finished) := by
  dsimp
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      unfold chooseFrame readFrame readForeign readProjection
        renameCfg liftCfg
      congr 1
      funext k
      fin_cases k <;> rfl

def foreignFrom (target : MatrixStage4PowerTailRead.Config) :
    Fin 40 → List Bool :=
  fun i => target.stk ⟨(chooseStacks (.inr i)).val,by
    fin_cases i <;> decide⟩

theorem projection_after_choose (target : MatrixStage4PowerTailRead.Config)
    (c : MatrixStage4GraphChoose.Config)
    (hindex : c.stk 2 = target.stk 37) :
    readProjection
      (chooseFrame target.var (foreignFrom target) c) =
      ⟨some MatrixStage4PowerTailRead.powerStart,target.var,target.stk⟩ := by
  cases target with
  | mk l v S =>
    unfold readProjection chooseFrame foreignFrom renameCfg liftCfg
    congr 1
    funext k
    fin_cases k <;> first | exact hindex | rfl

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

open MatrixStage4Codes Construction MatrixMaterialization

theorem graph_source_run {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool)
    (hflag : flag = true ↔
      aligned hs ((rawColumnCode a s q cy).symm code))
    (out : List Bool) :
    let c := (rawColumnCode a s q cy).symm code
    let α := (c.2 (firstBin s hs)).1
    let j := MatrixStage4GraphChoose.chosenTail hs vectors cap i c
    let y := c.1 j
    let readTarget := MatrixStage4TailSourceRead.tailFrame
      (List.replicate x.val true) (List.replicate cy true)
      (rowMajor R) out (MatrixStage4TailSourceRead.tailInput code j)
    let target := MatrixStage4PowerTailRead.powerFrame readTarget.var
      (MatrixStage4PowerTailRead.foreignFrom readTarget)
      (MatrixStage4SelectedPower.cutFrame (List.replicate cy true)
        (MatrixUnaryCut.cfg (some .scan) (false,true)
          (List.replicate s true) (List.replicate j.val true) [] []))
    let input := chooseFrame target.var (foreignFrom target)
      (MatrixStage4GraphChoose.cfg (some ())
        (MatrixStage4GraphChoose.initial flag (vectors i α))
        (List.replicate (activeRank vectors α i) true)
        (List.replicate s true) [])
    ∃ t ≤ activeRank vectors α i+s+1+
      (3*j.val+4+MatrixWeightedPower.powerBound cy (s-j.val)+
      MatrixStage4TailSourceRead.tailBudget code j+
      32*(x.val+cy+y.val+rx*cy+1)^2+5)+1,
      (run t input).l = none ∧
      (run t input).stk 28 = graphEntry R hs vectors cap i x c :: out := by
  dsimp
  let c := (rawColumnCode a s q cy).symm code
  let α := (c.2 (firstBin s hs)).1
  let j := MatrixStage4GraphChoose.chosenTail hs vectors cap i c
  let readTarget := MatrixStage4TailSourceRead.tailFrame
    (List.replicate x.val true) (List.replicate cy true)
    (rowMajor R) out (MatrixStage4TailSourceRead.tailInput code j)
  let target := MatrixStage4PowerTailRead.powerFrame readTarget.var
    (MatrixStage4PowerTailRead.foreignFrom readTarget)
    (MatrixStage4SelectedPower.cutFrame (List.replicate cy true)
      (MatrixUnaryCut.cfg (some .scan) (false,true)
        (List.replicate s true) (List.replicate j.val true) [] []))
  let chooseInput := MatrixStage4GraphChoose.cfg (some ())
    (MatrixStage4GraphChoose.initial flag (vectors i α))
    (List.replicate (activeRank vectors α i) true)
    (List.replicate s true) []
  obtain ⟨tc,htc,hcl,hcj⟩ :=
    MatrixStage4GraphChoose.graph_tail_choose_run
      hs vectors cap i c flag hflag []
  obtain ⟨t₁,ht₁,h₁⟩ := choose_phase target.var
    (foreignFrom target) chooseInput tc
    (by simpa only [chooseInput,α,c] using hcl)
  let chooseResult := MatrixStage4GraphChoose.run tc chooseInput
  have hb := bridge target.var (foreignFrom target)
    chooseResult (by simpa only [chooseResult,chooseInput,α,c] using hcl)
  have hprojection : readProjection
      (chooseFrame target.var (foreignFrom target) chooseResult) = target := by
    have hh := projection_after_choose target chooseResult
      (by
        have hi : chooseResult.stk 2 = List.replicate j.val true := by
          simpa only [chooseResult,chooseInput,α,c,j,List.append_nil] using hcj
        simpa only [target,MatrixStage4PowerTailRead.powerFrame,
          MatrixStage4SelectedPower.cutFrame,renameCfg,liftCfg] using hi)
    simpa only [target] using hh
  dsimp at hb
  rw [hprojection] at hb
  let foreign := readForeign
    (chooseFrame target.var (foreignFrom target) chooseResult)
  obtain ⟨tr,htr,hrl,hro⟩ :=
    MatrixStage4PowerTailRead.power_tail_source_run R code j x out
  have hhalt : (MatrixStage4PowerTailRead.run tr target).l = none := by
    simpa only [target,readTarget] using hrl
  obtain ⟨t₂,ht₂,h₂⟩ := read_phase foreign chooseResult.var target tr hhalt
  let terminal := readFrame foreign chooseResult.var
    (MatrixStage4PowerTailRead.run tr target)
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
  · dsimp [c,α,j] at htc htr ⊢
    omega
  · rw [h123]
  · rw [h123]
    have hgraph := MatrixStage4GraphChoose.graphEntry_chosenTail
      hs R vectors cap i x c
    rw [hgraph]
    simpa only [terminal,readFrame,renameCfg,liftCfg,target,c,j]
      using hro

end EthInapproximability.CurrentPaper.MatrixStage4GraphTailSource
