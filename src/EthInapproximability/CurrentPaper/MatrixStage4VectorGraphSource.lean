import EthInapproximability.CurrentPaper.MatrixStage4VectorFlagRank
import EthInapproximability.CurrentPaper.MatrixStage4GraphTailSource
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical vector bit/rank handoff to graph source

The first fixed subprogram reads one literal vector bit and computes its
active rank from the same table. One charged administrative pop transfers
that bit into the graph selector's finite control; the rank output occupies
the selector's unary input bank. The graph-tail source program then runs.
The alignment flag and other raw-column scalar inputs are still supplied.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4VectorGraphSource

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 59
abbrev Label := MatrixStage4VectorFlagRank.Label ⊕
  (Unit ⊕ (MatrixStage4GraphTailSource.Label ⊕ Unit))
abbrev Control := MatrixStage4VectorFlagRank.Control ×
  MatrixStage4GraphTailSource.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def vectorStart : Label := .inl MatrixStage4VectorFlagRank.lookupStart
def admin : Label := .inr (.inl ())
def graphStart : Label := .inr (.inr (.inl MatrixStage4GraphTailSource.chooseStart))
def done : Label := .inr (.inr (.inr ()))

def vectorPermutation : Stack ≃ Stack where
  toFun := ![41,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,
    0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,
    22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,42]
  invFun := ![17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,
    37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,
    0,58,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def vectorStacks : Fin 17 ⊕ Fin 42 ≃ Stack :=
  finSumFinEquiv.trans vectorPermutation
def graphStacks : Fin 43 ⊕ Fin 16 ≃ Stack := finSumFinEquiv

def graphLabels : MatrixStage4GraphTailSource.Label ⊕
    (MatrixStage4VectorFlagRank.Label ⊕ (Unit ⊕ Unit)) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl u)) => .inr (.inl u)
    | .inr (.inr (.inr u)) => .inr (.inr (.inr u))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl u) => .inr (.inr (.inl u))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr u)) => .inr (.inr (.inr u))
  left_inv l := by rcases l with l | (l | (u | u)) <;> rfl
  right_inv l := by rcases l with l | (u | (l | u)) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt vectorStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl ())) (MatrixStage4VectorFlagRank.program l))
  | .inr (.inl ()) => pop 49
      (fun v b => (v.1, ((v.2.1.1 && b.getD false,none),v.2.2)))
      (goto (fun _ => graphStart))
  | .inr (.inr (.inl l)) => renameStmt graphStacks graphLabels
      (Equiv.prodComm _ _)
      (liftStmt (some (.inr (.inr ())))
        (MatrixStage4GraphTailSource.program l))
  | .inr (.inr (.inr ())) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def vectorFrame (graphControl : MatrixStage4GraphTailSource.Control)
    (foreign : Fin 42 → List Bool)
    (c : MatrixStage4VectorFlagRank.Config) : Config :=
  renameCfg vectorStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl ())) graphControl foreign c)

theorem vector_phase (graphControl : MatrixStage4GraphTailSource.Control)
    (foreign : Fin 42 → List Bool)
    (c : MatrixStage4VectorFlagRank.Config) (bound : ℕ)
    (hhalt : (MatrixStage4VectorFlagRank.run bound c).l = none) :
    ∃ t ≤ bound, run t (vectorFrame graphControl foreign c) =
      vectorFrame graphControl foreign
        (MatrixStage4VectorFlagRank.run bound c) := by
  apply lift_outputs_renamed vectorStacks (Equiv.refl _) (Equiv.refl _)
    MatrixStage4VectorFlagRank.program program (some (.inl ()))
  · intro l
    rfl
  · exact hhalt

def graphFrame (foreign : Fin 16 → List Bool)
    (vectorControl : MatrixStage4VectorFlagRank.Control)
    (c : MatrixStage4GraphTailSource.Config) : Config :=
  renameCfg graphStacks graphLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr (.inr ()))) vectorControl foreign c)

theorem graph_phase (foreign : Fin 16 → List Bool)
    (vectorControl : MatrixStage4VectorFlagRank.Control)
    (c : MatrixStage4GraphTailSource.Config) (bound : ℕ)
    (hhalt : (MatrixStage4GraphTailSource.run bound c).l = none) :
    ∃ t ≤ bound, run t (graphFrame foreign vectorControl c) =
      graphFrame foreign vectorControl
        (MatrixStage4GraphTailSource.run bound c) := by
  apply lift_outputs_renamed graphStacks graphLabels (Equiv.prodComm _ _)
    MatrixStage4GraphTailSource.program program
    (some (.inr (.inr ())))
  · intro l
    rfl
  · exact hhalt

def graphForeign (c : Config) : Fin 16 → List Bool :=
  fun j => c.stk (graphStacks (.inr j))

def graphProjection (c : Config) : MatrixStage4GraphTailSource.Config :=
  ⟨some MatrixStage4GraphTailSource.chooseStart,c.var.2,
    fun i => c.stk (graphStacks (.inl i))⟩

theorem graph_bridge (c : Config) (hc : c.l = some graphStart) :
    c = graphFrame (graphForeign c) c.var.1 (graphProjection c) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp at hc
    | some l =>
      have hl : l = graphStart := Option.some.inj hc
      subst l
      unfold graphFrame graphForeign graphProjection renameCfg liftCfg
      congr 1
      funext k
      fin_cases k <;> rfl

def foreignFrom (target : MatrixStage4GraphTailSource.Config) :
    Fin 42 → List Bool :=
  fun i => target.stk ⟨(vectorStacks (.inr i)).val,by
    fin_cases i <;> decide⟩

def pending (target : MatrixStage4GraphTailSource.Config)
    (flag : Bool) : MatrixStage4GraphTailSource.Control :=
  ((flag,none),target.var.2)

theorem admin_handoff (target : MatrixStage4GraphTailSource.Config)
    (flag bit : Bool) (c : MatrixStage4VectorFlagRank.Config)
    (hl : c.l = none)
    (hrank : c.stk 0 = target.stk 41)
    (hbit : c.stk 7 = [bit])
    (htarget : target.l = some MatrixStage4GraphTailSource.chooseStart)
    (hcontrol : target.var.1 = (flag && bit, none)) :
    let before := vectorFrame (pending target flag) (foreignFrom target) c
    let after := advance program before
    after.l = some graphStart ∧ graphProjection after = target := by
  dsimp
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      constructor
      · simp [vectorFrame,renameCfg,liftCfg,advance,TM2.step,
          TM2.stepAux,program,graphStart]
      · cases target with
        | mk tl tv T =>
          have htl : tl = some MatrixStage4GraphTailSource.chooseStart := htarget
          subst tl
          simp only [graphProjection]
          congr 1
          · simp [vectorFrame,renameCfg,liftCfg,advance,TM2.step,
              TM2.stepAux,program,pending]
            have hbit' : S 7 = [bit] := hbit
            have hmap : vectorStacks.symm (49 : Stack) = Sum.inl (7 : Fin 17) := by
              decide
            simp only [hmap, Sum.elim_inl]
            rw [hbit']
            simp only [List.head?_cons, Option.getD_some]
            exact Prod.ext hcontrol.symm rfl
          · funext k
            fin_cases k <;> first | exact hrank | rfl

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

theorem composed_run (target : MatrixStage4GraphTailSource.Config)
    (flag bit : Bool) (input : MatrixStage4VectorFlagRank.Config)
    (tv tg : ℕ) (value : List Bool)
    (hv : (MatrixStage4VectorFlagRank.run tv input).l = none)
    (hrank : (MatrixStage4VectorFlagRank.run tv input).stk 0 = target.stk 41)
    (hbit : (MatrixStage4VectorFlagRank.run tv input).stk 7 = [bit])
    (htarget : target.l = some MatrixStage4GraphTailSource.chooseStart)
    (hcontrol : target.var.1 = (flag && bit, none))
    (hg : (MatrixStage4GraphTailSource.run tg target).l = none)
    (hout : (MatrixStage4GraphTailSource.run tg target).stk 28 = value) :
    ∃ t ≤ tv+tg+2,
      (run t (vectorFrame (pending target flag) (foreignFrom target) input)).l = none ∧
      (run t (vectorFrame (pending target flag) (foreignFrom target) input)).stk 28 =
        value := by
  obtain ⟨t₁,ht₁,h₁⟩ := vector_phase (pending target flag)
    (foreignFrom target) input tv hv
  obtain ⟨hlabel,hprojection⟩ := admin_handoff target flag bit
    (MatrixStage4VectorFlagRank.run tv input) hv hrank hbit htarget hcontrol
  let after := advance program
    (vectorFrame (pending target flag) (foreignFrom target)
      (MatrixStage4VectorFlagRank.run tv input))
  have hbridge : after = graphFrame (graphForeign after) after.var.1 target := by
    have hh := graph_bridge after hlabel
    rw [hprojection] at hh
    exact hh
  obtain ⟨t₂,ht₂,h₂⟩ := graph_phase (graphForeign after) after.var.1
    target tg hg
  let terminal := graphFrame (graphForeign after) after.var.1
    (MatrixStage4GraphTailSource.run tg target)
  have hterminal : terminal.l = some done := by
    dsimp [terminal,graphFrame,renameCfg,liftCfg]
    rw [hg]
    rfl
  have hf := finish terminal hterminal
  have h12 := run_add h₁ 1
  change run (t₁+1) _ = after at h12
  have h123 := run_add h12 t₂
  rw [hbridge,h₂] at h123
  have h1234 := run_add h123 1
  rw [hf] at h1234
  refine ⟨t₁+1+t₂+1,by omega,?_,?_⟩
  · rw [h1234]
  · rw [h1234]
    simpa only [terminal,graphFrame,renameCfg,liftCfg] using hout

open MatrixStage4Codes Construction MatrixMaterialization

def sourceTargetSeed {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) (seed : Fin (s + 1)) :
    MatrixStage4GraphTailSource.Config :=
  let c := (rawColumnCode a s q cy).symm code
  let α := (c.2 (firstBin s hs)).1
  let readTarget := MatrixStage4TailSourceRead.tailFrame
    (List.replicate x.val true) (List.replicate cy true)
    (rowMajor R) out (MatrixStage4TailSourceRead.tailInput code seed)
  let target := MatrixStage4PowerTailRead.powerFrame readTarget.var
    (MatrixStage4PowerTailRead.foreignFrom readTarget)
    (MatrixStage4SelectedPower.cutFrame (List.replicate cy true)
      (MatrixUnaryCut.cfg (some .scan) (false, true)
        (List.replicate s true) (List.replicate seed.val true) [] []))
  MatrixStage4GraphTailSource.chooseFrame target.var
    (MatrixStage4GraphTailSource.foreignFrom target)
    (MatrixStage4GraphChoose.cfg (some ())
      (MatrixStage4GraphChoose.initial flag (vectors i α))
      (List.replicate (activeRank vectors α i) true)
      (List.replicate s true) [])

theorem sourceTargetSeed_independent {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) (u v : Fin (s + 1)) :
    sourceTargetSeed hs vectors R code i x flag out u =
      sourceTargetSeed hs vectors R code i x flag out v := by
  unfold sourceTargetSeed
  dsimp
  congr 1
  funext k
  fin_cases k <;> rfl

def sourceTarget {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) : MatrixStage4GraphTailSource.Config :=
  sourceTargetSeed hs vectors R code i x flag out ⟨0, Nat.zero_lt_succ s⟩

def vectorInput {n q : ℕ} (vectors : Fin n → Fin q → Bool)
    (i : Fin n) (α : Fin q) : MatrixStage4VectorFlagRank.Config :=
  MatrixStage4VectorFlagRank.lookupFrame
    (MatrixTableLookup.cfg (some MatrixTableLookup.start)
      MatrixTableLookup.initial (List.replicate i.val true)
      (List.replicate q true) (List.replicate α.val true)
      [] (rowMajor vectors) [])

theorem sourceTarget_rank {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) :
    (sourceTarget hs vectors R code i x flag out).stk 41 =
      List.replicate (activeRank vectors
        (((rawColumnCode a s q cy).symm code).2 (firstBin s hs)).1 i) true := by
  rfl

theorem sourceTarget_control {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) :
    (sourceTarget hs vectors R code i x flag out).var.1 =
      (flag && vectors i
        (((rawColumnCode a s q cy).symm code).2 (firstBin s hs)).1, none) := by
  rfl

theorem sourceTarget_start {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) :
    (sourceTarget hs vectors R code i x flag out).l =
      some MatrixStage4GraphTailSource.chooseStart := by
  rfl

theorem vector_graph_source_run {a s q n rx cy : ℕ} (hs : 0 < s)
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
    let target := sourceTarget hs vectors R code i x flag out
    let input := vectorFrame (pending target flag) (foreignFrom target)
      (vectorInput vectors i α)
    ∃ t ≤
      (32*(i.val+q+α.val+n*q+1)^2+
        i.val*(3*(α.val+i.val*q)+3*(n*q)+2*q+12)+i.val+4)+
      (activeRank vectors α i + s + 1 +
        (3*j.val + 4 + MatrixWeightedPower.powerBound cy (s - j.val) +
          MatrixStage4TailSourceRead.tailBudget code j +
          32*(x.val + cy + y.val + rx*cy + 1)^2 + 5) + 1) + 2,
      (run t input).l = none ∧
      (run t input).stk 28 = graphEntry R hs vectors cap i x c :: out := by
  dsimp
  let c := (rawColumnCode a s q cy).symm code
  let α := (c.2 (firstBin s hs)).1
  let j := MatrixStage4GraphChoose.chosenTail hs vectors cap i c
  let y := c.1 j
  let target := sourceTarget hs vectors R code i x flag out
  let vin := vectorInput vectors i α
  obtain ⟨tv,htv,hvl,hvr,hvb⟩ :=
    MatrixStage4VectorFlagRank.vector_flag_rank_run vectors i α
  have hvin : (MatrixStage4VectorFlagRank.run tv vin).l = none := by
    simpa only [vin,vectorInput] using hvl
  have hvrank : (MatrixStage4VectorFlagRank.run tv vin).stk 0 =
      target.stk 41 := by
    rw [sourceTarget_rank]
    simpa only [vin,vectorInput,α,c] using hvr
  have hvbit : (MatrixStage4VectorFlagRank.run tv vin).stk 7 =
      [vectors i α] := by
    simpa only [vin,vectorInput] using hvb
  obtain ⟨tg,htg,hgl,hgo⟩ :=
    MatrixStage4GraphTailSource.graph_source_run
      hs vectors cap R code i x flag hflag out
  have hseed : target = sourceTargetSeed hs vectors R code i x flag out j := by
    exact sourceTargetSeed_independent hs vectors R code i x flag out
      ⟨0, Nat.zero_lt_succ s⟩ j
  have hgraph : (MatrixStage4GraphTailSource.run tg target).l = none := by
    rw [hseed]
    change (MatrixStage4GraphTailSource.run tg
      (sourceTargetSeed hs vectors R code i x flag out j)).l = none at hgl
    exact hgl
  have hout : (MatrixStage4GraphTailSource.run tg target).stk 28 =
      graphEntry R hs vectors cap i x c :: out := by
    rw [hseed]
    change (MatrixStage4GraphTailSource.run tg
      (sourceTargetSeed hs vectors R code i x flag out j)).stk 28 =
      graphEntry R hs vectors cap i x c :: out at hgo
    exact hgo
  obtain ⟨t,ht,hl,ho⟩ := composed_run target flag (vectors i α)
    vin tv tg (graphEntry R hs vectors cap i x c :: out)
    hvin hvrank hvbit (sourceTarget_start hs vectors R code i x flag out)
    (sourceTarget_control hs vectors R code i x flag out) hgraph hout
  refine ⟨t,?_,hl,ho⟩
  dsimp only [α,c] at ht htv htg ⊢
  omega

end EthInapproximability.CurrentPaper.MatrixStage4VectorGraphSource
