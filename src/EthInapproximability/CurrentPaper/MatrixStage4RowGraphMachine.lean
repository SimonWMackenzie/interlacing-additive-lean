import EthInapproximability.CurrentPaper.MatrixStage4AlignmentVectorGraph
import EthInapproximability.CurrentPaper.MatrixStage4RowMachine
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-!
# Raw-row decoding before the physical graph branch

The row program produces the source row and ordered item index on its own
banks. This controller will share those banks with the later graph program;
they are not constructor-provided graph inputs.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4RowGraphMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming MatrixStage4Codes Construction
open MatrixMaterialization

def graphSeed {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool) (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (out : List Bool) : MatrixStage4AlignmentVectorGraph.Config :=
  let c := (rawColumnCode a s q cy).symm code
  let flag := decide (aligned hs c)
  let target := MatrixStage4AlignmentVectorGraph.graphInput
    hs vectors R code i x flag out
  let ai := MatrixStage4OrdinalCopyAlignment.alignmentInput code
  let ac := MatrixStage4OrdinalCopyAlignment.copyFrame ai.var
    (MatrixStage4OrdinalCopyAlignment.copyForeign ai)
    (BitMachineCopy.cfg (some .scan) none
      (List.replicate code.val true) [] [])
  MatrixStage4AlignmentVectorGraph.alignmentFrame
    (MatrixStage4AlignmentVectorGraph.pendingGraphControl target)
    (MatrixStage4AlignmentVectorGraph.graphBankSeedBlank target) ac

theorem graphSeed_control_independent {a s q n rx cy : ℕ}
    (hs : 0 < s) (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i j : Fin n) (x y : Fin rx)
    (out : List Bool) :
    (graphSeed hs vectors R code i x out).var =
    (graphSeed hs vectors R code j y out).var := by rfl

theorem graphSeed_banks_replaced {a s q n rx cy : ℕ}
    (hs : 0 < s) (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i j : Fin n) (x y : Fin rx)
    (out : List Bool) :
    (graphSeed hs vectors R code i x out).stk =
    Function.update (Function.update
      (graphSeed hs vectors R code j y out).stk (42 : Fin 79)
      (List.replicate x.val true)) (61 : Fin 79)
      (List.replicate i.val true) := by
  funext k
  fin_cases k <;> rfl

theorem graphSeed_source_row {a s q n rx cy : ℕ}
    (hs : 0 < s) (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (out : List Bool) :
    (graphSeed hs vectors R code i x out).stk 42 =
      List.replicate x.val true := by rfl

theorem graphSeed_item_index {a s q n rx cy : ℕ}
    (hs : 0 < s) (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (out : List Bool) :
    (graphSeed hs vectors R code i x out).stk 61 =
      List.replicate i.val true := by rfl


abbrev Stack := Fin 89
abbrev Label := MatrixStage4RowMachine.Label ⊕
  (MatrixStage4AlignmentVectorGraph.Label ⊕ Unit)
abbrev Control := MatrixStage4RowMachine.Control ×
  MatrixStage4AlignmentVectorGraph.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def rowStart : Label := .inl MatrixStage4RowMachine.cutStart
def graphStart : Label := .inr (.inl MatrixStage4AlignmentVectorGraph.alignStart)
def done : Label := .inr (.inr ())

def rowPermutation : Stack ≃ Stack :=
  (((((((((Equiv.swap (0 : Stack) 79).trans
    (Equiv.swap (1 : Stack) 80)).trans
    (Equiv.swap (2 : Stack) 81)).trans
    (Equiv.swap (3 : Stack) 82)).trans
    (Equiv.swap (4 : Stack) 83)).trans
    (Equiv.swap (5 : Stack) 84)).trans
    (Equiv.swap (6 : Stack) 85)).trans
    (Equiv.swap (7 : Stack) 42)).trans
    (Equiv.swap (8 : Stack) 61)).trans
    (Equiv.swap (9 : Stack) 86)

def rowStacks : Fin 10 ⊕ Fin 79 ≃ Stack :=
  finSumFinEquiv.trans rowPermutation
def graphStacks : Fin 79 ⊕ Fin 10 ≃ Stack := finSumFinEquiv

def graphLabels : MatrixStage4AlignmentVectorGraph.Label ⊕
    (MatrixStage4RowMachine.Label ⊕ Unit) ≃ Label where
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
  | .inl l => renameStmt rowStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4AlignmentVectorGraph.alignStart))
        (MatrixStage4RowMachine.program l))
  | .inr (.inl l) => renameStmt graphStacks graphLabels
      (Equiv.prodComm _ _)
      (liftStmt (some (.inr ()))
        (MatrixStage4AlignmentVectorGraph.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def foreignSeed (target : MatrixStage4AlignmentVectorGraph.Config)
    (j : Fin 79) : List Bool :=
  let k := rowStacks (.inr j)
  if h : k.val < 79 then target.stk ⟨k.val,h⟩ else []

def rowFrame (target : MatrixStage4AlignmentVectorGraph.Config)
    (c : MatrixStage4RowMachine.Config) : Config :=
  renameCfg rowStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4AlignmentVectorGraph.alignStart))
      target.var (foreignSeed target) c)

theorem row_phase (target : MatrixStage4AlignmentVectorGraph.Config)
    (c : MatrixStage4RowMachine.Config) (bound : ℕ)
    (hhalt : (MatrixStage4RowMachine.run bound c).l = none) :
    ∃ t ≤ bound, run t (rowFrame target c) =
      rowFrame target (MatrixStage4RowMachine.run bound c) := by
  apply lift_outputs_renamed rowStacks (Equiv.refl _) (Equiv.refl _)
    MatrixStage4RowMachine.program program
    (some (.inl MatrixStage4AlignmentVectorGraph.alignStart))
  · intro l; rfl
  · exact hhalt

def graphFrame (foreign : Fin 10 → List Bool)
    (rowControl : MatrixStage4RowMachine.Control)
    (c : MatrixStage4AlignmentVectorGraph.Config) : Config :=
  renameCfg graphStacks graphLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) rowControl foreign c)

theorem graph_phase (foreign : Fin 10 → List Bool)
    (rowControl : MatrixStage4RowMachine.Control)
    (c : MatrixStage4AlignmentVectorGraph.Config) (bound : ℕ)
    (hhalt : (MatrixStage4AlignmentVectorGraph.run bound c).l = none) :
    ∃ t ≤ bound, run t (graphFrame foreign rowControl c) =
      graphFrame foreign rowControl
        (MatrixStage4AlignmentVectorGraph.run bound c) := by
  apply lift_outputs_renamed graphStacks graphLabels (Equiv.prodComm _ _)
    MatrixStage4AlignmentVectorGraph.program program (some (.inr ()))
  · intro l; rfl
  · exact hhalt

def graphForeign (c : Config) : Fin 10 → List Bool :=
  fun j => c.stk (graphStacks (.inr j))

def graphProjection (c : Config) : MatrixStage4AlignmentVectorGraph.Config :=
  ⟨some MatrixStage4AlignmentVectorGraph.alignStart,c.var.2,
    fun k => c.stk (graphStacks (.inl k))⟩

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

theorem row_output_slots :
    rowStacks (.inl (7 : Fin 10)) = (42 : Stack) ∧
    rowStacks (.inl (8 : Fin 10)) = (61 : Stack) := by decide

theorem row_foreign_slots :
    ∀ j : Fin 79, rowStacks (.inr j) ≠ (42 : Stack) ∧
      rowStacks (.inr j) ≠ (61 : Stack) := by decide

theorem graph_slot_classification :
    ∀ k : Fin 79, k = 42 ∨ k = 61 ∨
      ∃ j : Fin 79, rowStacks (.inr j) = graphStacks (.inl k) := by
  have hlocal : ∀ r : Fin 10,
      (rowStacks (.inl r)).val < 79 → r = 7 ∨ r = 8 := by decide
  intro k
  cases hw : rowStacks.symm (graphStacks (.inl k)) with
  | inl r =>
    have hmap : rowStacks (.inl r) = graphStacks (.inl k) := by
      simpa only [hw] using rowStacks.apply_symm_apply (graphStacks (.inl k))
    have hlt : (rowStacks (.inl r)).val < 79 := by
      rw [hmap]
      change k.val < 79
      exact k.isLt
    rcases hlocal r hlt with hr | hr
    · subst r
      left
      have h7 : rowStacks (.inl (7 : Fin 10)) = (42 : Stack) := by decide
      have hv := congrArg Fin.val (hmap.symm.trans h7)
      change k.val = 42 at hv
      exact Fin.ext hv
    · subst r
      right; left
      have h8 : rowStacks (.inl (8 : Fin 10)) = (61 : Stack) := by decide
      have hv := congrArg Fin.val (hmap.symm.trans h8)
      change k.val = 61 at hv
      exact Fin.ext hv
  | inr j =>
    right; right
    exact ⟨j,by simpa only [hw] using
      rowStacks.apply_symm_apply (graphStacks (.inl k))⟩

theorem row_projection (target : MatrixStage4AlignmentVectorGraph.Config)
    (c : MatrixStage4RowMachine.Config)
    (hstart : target.l = some MatrixStage4AlignmentVectorGraph.alignStart)
    (hx : c.stk 7 = target.stk 42)
    (hi : c.stk 8 = target.stk 61) :
    graphProjection (rowFrame target c) = target := by
  have hb : ∀ k, (rowFrame target c).stk (graphStacks (.inl k)) =
      target.stk k := by
    intro k
    rcases graph_slot_classification k with hk | hk | ⟨j,hmap⟩
    · subst k
      have h : graphStacks (.inl (42 : Fin 79)) =
          rowStacks (.inl (7 : Fin 10)) := by decide
      rw [h]
      simpa only [rowFrame,renameCfg,liftCfg,
        rowStacks.symm_apply_apply,Sum.elim_inl] using hx
    · subst k
      have h : graphStacks (.inl (61 : Fin 79)) =
          rowStacks (.inl (8 : Fin 10)) := by decide
      rw [h]
      simpa only [rowFrame,renameCfg,liftCfg,
        rowStacks.symm_apply_apply,Sum.elim_inl] using hi
    · rw [← hmap]
      simp only [rowFrame,renameCfg,liftCfg,
        rowStacks.symm_apply_apply,Sum.elim_inr]
      change foreignSeed target j = target.stk k
      simp [foreignSeed,hmap,graphStacks,finSumFinEquiv]
  cases target with
  | mk l v S =>
    have hl : l = some MatrixStage4AlignmentVectorGraph.alignStart := hstart
    subst l
    have hv : (rowFrame ⟨some MatrixStage4AlignmentVectorGraph.alignStart,v,S⟩
        c).var.2 = v := rfl
    have hs : (fun k => (rowFrame
        ⟨some MatrixStage4AlignmentVectorGraph.alignStart,v,S⟩ c).stk
        (graphStacks (.inl k))) = S := by
      funext k
      exact hb k
    unfold graphProjection
    rw [hv,hs]

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

theorem composed_run (rowInput : MatrixStage4RowMachine.Config)
    (target : MatrixStage4AlignmentVectorGraph.Config)
    (tr tg : ℕ) (value : List Bool)
    (hr : (MatrixStage4RowMachine.run tr rowInput).l = none)
    (htarget : target.l = some MatrixStage4AlignmentVectorGraph.alignStart)
    (hx : (MatrixStage4RowMachine.run tr rowInput).stk 7 = target.stk 42)
    (hi : (MatrixStage4RowMachine.run tr rowInput).stk 8 = target.stk 61)
    (hg : (MatrixStage4AlignmentVectorGraph.run tg target).l = none)
    (hout : (MatrixStage4AlignmentVectorGraph.run tg target).stk 48 = value) :
    ∃ t ≤ tr+tg+1,
      (run t (rowFrame target rowInput)).l = none ∧
      (run t (rowFrame target rowInput)).stk 48 = value := by
  obtain ⟨t₁,ht₁,h₁⟩ := row_phase target rowInput tr hr
  let afterRow := rowFrame target (MatrixStage4RowMachine.run tr rowInput)
  have hlabel : afterRow.l = some graphStart := by
    dsimp [afterRow,rowFrame,renameCfg,liftCfg]
    rw [hr]
    rfl
  have hproj : graphProjection afterRow = target :=
    row_projection target (MatrixStage4RowMachine.run tr rowInput)
      htarget hx hi
  have hb : afterRow = graphFrame (graphForeign afterRow)
      afterRow.var.1 target := by
    have hh := graph_bridge afterRow hlabel
    rw [hproj] at hh
    exact hh
  obtain ⟨t₂,ht₂,h₂⟩ := graph_phase (graphForeign afterRow)
    afterRow.var.1 target tg hg
  let terminal := graphFrame (graphForeign afterRow) afterRow.var.1
    (MatrixStage4AlignmentVectorGraph.run tg target)
  have hterminal : terminal.l = some done := by
    dsimp [terminal,graphFrame,renameCfg,liftCfg]
    rw [hg]
    rfl
  have hf := finish terminal hterminal
  have h12 := run_add h₁ t₂
  change run (t₁+t₂) (rowFrame target rowInput) =
    run t₂ afterRow at h12
  rw [hb,h₂] at h12
  have h123 := run_add h12 1
  rw [hf] at h123
  refine ⟨t₁+t₂+1,by omega,?_,?_⟩
  · rw [h123]
  · rw [h123]
    simpa only [terminal,graphFrame,renameCfg,liftCfg] using hout


open MatrixStage4Digits MatrixStage4AlignmentDigits

def graphBudget {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx) : ℕ :=
  let c := (rawColumnCode a s q cy).symm code
  let α := (c.2 (firstBin s hs)).1
  let j := MatrixStage4GraphChoose.chosenTail hs vectors cap i c
  let y := c.1 j
  let base := binBase a s q cy
  let wordSize := wordBase a s cy
  let outer := base^s
  let nlow := code.val%outer
  let reference := selectorDigit code (firstBin s hs)
  ((2*code.val+2)+
    (MatrixUnaryDivision.totalTime code.val outer+
      MatrixStage4LowDigitStream.timeBudget nlow base wordSize (s-1)+
      MatrixStage4AlignmentStream.budget
        (MatrixStage4AlignmentCorrect.selectorWords code) reference+3)+1)+
  (2*α.val+3)+
  ((32*(i.val+q+α.val+n*q+1)^2+
    i.val*(3*(α.val+i.val*q)+3*(n*q)+2*q+12)+i.val+4)+
    (activeRank vectors α i+s+1+
      (3*j.val+4+MatrixWeightedPower.powerBound cy (s-j.val)+
        MatrixStage4TailSourceRead.tailBudget code j+
        32*(x.val+cy+y.val+rx*cy+1)^2+5)+1)+2)+1

def itemRowInput {s L nv nb rx : ℕ} (order : ItemOrder nv nb)
    (i : Fin (nv+nb)) (x : Fin rx) : MatrixStage4RowMachine.Config :=
  MatrixStage4RowMachine.cfg (some MatrixStage4RowMachine.cutStart)
    MatrixStage4RowMachine.initial
    (List.replicate
      (rowCode s L nv nb rx order
        ((rawRowEquiv s L nv nb order).symm (.inr (i,x)))).val true)
    (List.replicate (s*L) true) (List.replicate L true)
    (List.replicate rx true) [] [] [] []

theorem graphSeed_start {a s q n rx cy : ℕ}
    (hs : 0 < s) (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (out : List Bool) :
    (graphSeed hs vectors R code i x out).l =
      some MatrixStage4AlignmentVectorGraph.alignStart := by rfl

theorem rawMatrix_item {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin (nv+nb)) (x : Fin rx)
    (c : RawColumns a s q (Fin cy)) :
    rawMatrix R a s q L nv nb hs family order vectors cap
      ((rawRowEquiv s L nv nb order).symm (.inr (i,x))) c =
      graphEntry R hs vectors cap i x c := by
  let e := rawRowEquiv s L nv nb order (X := Fin rx)
  obtain ⟨r,hr⟩ := e.surjective (.inr (i,x))
  have he : e.symm (.inr (i,x)) = r := by rw [← hr,Equiv.symm_apply_apply]
  rw [he]
  rcases r with r | (r | r)
  · have hh : (Sum.inl r : ThirdRows s L ⊕
        (Fin (nv+nb) × Fin rx)) = Sum.inr (i,x) := by
      simpa only [e,rawRowEquiv] using hr
    cases hh
  · rcases r with ⟨j,y⟩
    have hh : (vertexIndex order j,y) = (i,x) := by
      exact Sum.inr.inj (by simpa only [e,rawRowEquiv_vertex] using hr)
    cases hh
    rfl
  · rcases r with ⟨j,y⟩
    have hh : (auxiliaryIndex order j,y) = (i,x) := by
      exact Sum.inr.inj (by simpa only [e,rawRowEquiv_auxiliary] using hr)
    cases hh
    rfl

theorem item_graph_run {a s q L nv nb rx cy : ℕ} (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin (nv+nb)) (x : Fin rx)
    (out : List Bool) :
    let rowInput := itemRowInput (s := s) (L := L) order i x
    let target := graphSeed hs vectors R code i x out
    ∃ t ≤ (3*(s*L)+8*(x.val+rx*i.val)+3*rx+10)+
      graphBudget hs vectors cap R code i x+1,
      (run t (rowFrame target rowInput)).l = none ∧
      (run t (rowFrame target rowInput)).stk 48 =
        rawMatrix R a s q L nv nb hs family order vectors cap
          ((rawRowEquiv s L nv nb order).symm (.inr (i,x)))
          ((rawColumnCode a s q cy).symm code) :: out := by
  dsimp
  let rowInput := itemRowInput (s := s) (L := L) order i x
  let target := graphSeed hs vectors R code i x out
  obtain ⟨tr,htr,hrEq⟩ := MatrixStage4RowMachine.item_row_run order i x
  have hr : (MatrixStage4RowMachine.run tr rowInput).l = none := by
    simpa only [rowInput,itemRowInput] using congrArg (fun c => c.l) hrEq
  have hx : (MatrixStage4RowMachine.run tr rowInput).stk 7 = target.stk 42 := by
    rw [graphSeed_source_row]
    simpa only [rowInput,itemRowInput] using congrArg (fun c => c.stk 7) hrEq
  have hi : (MatrixStage4RowMachine.run tr rowInput).stk 8 = target.stk 61 := by
    rw [graphSeed_item_index]
    simpa only [rowInput,itemRowInput] using congrArg (fun c => c.stk 8) hrEq
  obtain ⟨tg,htg,hgl,hgo⟩ :=
    MatrixStage4AlignmentVectorGraph.alignment_vector_graph_run
      hs vectors cap R code i x out
  have hg : (MatrixStage4AlignmentVectorGraph.run tg target).l = none := by
    change (MatrixStage4AlignmentVectorGraph.run tg target).l = none at hgl
    exact hgl
  have hout : (MatrixStage4AlignmentVectorGraph.run tg target).stk 48 =
      graphEntry R hs vectors cap i x
        ((rawColumnCode a s q cy).symm code) :: out := by
    change (MatrixStage4AlignmentVectorGraph.run tg target).stk 48 =
      graphEntry R hs vectors cap i x
        ((rawColumnCode a s q cy).symm code) :: out at hgo
    exact hgo
  obtain ⟨t,ht,hl,ho⟩ := composed_run rowInput target tr tg
    (graphEntry R hs vectors cap i x
      ((rawColumnCode a s q cy).symm code) :: out)
    hr (graphSeed_start hs vectors R code i x out) hx hi hg hout
  refine ⟨t,?_,hl,?_⟩
  · have hgt : tg ≤ graphBudget hs vectors cap R code i x := by
      dsimp [graphBudget]
      omega
    omega
  · rw [rawMatrix_item]
    exact ho

end EthInapproximability.CurrentPaper.MatrixStage4RowGraphMachine
