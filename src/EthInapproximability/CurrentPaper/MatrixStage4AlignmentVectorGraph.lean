import EthInapproximability.CurrentPaper.MatrixStage4AlignmentSelector
import EthInapproximability.CurrentPaper.MatrixStage4VectorGraphSource
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

set_option maxRecDepth 4096

/-!
# Physical alignment-to-vector/graph handoff

The alignment phase holds the sole original raw-column ordinal on bank 19.
The graph phase shares that bank. A charged copy transfers the computed
first-bin selector to the vector-table query bank 64, and a charged control
transition transfers the computed alignment bit. Neither value is supplied
to the starting configuration. This is a graph-branch entry machine, not yet
the full raw-matrix evaluator: source-row preparation, scalar construction,
and the template branch remain external.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4AlignmentVectorGraph

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 79
abbrev Label := MatrixStage4OrdinalCopyAlignment.Label ⊕
  (BitMachineCopy.Label ⊕ (Unit ⊕
    (MatrixStage4VectorGraphSource.Label ⊕ Unit)))
abbrev Control := MatrixStage4OrdinalCopyAlignment.Control ×
  MatrixStage4VectorGraphSource.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def alignStart : Label := .inl MatrixStage4OrdinalCopyAlignment.copyStart
def copyStart : Label := .inr (.inl .scan)
def admin : Label := .inr (.inr (.inl ()))
def graphStart : Label := .inr (.inr (.inr (.inl MatrixStage4VectorGraphSource.vectorStart)))
def done : Label := .inr (.inr (.inr (.inr ())))

def alignStacks : Fin 21 ⊕ Fin 58 ≃ Stack := finSumFinEquiv

def copyPermutation : Stack ≃ Stack :=
  ((Equiv.swap (0 : Stack) 9).trans (Equiv.swap (1 : Stack) 64)).trans
    (Equiv.swap (2 : Stack) 20)
def copyStacks : Fin 3 ⊕ Fin 76 ≃ Stack :=
  finSumFinEquiv.trans copyPermutation

def graphPermutation : Stack ≃ Stack where
  toFun := ![21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,
    19,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,
    57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,
    0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20]
  invFun := ![59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,
    16,78,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,18,19,20,21,22,23,
    24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,
    46,47,48,49,50,51,52,53,54,55,56,57,58]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def graphStacks : Fin 59 ⊕ Fin 20 ≃ Stack :=
  finSumFinEquiv.trans graphPermutation

def copyLabels : BitMachineCopy.Label ⊕
    (MatrixStage4OrdinalCopyAlignment.Label ⊕
      (Unit ⊕ (MatrixStage4VectorGraphSource.Label ⊕ Unit))) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl u)) => .inr (.inr (.inl u))
    | .inr (.inr (.inr (.inl l))) => .inr (.inr (.inr (.inl l)))
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl u)) => .inr (.inr (.inl u))
    | .inr (.inr (.inr (.inl l))) => .inr (.inr (.inr (.inl l)))
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  left_inv l := by rcases l with l | (l | (u | (l | u))) <;> rfl
  right_inv l := by rcases l with l | (l | (u | (l | u))) <;> rfl

def copyControl : (Option Bool ×
    (MatrixStage4AlignmentFromOrdinal.Control ×
      MatrixStage4VectorGraphSource.Control)) ≃ Control where
  toFun v := ((v.1,v.2.1),v.2.2)
  invFun v := (v.1.1,(v.1.2,v.2))
  left_inv v := by cases v with | mk a bc => cases bc; rfl
  right_inv v := by cases v with | mk ab c => cases ab; rfl

def graphLabels : MatrixStage4VectorGraphSource.Label ⊕
    (MatrixStage4OrdinalCopyAlignment.Label ⊕
      (BitMachineCopy.Label ⊕ (Unit ⊕ Unit))) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inr (.inl l)))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr (.inl u))) => .inr (.inr (.inl u))
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl u)) => .inr (.inr (.inr (.inl u)))
    | .inr (.inr (.inr (.inl l))) => .inl l
    | .inr (.inr (.inr (.inr u))) => .inr (.inr (.inr (.inr u)))
  left_inv l := by rcases l with l | (l | (l | (u | u))) <;> rfl
  right_inv l := by rcases l with l | (l | (u | (l | u))) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt alignStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl BitMachineCopy.Label.scan))
        (MatrixStage4OrdinalCopyAlignment.program l))
  | .inr (.inl l) => renameStmt copyStacks copyLabels copyControl
      (liftStmt (some (.inr (.inl ()))) (BitMachineCopy.program l))
  | .inr (.inr (.inl ())) => load
      (fun v => (v.1,(v.2.1,((v.1.2.2.2.1,none),v.2.2.2))))
      (goto (fun _ => graphStart))
  | .inr (.inr (.inr (.inl l))) => renameStmt graphStacks graphLabels
      (Equiv.prodComm _ _)
      (liftStmt (some (.inr (.inr (.inr ()))))
        (MatrixStage4VectorGraphSource.program l))
  | .inr (.inr (.inr (.inr ()))) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def alignmentFrame (graphControl : MatrixStage4VectorGraphSource.Control)
    (foreign : Fin 58 → List Bool)
    (c : MatrixStage4OrdinalCopyAlignment.Config) : Config :=
  renameCfg alignStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl BitMachineCopy.Label.scan)) graphControl foreign c)

theorem alignment_phase (graphControl : MatrixStage4VectorGraphSource.Control)
    (foreign : Fin 58 → List Bool)
    (c : MatrixStage4OrdinalCopyAlignment.Config) (bound : ℕ)
    (hhalt : (MatrixStage4OrdinalCopyAlignment.run bound c).l = none) :
    ∃ t ≤ bound, run t (alignmentFrame graphControl foreign c) =
      alignmentFrame graphControl foreign
        (MatrixStage4OrdinalCopyAlignment.run bound c) := by
  apply lift_outputs_renamed alignStacks (Equiv.refl _) (Equiv.refl _)
    MatrixStage4OrdinalCopyAlignment.program program
    (some (.inl BitMachineCopy.Label.scan))
  · intro l
    rfl
  · exact hhalt

def copyFrame (restControl : MatrixStage4AlignmentFromOrdinal.Control ×
      MatrixStage4VectorGraphSource.Control)
    (foreign : Fin 76 → List Bool)
    (c : MatrixStage4OrdinalCopyAlignment.CopyConfig) : Config :=
  renameCfg copyStacks copyLabels copyControl
    (liftCfg (some (.inr (.inl ()))) restControl foreign c)

theorem copy_phase (restControl : MatrixStage4AlignmentFromOrdinal.Control ×
      MatrixStage4VectorGraphSource.Control)
    (foreign : Fin 76 → List Bool)
    (c : MatrixStage4OrdinalCopyAlignment.CopyConfig) (bound : ℕ)
    (hhalt : (BitMachineCopy.run bound c).l = none) :
    ∃ t ≤ bound, run t (copyFrame restControl foreign c) =
      copyFrame restControl foreign (BitMachineCopy.run bound c) := by
  apply lift_outputs_renamed copyStacks copyLabels copyControl
    BitMachineCopy.program program (some (.inr (.inl ())))
  · intro l
    rfl
  · exact hhalt

def copyForeign (c : Config) : Fin 76 → List Bool :=
  fun j => c.stk (copyStacks (.inr j))

def copyProjection (c : Config) : MatrixStage4OrdinalCopyAlignment.CopyConfig :=
  ⟨some .scan,c.var.1.1,fun i => c.stk (copyStacks (.inl i))⟩

theorem copy_bridge (c : Config) (hc : c.l = some copyStart) :
    c = copyFrame (c.var.1.2,c.var.2) (copyForeign c) (copyProjection c) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp at hc
    | some l =>
      have hl : l = copyStart := Option.some.inj hc
      subst l
      unfold copyFrame copyForeign copyProjection renameCfg liftCfg
      congr 1
      funext k
      fin_cases k <;> rfl

def graphFrame (foreign : Fin 20 → List Bool)
    (alignmentControl : MatrixStage4OrdinalCopyAlignment.Control)
    (c : MatrixStage4VectorGraphSource.Config) : Config :=
  renameCfg graphStacks graphLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr (.inr (.inr ())))) alignmentControl foreign c)

theorem graph_phase (foreign : Fin 20 → List Bool)
    (alignmentControl : MatrixStage4OrdinalCopyAlignment.Control)
    (c : MatrixStage4VectorGraphSource.Config) (bound : ℕ)
    (hhalt : (MatrixStage4VectorGraphSource.run bound c).l = none) :
    ∃ t ≤ bound, run t (graphFrame foreign alignmentControl c) =
      graphFrame foreign alignmentControl
        (MatrixStage4VectorGraphSource.run bound c) := by
  apply lift_outputs_renamed graphStacks graphLabels (Equiv.prodComm _ _)
    MatrixStage4VectorGraphSource.program program
    (some (.inr (.inr (.inr ()))))
  · intro l
    rfl
  · exact hhalt

def graphBankSeed (target : MatrixStage4VectorGraphSource.Config) :
    Fin 58 → List Bool :=
  fun j => Sum.elim target.stk (fun _ => [])
    (graphStacks.symm (alignStacks (.inr j)))

def graphBankSeedBlank (target : MatrixStage4VectorGraphSource.Config) :
    Fin 58 → List Bool :=
  Function.update (graphBankSeed target) 43 []

def pendingGraphControl (target : MatrixStage4VectorGraphSource.Config) :
    MatrixStage4VectorGraphSource.Control :=
  (target.var.1,((false,none),target.var.2.2))

def graphForeign (c : Config) : Fin 20 → List Bool :=
  fun j => c.stk (graphStacks (.inr j))

def graphProjection (c : Config) : MatrixStage4VectorGraphSource.Config :=
  ⟨some MatrixStage4VectorGraphSource.vectorStart,c.var.2,
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

theorem admin_handoff (target : MatrixStage4VectorGraphSource.Config)
    (c : Config)
    (hl : c.l = some admin)
    (htarget : target.l = some MatrixStage4VectorGraphSource.vectorStart)
    (hbank : ∀ k, c.stk (graphStacks (.inl k)) = target.stk k)
    (hcontrol : (c.var.2.1,
      ((c.var.1.2.2.2.1,none),c.var.2.2.2)) = target.var) :
    let after := advance program c
    after.l = some graphStart ∧ graphProjection after = target := by
  dsimp
  cases c with
  | mk cl cv C =>
    cases cl with
    | none => simp at hl
    | some cl =>
      have he : cl = admin := Option.some.inj hl
      subst cl
      constructor
      · simp [advance,TM2.step,TM2.stepAux,program,admin,graphStart]
      · cases target with
        | mk tl tv T =>
          have ht : tl = some MatrixStage4VectorGraphSource.vectorStart := htarget
          subst tl
          have hv : (cv.2.1,((cv.1.2.2.2.1,none),cv.2.2.2)) = tv := hcontrol
          have hs : (fun k => C (graphStacks (.inl k))) = T := by
            funext k
            exact hbank k
          simp [graphProjection,advance,TM2.step,TM2.stepAux,program,
            admin,hv,hs]

theorem selector_copy_input (target : MatrixStage4VectorGraphSource.Config)
    (c : MatrixStage4OrdinalCopyAlignment.Config) (bits : List Bool)
    (hbits : c.stk 9 = bits) (hscratch : c.stk 20 = []) :
    let before := alignmentFrame (pendingGraphControl target)
      (graphBankSeedBlank target) c
    copyProjection before = BitMachineCopy.cfg (some .scan)
      c.var.1 bits [] [] := by
  dsimp
  unfold copyProjection BitMachineCopy.cfg
  congr 1
  funext k
  fin_cases k
  · simpa [alignmentFrame,renameCfg,liftCfg,copyStacks,copyPermutation]
      using hbits
  · have hc : copyStacks (.inl (1 : Fin 3)) = (64 : Stack) := by decide
    have ha : alignStacks.symm (64 : Stack) = Sum.inr (43 : Fin 58) := by decide
    change (alignmentFrame (pendingGraphControl target)
      (graphBankSeedBlank target) c).stk
        (copyStacks (.inl (1 : Fin 3))) = []
    rw [hc]
    simp only [alignmentFrame,renameCfg,liftCfg,ha,Sum.elim_inr,
      graphBankSeedBlank]
    simp
  · simpa [alignmentFrame,renameCfg,liftCfg,copyStacks,copyPermutation]
      using hscratch

theorem copy_finished_update (before : Config) (bits : List Bool)
    (hlabel : before.l = some copyStart)
    (hlocal : copyProjection before = BitMachineCopy.cfg (some .scan)
      before.var.1.1 bits [] []) :
    copyFrame (before.var.1.2,before.var.2) (copyForeign before)
      (BitMachineCopy.cfg none none bits bits []) =
    ⟨some admin,((none,before.var.1.2),before.var.2),
      Function.update before.stk 64 bits⟩ := by
  have hframe := copy_bridge before hlabel
  have hstack : (BitMachineCopy.cfg none none bits bits []).stk =
      Function.update (copyProjection before).stk 1 bits := by
    rw [hlocal]
    funext k
    fin_cases k <;> rfl
  have hmap : copyStacks (.inl (1 : Fin 3)) = (64 : Stack) := by decide
  have hbank : (copyFrame (before.var.1.2,before.var.2)
        (copyForeign before) (BitMachineCopy.cfg none none bits bits [])).stk =
      Function.update before.stk 64 bits := by
    simp only [copyFrame,renameCfg,liftCfg,hstack]
    rw [← BitMachineComposition.sum_update,BitMachineEncoding.rename_update]
    rw [hmap]
    exact congrArg (fun S : Stack → List Bool => Function.update S 64 bits)
      (congrArg (fun c : Config => c.stk) hframe.symm)
  cases before with
  | mk l v S =>
    have hl : l = some copyStart := hlabel
    subst l
    unfold copyFrame renameCfg liftCfg BitMachineCopy.cfg
    congr 1

theorem graph_slot_classification :
    ∀ k : Fin 59, k = 16 ∨ k = 44 ∨
      ∃ j : Fin 58, j ≠ 43 ∧
        alignStacks (.inr j) = graphStacks (.inl k) := by
  decide

theorem graph_banks_after_selector_copy
    (target : MatrixStage4VectorGraphSource.Config)
    (c : MatrixStage4OrdinalCopyAlignment.Config) (bits : List Bool)
    (hcode : c.stk 19 = target.stk 16)
    (hcolumn : target.stk 44 = bits) :
    ∀ k, (Function.update
      (alignmentFrame (pendingGraphControl target)
        (graphBankSeedBlank target) c).stk 64 bits)
      (graphStacks (.inl k)) = target.stk k := by
  intro k
  rcases graph_slot_classification k with hk | hk | ⟨j,hj,hmap⟩
  · subst k
    have h16 : graphStacks (.inl (16 : Fin 59)) = (19 : Stack) := by decide
    rw [h16]
    simp only [Function.update_of_ne (by decide : (19 : Stack) ≠ 64)]
    change c.stk 19 = target.stk 16
    exact hcode
  · subst k
    have h44 : graphStacks (.inl (44 : Fin 59)) = (64 : Stack) := by decide
    rw [h44]
    simp [hcolumn]
  · rw [← hmap]
    have h64 : alignStacks (.inr (43 : Fin 58)) = (64 : Stack) := by decide
    have hne : alignStacks (.inr j) ≠ (64 : Stack) := by
      intro hh
      exact hj (Sum.inr.inj (alignStacks.injective (hh.trans h64.symm)))
    rw [Function.update_of_ne hne]
    simp only [alignmentFrame,renameCfg,liftCfg,
      alignStacks.symm_apply_apply,Sum.elim_inr]
    change (graphBankSeedBlank target) j = target.stk k
    simp only [graphBankSeedBlank,Function.update_of_ne hj,
      graphBankSeed,hmap,graphStacks.symm_apply_apply,Sum.elim_inl]

theorem selector_copy_handoff
    (target : MatrixStage4VectorGraphSource.Config)
    (c : MatrixStage4OrdinalCopyAlignment.Config) (bits : List Bool)
    (hl : c.l = none)
    (hstart : target.l = some MatrixStage4VectorGraphSource.vectorStart)
    (hbits : c.stk 9 = bits) (hscratch : c.stk 20 = [])
    (hcode : c.stk 19 = target.stk 16)
    (hcolumn : target.stk 44 = bits)
    (hflag : target.var.2.1 = (c.var.2.2.2.1,none)) :
    let before := alignmentFrame (pendingGraphControl target)
      (graphBankSeedBlank target) c
    ∃ t ≤ 2*bits.length+3,
      (run t before).l = some graphStart ∧
      graphProjection (run t before) = target := by
  dsimp
  let before := alignmentFrame (pendingGraphControl target)
    (graphBankSeedBlank target) c
  have hlabel : before.l = some copyStart := by
    dsimp [before,alignmentFrame,renameCfg,liftCfg]
    rw [hl]
    rfl
  let copyInput := BitMachineCopy.cfg (some .scan) c.var.1 bits [] []
  have hlocal : copyProjection before = copyInput := by
    simpa only [before,copyInput] using selector_copy_input
      target c bits hbits hscratch
  have hb : before = copyFrame (before.var.1.2,before.var.2)
      (copyForeign before) copyInput := by
    have hh := copy_bridge before hlabel
    rw [hlocal] at hh
    exact hh
  have hcopy : BitMachineCopy.run (2*bits.length+2) copyInput =
      BitMachineCopy.cfg none none bits bits [] := by
    simpa only [copyInput,List.append_nil] using
      BitMachineCopy.run_correct c.var.1 bits []
  obtain ⟨tc,htc,hc⟩ := copy_phase (before.var.1.2,before.var.2)
    (copyForeign before) copyInput (2*bits.length+2)
    (by rw [hcopy]; rfl)
  rw [hcopy] at hc
  have hupdate := copy_finished_update before bits hlabel
    (by simpa only [copyInput] using hlocal)
  let ready : Config := ⟨some admin,
    ((none,before.var.1.2),before.var.2),
    Function.update before.stk 64 bits⟩
  have hr : run tc before = ready := by
    rw [hb,hc,hupdate]
  have hbank : ∀ k, ready.stk (graphStacks (.inl k)) = target.stk k := by
    simpa only [ready,before] using
      graph_banks_after_selector_copy target c bits hcode hcolumn
  have hcontrol : (ready.var.2.1,
      ((ready.var.1.2.2.2.1,none),ready.var.2.2.2)) = target.var := by
    simp only [ready,before,alignmentFrame,pendingGraphControl,
      renameCfg,liftCfg]
    exact Prod.ext rfl (Prod.ext hflag.symm rfl)
  obtain ⟨hnext,hprojection⟩ := admin_handoff target ready
    (by rfl) hstart hbank hcontrol
  have hstep : run 1 ready = advance program ready := by rfl
  have htotal := run_add hr 1
  rw [hstep] at htotal
  refine ⟨tc+1,by omega,?_,?_⟩
  · rw [htotal]
    exact hnext
  · rw [htotal]
    exact hprojection

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

theorem composed_run (alignmentInput : MatrixStage4OrdinalCopyAlignment.Config)
    (target : MatrixStage4VectorGraphSource.Config)
    (ta tg : ℕ) (bits value : List Bool)
    (ha : (MatrixStage4OrdinalCopyAlignment.run ta alignmentInput).l = none)
    (hbits : (MatrixStage4OrdinalCopyAlignment.run ta alignmentInput).stk 9 = bits)
    (hscratch : (MatrixStage4OrdinalCopyAlignment.run ta alignmentInput).stk 20 = [])
    (hcode : (MatrixStage4OrdinalCopyAlignment.run ta alignmentInput).stk 19 =
      target.stk 16)
    (hcolumn : target.stk 44 = bits)
    (hstart : target.l = some MatrixStage4VectorGraphSource.vectorStart)
    (hflag : target.var.2.1 =
      ((MatrixStage4OrdinalCopyAlignment.run ta alignmentInput).var.2.2.2.1,none))
    (hg : (MatrixStage4VectorGraphSource.run tg target).l = none)
    (hout : (MatrixStage4VectorGraphSource.run tg target).stk 28 = value) :
    ∃ t ≤ ta+(2*bits.length+3)+tg+1,
      (run t (alignmentFrame (pendingGraphControl target)
        (graphBankSeedBlank target) alignmentInput)).l = none ∧
      (run t (alignmentFrame (pendingGraphControl target)
        (graphBankSeedBlank target) alignmentInput)).stk 48 = value := by
  obtain ⟨t₁,ht₁,h₁⟩ := alignment_phase (pendingGraphControl target)
    (graphBankSeedBlank target) alignmentInput ta ha
  let ac := MatrixStage4OrdinalCopyAlignment.run ta alignmentInput
  obtain ⟨tc,htc,hlabel,hprojection⟩ := selector_copy_handoff target ac bits
    ha hstart hbits hscratch hcode hcolumn hflag
  have h12 := run_add h₁ tc
  let between := run tc (alignmentFrame (pendingGraphControl target)
    (graphBankSeedBlank target) ac)
  have hb : between = graphFrame (graphForeign between)
      between.var.1 target := by
    have hh := graph_bridge between hlabel
    rw [hprojection] at hh
    exact hh
  obtain ⟨t₂,ht₂,h₂⟩ := graph_phase (graphForeign between)
    between.var.1 target tg hg
  let terminal := graphFrame (graphForeign between) between.var.1
    (MatrixStage4VectorGraphSource.run tg target)
  have hterminal : terminal.l = some done := by
    dsimp [terminal,graphFrame,renameCfg,liftCfg]
    rw [hg]
    rfl
  have hf := finish terminal hterminal
  change run (t₁+tc)
    (alignmentFrame (pendingGraphControl target)
      (graphBankSeedBlank target) alignmentInput) = between at h12
  have h123 := run_add h12 t₂
  rw [hb,h₂] at h123
  have h1234 := run_add h123 1
  rw [hf] at h1234
  refine ⟨t₁+tc+t₂+1,by omega,?_,?_⟩
  · rw [h1234]
  · rw [h1234]
    simpa only [terminal,graphFrame,renameCfg,liftCfg] using hout


open MatrixStage4Codes MatrixStage4Digits MatrixStage4AlignmentDigits
open Construction MatrixMaterialization

def graphInput {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) : MatrixStage4VectorGraphSource.Config :=
  let c := (rawColumnCode a s q cy).symm code
  let α := (c.2 (firstBin s hs)).1
  let target := MatrixStage4VectorGraphSource.sourceTarget
    hs vectors R code i x flag out
  MatrixStage4VectorGraphSource.vectorFrame
    (MatrixStage4VectorGraphSource.pending target flag)
    (MatrixStage4VectorGraphSource.foreignFrom target)
    (MatrixStage4VectorGraphSource.vectorInput vectors i α)

theorem graphInput_start {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) :
    (graphInput hs vectors R code i x flag out).l =
      some MatrixStage4VectorGraphSource.vectorStart := by
  rfl

theorem graphInput_control {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) :
    (graphInput hs vectors R code i x flag out).var.2.1 = (flag,none) := by
  rfl

theorem graphInput_code {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) :
    (graphInput hs vectors R code i x flag out).stk 16 =
      List.replicate code.val true := by
  rfl

theorem graphInput_column {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (flag : Bool) (out : List Bool) :
    (graphInput hs vectors R code i x flag out).stk 44 =
      List.replicate
        (((rawColumnCode a s q cy).symm code).2 (firstBin s hs)).1.val true := by
  rfl

theorem initial_flag_independent {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (out : List Bool) (f g : Bool)
    (ainput : MatrixStage4OrdinalCopyAlignment.Config) :
    alignmentFrame (pendingGraphControl (graphInput hs vectors R code i x f out))
      (graphBankSeedBlank (graphInput hs vectors R code i x f out)) ainput =
    alignmentFrame (pendingGraphControl (graphInput hs vectors R code i x g out))
      (graphBankSeedBlank (graphInput hs vectors R code i x g out)) ainput := by
  rfl


theorem alignment_vector_graph_run {a s q n rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin n) (x : Fin rx)
    (out : List Bool) :
    let c := (rawColumnCode a s q cy).symm code
    let flag := decide (aligned hs c)
    let α := (c.2 (firstBin s hs)).1
    let j := MatrixStage4GraphChoose.chosenTail hs vectors cap i c
    let y := c.1 j
    let base := binBase a s q cy
    let wordSize := wordBase a s cy
    let outer := base^s
    let nlow := code.val%outer
    let reference := selectorDigit code (firstBin s hs)
    let ainput := MatrixStage4OrdinalCopyAlignment.alignmentInput code
    let astart := MatrixStage4OrdinalCopyAlignment.copyFrame
      ainput.var (MatrixStage4OrdinalCopyAlignment.copyForeign ainput)
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate code.val true) [] [])
    let gtarget := graphInput hs vectors R code i x flag out
    let input := alignmentFrame (pendingGraphControl gtarget)
      (graphBankSeedBlank gtarget) astart
    ∃ t ≤
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
            32*(x.val+cy+y.val+rx*cy+1)^2+5)+1)+2)+1,
      (run t input).l = none ∧
      (run t input).stk 48 = graphEntry R hs vectors cap i x c :: out := by
  dsimp
  let c := (rawColumnCode a s q cy).symm code
  let flag := decide (aligned hs c)
  let α := (c.2 (firstBin s hs)).1
  let j := MatrixStage4GraphChoose.chosenTail hs vectors cap i c
  let y := c.1 j
  let ainput := MatrixStage4OrdinalCopyAlignment.alignmentInput code
  let astart := MatrixStage4OrdinalCopyAlignment.copyFrame
    ainput.var (MatrixStage4OrdinalCopyAlignment.copyForeign ainput)
    (BitMachineCopy.cfg (some .scan) none
      (List.replicate code.val true) [] [])
  let gtarget := graphInput hs vectors R code i x flag out
  let bits := List.replicate α.val true
  obtain ⟨ta,hta,hal,hasource,haflag,haquo,hasel,hascratch⟩ :=
    MatrixStage4AlignmentSelector.copy_alignment_selector hs code
  have hAlign : (MatrixStage4OrdinalCopyAlignment.run ta astart).l = none := by
    simpa only [astart,ainput] using hal
  have hSource : (MatrixStage4OrdinalCopyAlignment.run ta astart).stk 19 =
      gtarget.stk 16 := by
    rw [graphInput_code]
    simpa only [astart,ainput] using hasource
  have hSelector : (MatrixStage4OrdinalCopyAlignment.run ta astart).stk 9 =
      bits := by
    have he := MatrixStage4AlignmentDigits.selector_value code (firstBin s hs)
    simpa only [astart,ainput,bits,α,c,he] using hasel
  have hScratch : (MatrixStage4OrdinalCopyAlignment.run ta astart).stk 20 =
      [] := by simpa only [astart,ainput] using hascratch
  have hColumn : gtarget.stk 44 = bits := by
    simpa only [gtarget,bits,α,c] using
      graphInput_column hs vectors R code i x flag out
  have hPhysicalFlag :
      (MatrixStage4OrdinalCopyAlignment.run ta astart).var.2.2.2.1 = flag := by
    have hf : ((MatrixStage4OrdinalCopyAlignment.run ta astart).var.2.2.2.1 = true ↔
        aligned hs c) := by
      simpa only [astart,ainput,c] using haflag
    by_cases h : aligned hs c
    · have hb := hf.mpr h
      simp [flag,h,hb]
    · have hb : (MatrixStage4OrdinalCopyAlignment.run ta astart).var.2.2.2.1 =
          false := Bool.eq_false_iff.mpr (fun ht => h (hf.mp ht))
      simp [flag,h,hb]
  have hSemanticFlag : flag = true ↔ aligned hs c := by simp [flag]
  obtain ⟨tg,htg,hgl,hgo⟩ :=
    MatrixStage4VectorGraphSource.vector_graph_source_run
      hs vectors cap R code i x flag hSemanticFlag out
  have hGraph : (MatrixStage4VectorGraphSource.run tg gtarget).l = none := by
    change (MatrixStage4VectorGraphSource.run tg gtarget).l = none at hgl
    exact hgl
  have hOutput : (MatrixStage4VectorGraphSource.run tg gtarget).stk 28 =
      graphEntry R hs vectors cap i x c :: out := by
    change (MatrixStage4VectorGraphSource.run tg gtarget).stk 28 =
      graphEntry R hs vectors cap i x c :: out at hgo
    exact hgo
  have hTargetControl : gtarget.var.2.1 =
      ((MatrixStage4OrdinalCopyAlignment.run ta astart).var.2.2.2.1,none) := by
    rw [graphInput_control,hPhysicalFlag]
  obtain ⟨t,ht,hl,ho⟩ := composed_run astart gtarget ta tg bits
    (graphEntry R hs vectors cap i x c :: out)
    hAlign hSelector hScratch hSource hColumn
    (graphInput_start hs vectors R code i x flag out)
    hTargetControl hGraph hOutput
  refine ⟨t,?_,hl,ho⟩
  dsimp only [bits,α,c,flag] at ht hta htg ⊢
  simp only [List.length_replicate] at ht
  omega

end EthInapproximability.CurrentPaper.MatrixStage4AlignmentVectorGraph
