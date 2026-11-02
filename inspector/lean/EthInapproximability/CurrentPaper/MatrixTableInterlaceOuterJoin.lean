import EthInapproximability.CurrentPaper.MatrixTableInterlaceScalarJoin
import EthInapproximability.CurrentPaper.MatrixOuterWidthMachine

/-!
# Charged outer-width handoff

A fixed finite Boolean-stack controller produces unary outer width q from
unary lambda, duplicates q into the restoration-width input and the first
interlace size input, then runs the frozen scalar-to-double join. The protected
table and first-pass duplicated dimension headers remain explicit inputs.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceOuterJoin

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev OStack := MatrixOuterWidthMachine.Stack
abbrev IStack := MatrixTableInterlaceScalarJoin.Stack
abbrev Stack := OStack ⊕ IStack
abbrev OLabel := MatrixOuterWidthMachine.Label
abbrev ILabel := MatrixTableInterlaceScalarJoin.Label
abbrev Label := OLabel ⊕ (Unit ⊕ ILabel)
abbrev OControl := MatrixOuterWidthMachine.Control
abbrev IControl := MatrixTableInterlaceScalarJoin.Control
abbrev Control := OControl × (IControl × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable def qSource : Stack := .inl MatrixOuterWidthMachine.outputStack
noncomputable def qRestTarget : Stack :=
  .inr (.inl (MatrixRestorationWidthMachine.inputStack 3))
def qFirstTarget : Stack :=
  .inr (.inr (.inl (.inl (.inl (.inl 0)))))
def bridgeStart : Label := .inr (.inl ())
noncomputable def innerStart : Label :=
  .inr (.inr (.inl MatrixRestorationWidthMachine.startLabel))

def innerLabels : ILabel ⊕ (OLabel ⊕ Unit) ≃ Label where
  toFun
    | .inl l => .inr (.inr l)
    | .inr (.inl l) => .inl l
    | .inr (.inr u) => .inr (.inl u)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl u) => .inr (.inr u)
    | .inr (.inr l) => .inl l
  left_inv k := by rcases k with k | (k | k) <;> rfl
  right_inv k := by rcases k with k | (k | k) <;> rfl

def innerControl : IControl × (OControl × Option Bool) ≃ Control where
  toFun := fun v => (v.2.1,(v.1,v.2.2))
  invFun := fun v => (v.2.1,(v.1,v.2.2))
  left_inv v := by rcases v with ⟨_,⟨_,_⟩⟩; rfl
  right_inv v := by rcases v with ⟨_,⟨_,_⟩⟩; rfl

noncomputable def duplicate : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop qSource (fun v b => (v.1,(v.2.1,b)))
    (branch (fun v => v.2.2.isSome)
      (push qRestTarget (fun _ => true)
        (push qFirstTarget (fun _ => true)
          (goto (fun _ => bridgeStart))))
      (load (fun v => (v.1,(v.2.1,none)))
        (goto (fun _ => innerStart))))

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inl ()))
      (MatrixOuterWidthMachine.machine.program l)
  | .inr (.inl ()) => duplicate
  | .inr (.inr l) => renameStmt
      (Equiv.sumComm IStack OStack) innerLabels innerControl
      (liftStmt none (MatrixTableInterlaceScalarJoin.program l))

noncomputable def run (t : ℕ) (c : Config) : Config :=
  ((advance program)^[t]) c

noncomputable def outerFrame (d : MatrixTableInterlaceScalarJoin.Config)
    (c : MatrixOuterWidthMachine.Config) : Config :=
  liftCfg (some (.inl ())) (d.var,none) d.stk c

noncomputable def innerFrame (c : MatrixOuterWidthMachine.Config)
    (d : MatrixTableInterlaceScalarJoin.Config) : Config :=
  renameCfg (Equiv.sumComm IStack OStack) innerLabels innerControl
    (liftCfg none (c.var,none) c.stk d)

theorem outer_phase (lambda : ℕ)
    (d : MatrixTableInterlaceScalarJoin.Config) :
    ∃ t ≤ MatrixOuterWidthMachine.totalTime lambda,
      ∃ cf : MatrixOuterWidthMachine.Config,
        run t (outerFrame d (MatrixOuterWidthMachine.startCfg lambda)) =
          outerFrame d cf ∧
        cf.l = none ∧
        cf.stk MatrixOuterWidthMachine.outputStack =
          List.replicate (MatrixOuterWidthMachine.width lambda) true := by
  obtain ⟨t,ht,cf,hr,hh,ho⟩ := MatrixOuterWidthMachine.width_run lambda
  have hhalt : (MatrixOuterWidthMachine.machine.run t
      (MatrixOuterWidthMachine.startCfg lambda)).l = none := by
    rw [hr]
    exact hh
  obtain ⟨u,hu,he⟩ := lift_outputs
    MatrixOuterWidthMachine.machine.program program (some (.inl ()))
    (fun _ => rfl) (d.var,none) d.stk
    (MatrixOuterWidthMachine.startCfg lambda) t hhalt
  change run u (outerFrame d _) = outerFrame d
    (MatrixOuterWidthMachine.machine.run t _) at he
  rw [hr] at he
  exact ⟨u,hu.trans ht,cf,he,hh,ho⟩

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem duplicate_cons (v : OControl) (w : IControl)
    (o : Option Bool) (S : Stack → List Bool) (n : ℕ)
    (hs : S qSource = true :: List.replicate n true) :
    run 1 ⟨some bridgeStart,(v,(w,o)),S⟩ =
      ⟨some bridgeStart,(v,(w,some true)),
        Function.update
          (Function.update
            (Function.update S qSource (List.replicate n true))
            qRestTarget (true :: S qRestTarget))
          qFirstTarget (true :: S qFirstTarget)⟩ := by
  simp [run,advance,TM2.step,TM2.stepAux,program,duplicate,
    bridgeStart,innerStart,hs]
  funext k
  by_cases hf : k = qFirstTarget
  · subst k
    simp [Function.update_apply,qSource,qRestTarget,qFirstTarget]
  · by_cases hr : k = qRestTarget
    · subst k
      simp [Function.update_apply,qSource,qRestTarget,qFirstTarget,hf]
    · simp [Function.update_apply,qSource,qRestTarget,qFirstTarget,hr,hf]

private theorem duplicate_nil (v : OControl) (w : IControl)
    (o : Option Bool) (S : Stack → List Bool)
    (hs : S qSource = []) :
    run 1 ⟨some bridgeStart,(v,(w,o)),S⟩ =
      ⟨some innerStart,(v,(w,none)),S⟩ := by
  have hu : Function.update S qSource [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run,advance,TM2.step,TM2.stepAux,program,duplicate,
    bridgeStart,innerStart,hs,hu]

noncomputable def duplicated (S : Stack → List Bool) (n : ℕ) :
    Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update S qSource [])
      qRestTarget (List.replicate n true ++ S qRestTarget))
    qFirstTarget (List.replicate n true ++ S qFirstTarget)

theorem duplicate_run (v : OControl) (w : IControl)
    (o : Option Bool) (n : ℕ) (S : Stack → List Bool)
    (hs : S qSource = List.replicate n true) :
    run (n+1) ⟨some bridgeStart,(v,(w,o)),S⟩ =
      ⟨some innerStart,(v,(w,none)),duplicated S n⟩ := by
  induction n generalizing S o with
  | zero =>
      have hn := duplicate_nil v w o S (by simpa using hs)
      have hu1 : Function.update S qSource [] = S :=
        Function.update_eq_self_iff.mpr (by simpa using hs.symm)
      have hu2 : Function.update S qRestTarget (S qRestTarget) = S :=
        Function.update_eq_self_iff.mpr rfl
      have hu3 : Function.update S qFirstTarget (S qFirstTarget) = S :=
        Function.update_eq_self_iff.mpr rfl
      simpa only [duplicated,List.replicate_zero,List.nil_append,
        hu1,hu2,hu3] using hn
  | succ n ih =>
      let S' := Function.update
        (Function.update
          (Function.update S qSource (List.replicate n true))
          qRestTarget (true :: S qRestTarget))
        qFirstTarget (true :: S qFirstTarget)
      have hs' : S' qSource = List.replicate n true := by
        simp [S',qSource,qRestTarget,qFirstTarget]
      have h1 := duplicate_cons v w o S n hs
      have h2 := (run_add h1 (n+1)).trans (ih (some true) S' hs')
      have hupdate : duplicated S' n = duplicated S (n+1) := by
        funext k
        by_cases hf : k = qFirstTarget
        · subst k
          simp [duplicated,S',qSource,qRestTarget,qFirstTarget,
            List.replicate_add,List.append_assoc]
        · by_cases hr : k = qRestTarget
          · subst k
            simp [duplicated,S',qSource,qRestTarget,qFirstTarget,
              hf,List.replicate_add,List.append_assoc]
          · by_cases hsrc : k = qSource
            · subst k
              simp [duplicated,S',qSource,qRestTarget,qFirstTarget,
                hf,hr]
            · simp [duplicated,S',Function.update_apply,hf,hr,hsrc]
      rw [hupdate] at h2
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using h2

noncomputable def restSlot : IStack :=
  .inl (MatrixRestorationWidthMachine.inputStack 3)
def firstBlock : MatrixTableInterlaceDouble.Stack :=
  .inl (.inl (.inl (.inl 0)))
def firstSlot : IStack := .inr firstBlock

theorem rest_start_other (b c s q : ℕ)
    (k : MatrixRestorationWidthMachine.Stack)
    (hk : k ≠ MatrixRestorationWidthMachine.inputStack 3) :
    (MatrixRestorationWidthMachine.startCfg b c s q).stk k =
      (MatrixRestorationWidthMachine.startCfg b c s 0).stk k := by
  have hbank (j : Fin 12) (hj : j ≠ 3) :
      MatrixRestorationWidthMachineProduct.inputBank b c s q j =
        MatrixRestorationWidthMachineProduct.inputBank b c s 0 j := by
    fin_cases j <;>
      simp [MatrixRestorationWidthMachineProduct.inputBank] at *
  cases k with
  | inl k =>
      change MatrixRestorationWidthMachineProduct.inputBank b c s q
          ((Fintype.equivFin (Fin 12)).symm k) =
        MatrixRestorationWidthMachineProduct.inputBank b c s 0
          ((Fintype.equivFin (Fin 12)).symm k)
      let j : Fin 12 := (Fintype.equivFin (Fin 12)).symm k
      change MatrixRestorationWidthMachineProduct.inputBank b c s q j =
        MatrixRestorationWidthMachineProduct.inputBank b c s 0 j
      have hj : j ≠ 3 := by
        intro he
        apply hk
        change Sum.inl k = Sum.inl ((Fintype.equivFin (Fin 12)) 3)
        have he' := congrArg (Fintype.equivFin (Fin 12)) he
        simpa only [j,Equiv.apply_symm_apply] using
          congrArg Sum.inl he'
      exact hbank j hj
  | inr k =>
      rfl

noncomputable def readyInner (B r rows cols b c s q : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    MatrixTableInterlaceScalarJoin.Config :=
  MatrixTableInterlaceScalarJoin.restorationFrame
    (MatrixTableInterlaceScalarJoin.emptyDouble B r rows cols f)
    (MatrixRestorationWidthMachine.startCfg b c s q)

noncomputable def emptyInner (B r rows cols b c s : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    MatrixTableInterlaceScalarJoin.Config :=
  let d := readyInner B r rows cols b c s 0 f
  ⟨d.l,d.var,Function.update d.stk firstSlot []⟩

theorem firstBlock_ready (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (MatrixTableInterlaceScalarJoin.emptyDouble B r rows cols f).stk
      firstBlock = List.replicate (2^r) true := rfl

theorem emptyInner_rest (B r rows cols b c s : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (emptyInner B r rows cols b c s f).stk restSlot = [] := by
  change (Function.update (readyInner B r rows cols b c s 0 f).stk
      firstSlot []) restSlot = []
  have hne : restSlot ≠ firstSlot := by
    simp [restSlot,firstSlot]
  simp only [Function.update_apply,if_neg hne]
  change (MatrixRestorationWidthMachine.startCfg b c s 0).stk
    (MatrixRestorationWidthMachine.inputStack 3) = []
  simpa only [MatrixRestorationWidthMachine.unary,List.replicate_zero] using
    MatrixRestorationWidthMachine.startCfg_input b c s 0 3

theorem emptyInner_first (B r rows cols b c s : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (emptyInner B r rows cols b c s f).stk firstSlot = [] := by
  simp [emptyInner,firstSlot]

theorem readyInner_rest (B r rows cols b c s q : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (readyInner B r rows cols b c s q f).stk restSlot =
      List.replicate q true := by
  change (MatrixRestorationWidthMachine.startCfg b c s q).stk
    (MatrixRestorationWidthMachine.inputStack 3) = _
  exact MatrixRestorationWidthMachine.startCfg_input b c s q 3

theorem readyInner_first (B r rows cols b c s q : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (readyInner B r rows cols b c s q f).stk firstSlot =
      List.replicate (2^r) true :=
  firstBlock_ready B r rows cols f

theorem inner_other (B r rows cols b c s q : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (k : IStack) (hr : k ≠ restSlot) (hf : k ≠ firstSlot) :
    (emptyInner B r rows cols b c s f).stk k =
      (readyInner B r rows cols b c s q f).stk k := by
  change (Function.update (readyInner B r rows cols b c s 0 f).stk
    firstSlot []) k = (readyInner B r rows cols b c s q f).stk k
  simp only [Function.update_apply,if_neg hf]
  cases k with
  | inl k =>
      have hk : k ≠ MatrixRestorationWidthMachine.inputStack 3 := by
        intro he
        apply hr
        exact congrArg Sum.inl he
      change (MatrixRestorationWidthMachine.startCfg b c s 0).stk k =
        (MatrixRestorationWidthMachine.startCfg b c s q).stk k
      exact (rest_start_other b c s q k hk).symm
  | inr k =>
      rfl

noncomputable def clearedOuter (cf : MatrixOuterWidthMachine.Config) :
    MatrixOuterWidthMachine.Config :=
  ⟨cf.l,cf.var,Function.update cf.stk
    MatrixOuterWidthMachine.outputStack []⟩

set_option maxRecDepth 4096 in
theorem bridge_bank (B r rows cols b c s : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (cf : MatrixOuterWidthMachine.Config)
    (ho : cf.stk MatrixOuterWidthMachine.outputStack =
      List.replicate (2^r) true) :
    duplicated (outerFrame (emptyInner B r rows cols b c s f) cf).stk
      (2^r) =
        (innerFrame (clearedOuter cf)
          (readyInner B r rows cols b c s (2^r) f)).stk := by
  have hsource : qSource = .inl MatrixOuterWidthMachine.outputStack := rfl
  have hrest : qRestTarget = .inr restSlot := rfl
  have hfirst : qFirstTarget = .inr firstSlot := rfl
  have hdiff : restSlot ≠ firstSlot := by simp [restSlot,firstSlot]
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = MatrixOuterWidthMachine.outputStack
      · subst k
        simp only [duplicated,outerFrame,innerFrame,clearedOuter,
          renameCfg,liftCfg,hsource,hrest,hfirst,Function.update_apply]
        change _ = (Function.update cf.stk
          MatrixOuterWidthMachine.outputStack [])
          MatrixOuterWidthMachine.outputStack
        simp only [Sum.inl_ne_inr,if_false,if_true,
          Function.update_apply]
      · simp only [duplicated,outerFrame,innerFrame,clearedOuter,
          renameCfg,liftCfg,hsource,hrest,hfirst,Function.update_apply]
        change _ = (Function.update cf.stk
          MatrixOuterWidthMachine.outputStack []) k
        simp only [Sum.inl_ne_inr,Sum.inl.injEq,hk,
          if_false,Sum.elim_inl,Function.update_apply]
  | inr k =>
      by_cases hr : k = restSlot
      · subst k
        simp only [duplicated,outerFrame,innerFrame,clearedOuter,
          renameCfg,liftCfg,hsource,hrest,hfirst,Function.update_apply]
        change _ = (readyInner B r rows cols b c s (2^r) f).stk restSlot
        simp only [Sum.inr.injEq,hdiff,if_false,if_true,Sum.elim_inr]
        rw [emptyInner_rest,readyInner_rest]
        simp
      · by_cases hf : k = firstSlot
        · subst k
          simp only [duplicated,outerFrame,innerFrame,clearedOuter,
            renameCfg,liftCfg,hsource,hrest,hfirst,Function.update_apply]
          change _ = (readyInner B r rows cols b c s (2^r) f).stk firstSlot
          simp only [if_true,Sum.elim_inr]
          rw [emptyInner_first,readyInner_first]
          simp
        · simp only [duplicated,outerFrame,innerFrame,clearedOuter,
            renameCfg,liftCfg,hsource,hrest,hfirst,Function.update_apply]
          change _ = (readyInner B r rows cols b c s (2^r) f).stk k
          simp only [Sum.inr.injEq,hr,hf,if_false,
            Sum.inr_ne_inl,Sum.elim_inr]
          exact inner_other B r rows cols b c s (2^r) f k hr hf

theorem bridge_run (B r rows cols b c s : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (cf : MatrixOuterWidthMachine.Config)
    (hh : cf.l = none)
    (ho : cf.stk MatrixOuterWidthMachine.outputStack =
      List.replicate (2^r) true) :
    run ((2^r)+1)
      (outerFrame (emptyInner B r rows cols b c s f) cf) =
      innerFrame (clearedOuter cf)
        (readyInner B r rows cols b c s (2^r) f) := by
  let d := emptyInner B r rows cols b c s f
  let S := (outerFrame d cf).stk
  have hs : S qSource = List.replicate (2^r) true := by
    change cf.stk MatrixOuterWidthMachine.outputStack = _
    exact ho
  have hdup := duplicate_run cf.var d.var none (2^r) S hs
  have hstart : outerFrame d cf =
      (⟨some bridgeStart,(cf.var,(d.var,none)),S⟩ : Config) := by
    cases cf with
    | mk l var stk =>
        cases l <;> simp_all [outerFrame,liftCfg,d,S,bridgeStart]
  rw [hstart,hdup]
  have hbank := bridge_bank B r rows cols b c s f cf ho
  change (⟨some innerStart,(cf.var,(d.var,none)),duplicated S (2^r)⟩ :
    Config) = innerFrame (clearedOuter cf)
      (readyInner B r rows cols b c s (2^r) f)
  congr 1

theorem inner_phase (R r rows cols b c s : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (cf : MatrixOuterWidthMachine.Config)
    (hB : MatrixRestorationWidthMachine.width b c s (2^r) = 2^R)
    (hfirst : 0 < rows * (cols ^ (2^r)))
    (hsecond : 0 < MatrixTableInterlaceDouble.firstColsCount r cols *
      ((MatrixTableInterlaceDouble.firstRowsCount r rows) ^ (2^R))) :
    ∃ t ≤ MatrixTableInterlaceScalarJoin.totalBound R r rows cols
        b c s (2^r) f,
      ∃ d : MatrixTableInterlaceScalarJoin.Config,
        run t (innerFrame cf (readyInner (2^R) r rows cols
          b c s (2^r) f)) = innerFrame cf d ∧
        d.l = none ∧
        d.stk MatrixTableInterlaceScalarJoin.secondOutput =
          MatrixMaterialization.rowMajor
            (MatrixTableInterlaceDouble.secondResult R r rows cols f) := by
  obtain ⟨t,ht,d,he,hh,ho⟩ :=
    MatrixTableInterlaceScalarJoin.restoration_join_run R r rows cols
      b c s (2^r) f hB hfirst hsecond
  have hhe : MatrixTableInterlaceScalarJoin.run t
      (readyInner (2^R) r rows cols b c s (2^r) f) = d := by
    simpa only [readyInner] using he
  have hhalt : (MatrixTableInterlaceScalarJoin.run t
      (readyInner (2^R) r rows cols b c s (2^r) f)).l = none := by
    rw [hhe]
    exact hh
  obtain ⟨u,hu,hr⟩ := lift_outputs_renamed
    (Equiv.sumComm IStack OStack) innerLabels innerControl
    MatrixTableInterlaceScalarJoin.program program none (fun _ => rfl)
    (cf.var,none) cf.stk
    (readyInner (2^R) r rows cols b c s (2^r) f) t hhalt
  change run u (innerFrame cf _) = innerFrame cf
    (MatrixTableInterlaceScalarJoin.run t _) at hr
  rw [hhe] at hr
  exact ⟨u,hu.trans ht,d,hr,hh,ho⟩

noncomputable def totalBound (R r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  MatrixOuterWidthMachine.totalTime lambda +
    ((2^r)+1) +
    MatrixTableInterlaceScalarJoin.totalBound R r rows cols
      b c s (2^r) f

def secondOutput : Stack :=
  .inr MatrixTableInterlaceScalarJoin.secondOutput

theorem outer_join_run (R r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hq : MatrixOuterWidthMachine.width lambda = 2^r)
    (hB : MatrixRestorationWidthMachine.width b c s (2^r) = 2^R)
    (hfirst : 0 < rows * (cols ^ (2^r)))
    (hsecond : 0 < MatrixTableInterlaceDouble.firstColsCount r cols *
      ((MatrixTableInterlaceDouble.firstRowsCount r rows) ^ (2^R))) :
    ∃ t ≤ totalBound R r rows cols b c s lambda f,
      ∃ z : Config,
        run t (outerFrame (emptyInner (2^R) r rows cols b c s f)
          (MatrixOuterWidthMachine.startCfg lambda)) = z ∧
        z.l = none ∧
        z.stk secondOutput =
          MatrixMaterialization.rowMajor
            (MatrixTableInterlaceDouble.secondResult R r rows cols f) := by
  obtain ⟨t₁,ht₁,cf,h₁,hh,ho⟩ := outer_phase lambda
    (emptyInner (2^R) r rows cols b c s f)
  have ho' : cf.stk MatrixOuterWidthMachine.outputStack =
      List.replicate (2^r) true := by simpa only [hq] using ho
  have hbridge := bridge_run (2^R) r rows cols b c s f cf hh ho'
  obtain ⟨t₂,ht₂,d,h₂,hd,hout⟩ := inner_phase R r rows cols
    b c s f (clearedOuter cf) hB hfirst hsecond
  have h₁₂ := run_add h₁ ((2^r)+1)
  rw [hbridge] at h₁₂
  have h₁₂₃ := run_add h₁₂ t₂
  rw [h₂] at h₁₂₃
  let z := innerFrame (clearedOuter cf) d
  refine ⟨t₁+((2^r)+1)+t₂, ?_,z,h₁₂₃,?_,?_⟩
  · dsimp [totalBound]
    omega
  · simp [z,innerFrame,renameCfg,liftCfg,hd]
  · change d.stk MatrixTableInterlaceScalarJoin.secondOutput = _
    exact hout

def scale (R r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  lambda+(2^r)+
    MatrixTableInterlaceScalarJoin.scale R r rows cols b c s (2^r) f+1

theorem totalBound_polynomial (R r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hq : MatrixOuterWidthMachine.width lambda = 2^r)
    (hB : MatrixRestorationWidthMachine.width b c s (2^r) = 2^R) :
    totalBound R r rows cols b c s lambda f ≤
      (16194+4*UnaryBinaryEncoding.coefficient) *
        (scale R r rows cols b c s lambda f)^4 := by
  let N := scale R r rows cols b c s lambda f
  have hN : 1 ≤ N := by dsimp [N,scale]; omega
  have hN2 : N ≤ N^2 := by
    nlinarith [Nat.mul_le_mul (le_refl N) hN]
  have hN4 : N^2 ≤ N^4 := by
    have h : 1 ≤ N^2 := by nlinarith
    nlinarith [Nat.mul_le_mul (le_refl (N^2)) h]
  have hNto4 : N ≤ N^4 := by omega
  have hOuterScale : lambda+MatrixOuterWidthMachine.width lambda+1 ≤ N := by
    rw [hq]
    dsimp [N,scale]
    omega
  have hInnerScale : MatrixTableInterlaceScalarJoin.scale R r rows cols
      b c s (2^r) f ≤ N := by
    dsimp [N,scale]
    omega
  have houter := MatrixOuterWidthMachine.totalTime_output_poly lambda
  dsimp only at houter
  have houter' : MatrixOuterWidthMachine.totalTime lambda ≤ 5000*N^4 := by
    calc
      _ ≤ 5000*(lambda+MatrixOuterWidthMachine.width lambda+1)^2 := houter
      _ ≤ 5000*N^2 := Nat.mul_le_mul_left 5000
        (Nat.pow_le_pow_left hOuterScale 2)
      _ ≤ _ := Nat.mul_le_mul_left 5000 hN4
  have hinner := MatrixTableInterlaceScalarJoin.totalBound_polynomial
    R r rows cols b c s (2^r) f hB
  have hinner' : MatrixTableInterlaceScalarJoin.totalBound R r rows cols
      b c s (2^r) f ≤
        (11193+4*UnaryBinaryEncoding.coefficient)*N^4 :=
    hinner.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left hInnerScale 4))
  have hqsmall : (2^r)+1 ≤ N := by dsimp [N,scale]; omega
  change MatrixOuterWidthMachine.totalTime lambda +
    ((2^r)+1) +
    MatrixTableInterlaceScalarJoin.totalBound R r rows cols
      b c s (2^r) f ≤
        (16194+4*UnaryBinaryEncoding.coefficient)*N^4
  calc
    _ ≤ 5000*N^4+N^4+
        (11193+4*UnaryBinaryEncoding.coefficient)*N^4 := by omega
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
theorem outer_step_run {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (sourceConstant b y i : ℕ) (M : Iteration.Matrix) :
    let P := Iteration.stepParameters G sourceConstant b y i M
    let R := Iteration.rQ G sourceConstant b y i M
    let r := Iteration.rq G sourceConstant b y i M
    let rows := (Iteration.nRowNumbering G sourceConstant b y i M).size
    let cols := (Iteration.nColNumbering G sourceConstant b y i M).size
    let f := MatrixTableInterlaceLevelCodes.numericSource
      (Iteration.protectedMatrix G sourceConstant b y i M)
      (Iteration.nRowNumbering G sourceConstant b y i M)
      (Iteration.nColNumbering G sourceConstant b y i M)
    ∃ t ≤ (16194+4*UnaryBinaryEncoding.coefficient) *
        (scale R r rows cols P.nextDepth P.sourceConstant
          (Parameters.bins P) (Parameters.scale P) f)^4,
      ∃ z : Config,
        run t (outerFrame
          (emptyInner (2^R) r rows cols P.nextDepth P.sourceConstant
            (Parameters.bins P) f)
          (MatrixOuterWidthMachine.startCfg (Parameters.scale P))) = z ∧
        z.l = none ∧
        z.stk secondOutput =
          MatrixMaterialization.rowMajor
            (Iteration.step G sourceConstant b y i M).entry := by
  dsimp only
  let P := Iteration.stepParameters G sourceConstant b y i M
  let R := Iteration.rQ G sourceConstant b y i M
  let r := Iteration.rq G sourceConstant b y i M
  let rows := (Iteration.nRowNumbering G sourceConstant b y i M).size
  let cols := (Iteration.nColNumbering G sourceConstant b y i M).size
  let f := MatrixTableInterlaceLevelCodes.numericSource
    (Iteration.protectedMatrix G sourceConstant b y i M)
    (Iteration.nRowNumbering G sourceConstant b y i M)
    (Iteration.nColNumbering G sourceConstant b y i M)
  have hq : MatrixOuterWidthMachine.width (Parameters.scale P) = 2^r := by
    change MatrixOuterWidthMachine.width (Parameters.scale P) =
      Parameters.outerWidth P
    exact MatrixOuterWidthMachine.width_eq_parameters P
  have hB : MatrixRestorationWidthMachine.width P.nextDepth
      P.sourceConstant (Parameters.bins P) (2^r) = 2^R := by
    have h := MatrixRestorationWidthMachine.width_eq_parameters P
    change MatrixRestorationWidthMachine.width P.nextDepth
      P.sourceConstant (Parameters.bins P)
      (MatrixOuterWidthMachine.width (Parameters.scale P)) = 2^R at h
    simpa only [hq] using h
  have hr : 0 < rows :=
    (Iteration.nRowNumbering G sourceConstant b y i M).size_pos
  have hc : 0 < cols :=
    (Iteration.nColNumbering G sourceConstant b y i M).size_pos
  have hfirst : 0 < rows * (cols ^ (2^r)) := by positivity
  have hsecond : 0 < MatrixTableInterlaceDouble.firstColsCount r cols *
      ((MatrixTableInterlaceDouble.firstRowsCount r rows) ^ (2^R)) := by
    dsimp [MatrixTableInterlaceDouble.firstColsCount,
      MatrixTableInterlaceDouble.firstRowsCount]
    positivity
  have hfun : MatrixTableInterlaceDouble.secondResult R r rows cols f =
      (Iteration.step G sourceConstant b y i M).entry := by
    funext x z
    exact (MatrixTableInterlaceDouble.secondResult_step_entry
      G sourceConstant b y i M x z).symm
  obtain ⟨t,ht,z,he,hh,ho⟩ := outer_join_run R r rows cols
    P.nextDepth P.sourceConstant (Parameters.bins P)
    (Parameters.scale P) f hq hB hfirst hsecond
  refine ⟨t,ht.trans (totalBound_polynomial R r rows cols
    P.nextDepth P.sourceConstant (Parameters.bins P)
    (Parameters.scale P) f hq hB),z,he,hh,?_⟩
  simpa only [hfun] using ho

end EthInapproximability.CurrentPaper.MatrixTableInterlaceOuterJoin
