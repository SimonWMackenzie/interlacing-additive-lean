import EthInapproximability.CurrentPaper.MatrixTableInterlaceDouble
import EthInapproximability.CurrentPaper.MatrixRestorationWidthMachine

/-!
# Charged scalar handoff to the literal double restoration

This owner joins physical unary parameter producers to the frozen double
controller. The protected-table source and first-pass dimension headers remain
explicit input banks.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceScalarJoin

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev RStack := MatrixRestorationWidthMachine.Stack
abbrev DStack := MatrixTableInterlaceDouble.Stack
abbrev Stack := RStack ⊕ DStack
abbrev RLabel := MatrixRestorationWidthMachine.Label
abbrev DLabel := MatrixTableInterlaceDouble.Label
abbrev Label := RLabel ⊕ (Unit ⊕ DLabel)
abbrev RControl := MatrixRestorationWidthMachine.Control
abbrev DControl := MatrixTableInterlaceDouble.Control
abbrev Control := RControl × (DControl × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable def qSource : Stack :=
  .inl MatrixRestorationWidthMachine.outputStack
def qTarget : Stack := .inr MatrixTableInterlaceDouble.blockInput
def bridgeStart : Label := .inr (.inl ())
def doubleStart : Label := .inr (.inr MatrixTableInterlaceDouble.start)

def doubleLabels : DLabel ⊕ (RLabel ⊕ Unit) ≃ Label where
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

def doubleControl : DControl × (RControl × Option Bool) ≃ Control where
  toFun := fun v => (v.2.1,(v.1,v.2.2))
  invFun := fun v => (v.2.1,(v.1,v.2.2))
  left_inv v := by rcases v with ⟨_,⟨_,_⟩⟩; rfl
  right_inv v := by rcases v with ⟨_,⟨_,_⟩⟩; rfl

noncomputable def move : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop qSource (fun v b => (v.1,(v.2.1,b)))
    (branch (fun v => v.2.2.isSome)
      (push qTarget (fun _ => true) (goto (fun _ => bridgeStart)))
      (load (fun v => (v.1,(v.2.1,none)))
        (goto (fun _ => doubleStart))))

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inl ()))
      (MatrixRestorationWidthMachine.program l)
  | .inr (.inl ()) => move
  | .inr (.inr l) => renameStmt
      (Equiv.sumComm DStack RStack) doubleLabels doubleControl
      (liftStmt none (MatrixTableInterlaceDouble.program l))

noncomputable def run (t : ℕ) (c : Config) : Config :=
  ((advance program)^[t]) c

noncomputable def restorationFrame (d : MatrixTableInterlaceDouble.Config)
    (c : MatrixRestorationWidthMachine.Config) : Config :=
  liftCfg (some (.inl ())) (d.var,none) d.stk c

noncomputable def doubleFrame (c : MatrixRestorationWidthMachine.Config)
    (d : MatrixTableInterlaceDouble.Config) : Config :=
  renameCfg (Equiv.sumComm DStack RStack) doubleLabels doubleControl
    (liftCfg none (c.var,none) c.stk d)

theorem restoration_phase (b c s q : ℕ)
    (d : MatrixTableInterlaceDouble.Config) :
    ∃ t ≤ MatrixRestorationWidthMachine.totalTime b c s q,
      ∃ cf : MatrixRestorationWidthMachine.Config,
        run t (restorationFrame d
          (MatrixRestorationWidthMachine.startCfg b c s q)) =
        restorationFrame d cf ∧
        cf.l = none ∧
        cf.stk MatrixRestorationWidthMachine.outputStack =
          List.replicate (MatrixRestorationWidthMachine.width b c s q) true := by
  obtain ⟨t,ht,v,hv,cf,hr,_,hh,ho⟩ :=
    MatrixRestorationWidthMachine.width_run b c s q
  have hhalt :
      (((advance MatrixRestorationWidthMachine.program)^[t])
        (MatrixRestorationWidthMachine.startCfg b c s q)).l = none := by
    rw [hr]
    exact hh
  obtain ⟨u,hu,he⟩ := lift_outputs
    MatrixRestorationWidthMachine.program program (some (.inl ()))
    (fun _ => rfl) (d.var,none) d.stk
    (MatrixRestorationWidthMachine.startCfg b c s q) t hhalt
  change run u (restorationFrame d _) = restorationFrame d
    (((advance MatrixRestorationWidthMachine.program)^[t])
      (MatrixRestorationWidthMachine.startCfg b c s q)) at he
  rw [hr] at he
  exact ⟨u,hu.trans ht,cf,he,hh,ho⟩

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem move_cons (v : RControl) (w : DControl)
    (o : Option Bool) (S : Stack → List Bool)
    (bits : List Bool)
    (hs : S qSource = true :: bits) :
    run 1 ⟨some bridgeStart,(v,(w,o)),S⟩ =
      ⟨some bridgeStart,(v,(w,some true)),
        Function.update (Function.update S qSource bits)
          qTarget (true :: S qTarget)⟩ := by
  simp [run,advance,TM2.step,TM2.stepAux,program,move,
    bridgeStart,doubleStart,hs]
  simp [Function.update_apply,qSource,qTarget]

private theorem move_nil (v : RControl) (w : DControl)
    (o : Option Bool) (S : Stack → List Bool)
    (hs : S qSource = []) :
    run 1 ⟨some bridgeStart,(v,(w,o)),S⟩ =
      ⟨some doubleStart,(v,(w,none)),S⟩ := by
  have hu : Function.update S qSource [] = S :=
    Function.update_eq_self_iff.mpr hs.symm
  simp [run,advance,TM2.step,TM2.stepAux,program,move,
    bridgeStart,doubleStart,hs,hu]

noncomputable def moved (S : Stack → List Bool) (n : ℕ) :
    Stack → List Bool :=
  Function.update (Function.update S qSource []) qTarget
    (List.replicate n true ++ S qTarget)

theorem move_run (v : RControl) (w : DControl)
    (o : Option Bool) (n : ℕ) (S : Stack → List Bool)
    (hs : S qSource = List.replicate n true) :
    run (n+1) ⟨some bridgeStart,(v,(w,o)),S⟩ =
      ⟨some doubleStart,(v,(w,none)),moved S n⟩ := by
  induction n generalizing S o with
  | zero =>
      have hn := move_nil v w o S (by simpa using hs)
      have hu1 : Function.update S qSource [] = S :=
        Function.update_eq_self_iff.mpr (by simpa using hs.symm)
      have hu2 : Function.update S qTarget (S qTarget) = S :=
        Function.update_eq_self_iff.mpr rfl
      simpa only [moved,List.replicate_zero,List.nil_append,hu1,hu2] using hn
  | succ n ih =>
      let S' := Function.update (Function.update S qSource
        (List.replicate n true)) qTarget (true :: S qTarget)
      have hs' : S' qSource = List.replicate n true := by
        simp [S',qSource,qTarget]
      have h1 := move_cons v w o S (List.replicate n true) hs
      have h2 := (run_add h1 (n+1)).trans (ih (some true) S' hs')
      have hupdate : moved S' n = moved S (n+1) := by
        funext k
        by_cases ht : k = qTarget
        · subst k
          simp [moved,S',qSource,qTarget,List.replicate_add,
            List.append_assoc]
        · by_cases hsrc : k = qSource
          · subst k
            simp [moved,S',qSource,qTarget,ht]
          · simp [moved,S',Function.update_apply,ht,hsrc]
      rw [hupdate] at h2
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using h2

def emptyDouble (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : MatrixTableInterlaceDouble.Config :=
  MatrixTableInterlaceDouble.firstFrame
    (MatrixTableInterlaceDouble.secondPrepared B r rows cols f).var
    (MatrixTableInterlaceDouble.initialForeign 0)
    (MatrixTableInterlaceDouble.firstPrepared r rows cols f)

def readyDouble (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : MatrixTableInterlaceDouble.Config :=
  MatrixTableInterlaceDouble.firstFrame
    (MatrixTableInterlaceDouble.secondPrepared B r rows cols f).var
    (MatrixTableInterlaceDouble.initialForeign B)
    (MatrixTableInterlaceDouble.firstPrepared r rows cols f)

theorem emptyDouble_var (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (emptyDouble B r rows cols f).var =
      (readyDouble B r rows cols f).var := rfl

theorem emptyDouble_target (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (emptyDouble B r rows cols f).stk
      MatrixTableInterlaceDouble.blockInput = [] := by
  simp [emptyDouble,MatrixTableInterlaceDouble.firstFrame,
    MatrixTableInterlaceDouble.initialForeign,liftCfg,
    MatrixTableInterlaceDouble.blockInput]

theorem readyDouble_target (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (readyDouble B r rows cols f).stk
      MatrixTableInterlaceDouble.blockInput = List.replicate B true := by
  simp [readyDouble,MatrixTableInterlaceDouble.firstFrame,
    MatrixTableInterlaceDouble.initialForeign,liftCfg,
    MatrixTableInterlaceDouble.blockInput]

theorem double_other (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (k : DStack) (hk : k ≠ MatrixTableInterlaceDouble.blockInput) :
    (emptyDouble B r rows cols f).stk k =
      (readyDouble B r rows cols f).stk k := by
  cases k with
  | inl k => rfl
  | inr k =>
      cases k with
      | inl k => rfl
      | inr k =>
          fin_cases k
          simp [MatrixTableInterlaceDouble.blockInput] at hk

noncomputable def clearedRestoration
    (cf : MatrixRestorationWidthMachine.Config) :
    MatrixRestorationWidthMachine.Config :=
  ⟨cf.l,cf.var,Function.update cf.stk
    MatrixRestorationWidthMachine.outputStack []⟩

set_option maxRecDepth 4096 in
theorem bridge_bank (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (cf : MatrixRestorationWidthMachine.Config)
    (ho : cf.stk MatrixRestorationWidthMachine.outputStack =
      List.replicate B true) :
    moved (restorationFrame (emptyDouble B r rows cols f) cf).stk B =
      (doubleFrame (clearedRestoration cf)
        (readyDouble B r rows cols f)).stk := by
  have hsource : qSource = .inl MatrixRestorationWidthMachine.outputStack := rfl
  have htarget : qTarget = .inr MatrixTableInterlaceDouble.blockInput := rfl
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = MatrixRestorationWidthMachine.outputStack
      · subst k
        simp only [moved,restorationFrame,doubleFrame,clearedRestoration,
          renameCfg,liftCfg,Equiv.sumComm_apply]
        simp only [hsource,htarget,Function.update_apply]
        change _ = (Function.update cf.stk
          MatrixRestorationWidthMachine.outputStack [])
          MatrixRestorationWidthMachine.outputStack
        simp only [Sum.inl_ne_inr,if_false,if_true,
          Function.update_apply]
      · simp only [moved,restorationFrame,doubleFrame,clearedRestoration,
          renameCfg,liftCfg,Equiv.sumComm_apply]
        simp only [hsource,htarget,Function.update_apply]
        change _ = (Function.update cf.stk
          MatrixRestorationWidthMachine.outputStack []) k
        simp only [Sum.inl_ne_inr,Sum.inl.injEq,hk,
          if_false,Sum.elim_inl,Function.update_apply]
  | inr k =>
      by_cases hk : k = MatrixTableInterlaceDouble.blockInput
      · subst k
        simp only [moved,restorationFrame,doubleFrame,clearedRestoration,
          renameCfg,liftCfg,Equiv.sumComm_apply]
        simp only [hsource,htarget,Function.update_apply]
        change _ = (readyDouble B r rows cols f).stk
          MatrixTableInterlaceDouble.blockInput
        simp only [if_true,Sum.elim_inr]
        rw [emptyDouble_target,readyDouble_target]
        simp
      · simp only [moved,restorationFrame,doubleFrame,clearedRestoration,
          renameCfg,liftCfg,Equiv.sumComm_apply]
        simp only [hsource,htarget,Function.update_apply]
        change _ = (readyDouble B r rows cols f).stk k
        simp only [Sum.inr.injEq,hk,if_false,Sum.inr_ne_inl,
          Sum.elim_inr]
        exact double_other B r rows cols f k hk

theorem bridge_run (B r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (cf : MatrixRestorationWidthMachine.Config)
    (hh : cf.l = none)
    (ho : cf.stk MatrixRestorationWidthMachine.outputStack =
      List.replicate B true) :
    run (B+1) (restorationFrame (emptyDouble B r rows cols f) cf) =
      doubleFrame (clearedRestoration cf)
        (readyDouble B r rows cols f) := by
  let d := emptyDouble B r rows cols f
  let S := (restorationFrame d cf).stk
  have hs : S qSource = List.replicate B true := by
    change cf.stk MatrixRestorationWidthMachine.outputStack = _
    exact ho
  have hmove := move_run cf.var d.var none B S hs
  have hstart : restorationFrame d cf =
      (⟨some bridgeStart,(cf.var,(d.var,none)),S⟩ : Config) := by
    cases cf with
    | mk l var stk =>
        cases l <;> simp_all [restorationFrame,liftCfg,d,S,bridgeStart]
  rw [hstart]
  rw [hmove]
  have hbank := bridge_bank B r rows cols f cf ho
  change (⟨some doubleStart,(cf.var,(d.var,none)),moved S B⟩ : Config) =
    doubleFrame (clearedRestoration cf)
      (readyDouble B r rows cols f)
  congr 1

theorem double_phase (R r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (cf : MatrixRestorationWidthMachine.Config)
    (hfirst : 0 < rows * (cols ^ (2^r)))
    (hsecond : 0 < MatrixTableInterlaceDouble.firstColsCount r cols *
      ((MatrixTableInterlaceDouble.firstRowsCount r rows) ^ (2^R))) :
    ∃ t ≤ MatrixTableInterlaceDouble.totalBound (2^R) r rows cols f,
      ∃ d : MatrixTableInterlaceDouble.Config,
        run t (doubleFrame cf (readyDouble (2^R) r rows cols f)) =
          doubleFrame cf d ∧
        d.l = none ∧
        d.stk MatrixTableInterlaceDouble.secondOutput =
          MatrixMaterialization.rowMajor
            (MatrixTableInterlaceDouble.secondResult R r rows cols f) := by
  obtain ⟨t,ht,d,he,hh,ho⟩ :=
    MatrixTableInterlaceDouble.double_restoration_run R r rows cols f
      hfirst hsecond
  have hhe : MatrixTableInterlaceDouble.run t
      (readyDouble (2^R) r rows cols f) = d := by
    simpa only [readyDouble] using he
  have hhalt : (MatrixTableInterlaceDouble.run t
      (readyDouble (2^R) r rows cols f)).l = none := by
    rw [hhe]
    exact hh
  obtain ⟨u,hu,hr⟩ := lift_outputs_renamed
    (Equiv.sumComm DStack RStack) doubleLabels doubleControl
    MatrixTableInterlaceDouble.program program none (fun _ => rfl)
    (cf.var,none) cf.stk (readyDouble (2^R) r rows cols f) t hhalt
  change run u (doubleFrame cf _) = doubleFrame cf
    (MatrixTableInterlaceDouble.run t _) at hr
  rw [hhe] at hr
  exact ⟨u,hu.trans ht,d,hr,hh,ho⟩

noncomputable def totalBound (R r rows cols b c s q : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  MatrixRestorationWidthMachine.totalTime b c s q +
    ((2^R)+1) +
    MatrixTableInterlaceDouble.totalBound (2^R) r rows cols f

def secondOutput : Stack := .inr MatrixTableInterlaceDouble.secondOutput

/-- The unary restoration block count is produced from four physical unary
parameter banks and moved to the double controller. The protected source and
first-pass size headers are explicit separate inputs. -/
theorem restoration_join_run (R r rows cols b c s q : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hB : MatrixRestorationWidthMachine.width b c s q = 2^R)
    (hfirst : 0 < rows * (cols ^ (2^r)))
    (hsecond : 0 < MatrixTableInterlaceDouble.firstColsCount r cols *
      ((MatrixTableInterlaceDouble.firstRowsCount r rows) ^ (2^R))) :
    ∃ t ≤ totalBound R r rows cols b c s q f,
      ∃ z : Config,
        run t (restorationFrame
          (emptyDouble (2^R) r rows cols f)
          (MatrixRestorationWidthMachine.startCfg b c s q)) = z ∧
        z.l = none ∧
        z.stk secondOutput =
          MatrixMaterialization.rowMajor
            (MatrixTableInterlaceDouble.secondResult R r rows cols f) := by
  obtain ⟨t₁,ht₁,cf,h₁,hh,ho⟩ := restoration_phase b c s q
    (emptyDouble (2^R) r rows cols f)
  have ho' : cf.stk MatrixRestorationWidthMachine.outputStack =
      List.replicate (2^R) true := by simpa only [hB] using ho
  have hbridge := bridge_run (2^R) r rows cols f cf hh ho'
  obtain ⟨t₂,ht₂,d,h₂,hd,hout⟩ := double_phase R r rows cols f
    (clearedRestoration cf) hfirst hsecond
  have h₁₂ := run_add h₁ ((2^R)+1)
  rw [hbridge] at h₁₂
  have h₁₂₃ := run_add h₁₂ t₂
  rw [h₂] at h₁₂₃
  let z := doubleFrame (clearedRestoration cf) d
  refine ⟨t₁+((2^R)+1)+t₂, ?_,z,h₁₂₃,?_,?_⟩
  · dsimp [totalBound]
    omega
  · simp [z,doubleFrame,renameCfg,liftCfg,hd]
  · change d.stk MatrixTableInterlaceDouble.secondOutput = _
    exact hout

def scale (R r rows cols b c s q : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  b+c+s+q+(2^R)+
    MatrixTableInterlaceDouble.firstScale r rows cols f+
    MatrixTableInterlaceDouble.secondScale (2^R) r rows cols f+1

theorem totalBound_polynomial (R r rows cols b c s q : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hB : MatrixRestorationWidthMachine.width b c s q = 2^R) :
    totalBound R r rows cols b c s q f ≤
      (11193+4*UnaryBinaryEncoding.coefficient) *
        (scale R r rows cols b c s q f)^4 := by
  let N := scale R r rows cols b c s q f
  have hN : 1 ≤ N := by dsimp [N,scale]; omega
  have hN2 : N ≤ N^2 := by
    nlinarith [Nat.mul_le_mul (le_refl N) hN]
  have hN4 : N^2 ≤ N^4 := by
    have h : 1 ≤ N^2 := by nlinarith
    nlinarith [Nat.mul_le_mul (le_refl (N^2)) h]
  have hNto4 : N ≤ N^4 := by omega
  have hRestScale : b+c+s+q+
      MatrixRestorationWidthMachine.width b c s q+1 ≤ N := by
    rw [hB]
    dsimp [N,scale]
    omega
  have hDoubleScale :
      MatrixTableInterlaceDouble.firstScale r rows cols f+
        MatrixTableInterlaceDouble.secondScale (2^R) r rows cols f ≤ N := by
    dsimp [N,scale]
    omega
  have hrest := MatrixRestorationWidthMachine.totalTime_output_poly b c s q
  dsimp only at hrest
  have hrest' : MatrixRestorationWidthMachine.totalTime b c s q ≤
      (3000+4*UnaryBinaryEncoding.coefficient)*N^4 :=
    hrest.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left hRestScale 4))
  have hdouble := MatrixTableInterlaceDouble.totalBound_polynomial
    (2^R) r rows cols f
  have hdouble' : MatrixTableInterlaceDouble.totalBound
      (2^R) r rows cols f ≤ 8192*N^4 :=
    hdouble.trans (Nat.mul_le_mul_left 8192
      (Nat.pow_le_pow_left hDoubleScale 4))
  have hBsmall : (2^R)+1 ≤ N := by dsimp [N,scale]; omega
  change MatrixRestorationWidthMachine.totalTime b c s q +
    ((2^R)+1) +
    MatrixTableInterlaceDouble.totalBound (2^R) r rows cols f ≤
      (11193+4*UnaryBinaryEncoding.coefficient)*N^4
  calc
    _ ≤ (3000+4*UnaryBinaryEncoding.coefficient)*N^4 +
        N^4 + 8192*N^4 := by omega
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
theorem restoration_step_run {V E : Type} [Fintype V] [DecidableEq V]
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
    ∃ t ≤ (11193+4*UnaryBinaryEncoding.coefficient) *
        (scale R r rows cols P.nextDepth P.sourceConstant
          (Parameters.bins P) (Parameters.outerWidth P) f)^4,
      ∃ z : Config,
        run t (restorationFrame
          (emptyDouble (2^R) r rows cols f)
          (MatrixRestorationWidthMachine.startCfg
            P.nextDepth P.sourceConstant
            (Parameters.bins P) (Parameters.outerWidth P))) = z ∧
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
  have hB : MatrixRestorationWidthMachine.width
      P.nextDepth P.sourceConstant
      (Parameters.bins P) (Parameters.outerWidth P) = 2^R := by
    change MatrixRestorationWidthMachine.width
      P.nextDepth P.sourceConstant
      (Parameters.bins P) (Parameters.outerWidth P) =
        Parameters.restorationWidth P
    exact MatrixRestorationWidthMachine.width_eq_parameters P
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
  obtain ⟨t,ht,z,he,hh,ho⟩ := restoration_join_run R r rows cols
    P.nextDepth P.sourceConstant (Parameters.bins P)
    (Parameters.outerWidth P) f hB hfirst hsecond
  refine ⟨t,ht.trans (totalBound_polynomial R r rows cols
    P.nextDepth P.sourceConstant (Parameters.bins P)
    (Parameters.outerWidth P) f hB),z,he,hh,?_⟩
  simpa only [hfun] using ho

end EthInapproximability.CurrentPaper.MatrixTableInterlaceScalarJoin
