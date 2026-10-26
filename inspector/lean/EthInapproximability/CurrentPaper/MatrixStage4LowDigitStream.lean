import EthInapproximability.CurrentPaper.MatrixStage4ColumnSerialize
import EthInapproximability.CurrentPaper.MatrixStage4AlignmentStream
import EthInapproximability.CurrentPaper.MatrixStage4AlignmentCorrect

/-!
# Recurrent low-digit stream producer for variable-bin Stage--4 columns

The fixed program repeatedly divides the remaining bin code by the fixed
bin base, then divides the extracted low digit by the fixed word base and
prepends its selector quotient to the serialized stream. Unary fuel counts
the bins. A complete correctness and runtime proof is still in progress.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4LowDigitStream

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

inductive Admin where
  | test | clearSelector | clearWord | move
  deriving DecidableEq, Fintype

abbrev Stack := Fin 14
abbrev Label := MatrixUnaryDivision.Label ⊕
  (MatrixUnaryDivision.Label ⊕ (MatrixStage4WordPrepend.Label ⊕ Admin))
abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def firstStart : Label := .inl .start
def secondStart : Label := .inr (.inl .start)
def prependStart : Label := .inr (.inr (.inl .mark))
def testStart : Label := .inr (.inr (.inr .test))

def firstStacks : Fin 6 ⊕ Fin 8 ≃ Stack := finSumFinEquiv

def secondPermutation : Stack ≃ Stack where
  toFun := ![3,6,7,8,9,10,0,1,2,4,5,11,12,13]
  invFun := ![6,7,8,0,9,10,1,2,3,4,5,11,12,13]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def secondStacks : Fin 6 ⊕ Fin 8 ≃ Stack :=
  finSumFinEquiv.trans secondPermutation

def prependPermutation : Stack ≃ Stack where
  toFun := ![9,11,12,0,1,2,3,4,5,6,7,8,10,13]
  invFun := ![3,4,5,6,7,8,9,10,11,0,12,1,2,13]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def prependStacks : Fin 3 ⊕ Fin 11 ≃ Stack :=
  finSumFinEquiv.trans prependPermutation

def secondLabels : MatrixUnaryDivision.Label ⊕
    (MatrixUnaryDivision.Label ⊕
      (MatrixStage4WordPrepend.Label ⊕ Admin)) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inr (.inl l))
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inr (.inl l))
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def prependLabels : MatrixStage4WordPrepend.Label ⊕
    (MatrixUnaryDivision.Label ⊕
      (MatrixUnaryDivision.Label ⊕ Admin)) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def prependControl : Option Bool × Bool ≃ Control := Equiv.prodComm _ _

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt firstStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixUnaryDivision.Label.start))
        (MatrixUnaryDivision.program l))
  | .inr (.inl l) => renameStmt secondStacks secondLabels (Equiv.refl _)
      (liftStmt (some (.inr (.inl MatrixStage4WordPrepend.Label.mark)))
        (MatrixUnaryDivision.program l))
  | .inr (.inr (.inl l)) =>
      renameStmt prependStacks prependLabels prependControl
        (liftStmt (some (.inr (.inr Admin.test)))
          (MatrixStage4WordPrepend.program l))
  | .inr (.inr (.inr .test)) =>
      pop 13 (fun v b => (b.isSome,v.2))
        (branch (fun v => v.1)
          (goto (fun _ => .inr (.inr (.inr .clearSelector))))
          (load (fun _ => (false,none)) halt))
  | .inr (.inr (.inr .clearSelector)) =>
      pop 9 (fun v b => (b.isSome,v.2))
        (branch (fun v => v.1)
          (goto (fun _ => .inr (.inr (.inr .clearSelector))))
          (goto (fun _ => .inr (.inr (.inr .clearWord)))))
  | .inr (.inr (.inr .clearWord)) =>
      pop 8 (fun v b => (b.isSome,v.2))
        (branch (fun v => v.1)
          (goto (fun _ => .inr (.inr (.inr .clearWord))))
          (goto (fun _ => .inr (.inr (.inr .move)))))
  | .inr (.inr (.inr .move)) =>
      pop 4 (fun v b => (b.isSome,v.2))
        (branch (fun v => v.1)
          (push 0 (fun _ => true)
            (goto (fun _ => .inr (.inr (.inr .move)))))
          (load (fun _ => (false,none))
            (goto (fun _ => .inl .start))))

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def cfg (l : Option Label) (v : Control)
    (current base count digit next saved wordBase wordCount wordRemainder
      selector wordSaved stream scratch fuel : List Bool) : Config :=
  ⟨l,v,![current,base,count,digit,next,saved,wordBase,wordCount,
    wordRemainder,selector,wordSaved,stream,scratch,fuel]⟩

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_succ (c : Config) (t : ℕ) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

def loopCfg (l : Option Label) (v : Control)
    (current next wordRemainder selector stream fuel base wordBase : List Bool) :
    Config :=
  cfg l v current base [] [] next [] wordBase [] wordRemainder
    selector [] stream [] fuel

theorem test_cons (v : Control)
    (current next wordRemainder selector stream fuel base wordBase : List Bool) :
    advance program (loopCfg (some testStart) v
      current next wordRemainder selector stream (true::fuel) base wordBase) =
      loopCfg (some (.inr (.inr (.inr .clearSelector)))) (true,v.2)
        current next wordRemainder selector stream fuel base wordBase := by
  simp [advance,TM2.step,TM2.stepAux,program,loopCfg,cfg,testStart]
  funext k
  fin_cases k <;> rfl

theorem test_nil (v : Control)
    (current next wordRemainder selector stream base wordBase : List Bool) :
    advance program (loopCfg (some testStart) v
      current next wordRemainder selector stream [] base wordBase) =
      loopCfg none (false,none)
        current next wordRemainder selector stream [] base wordBase := by
  simp [advance,TM2.step,TM2.stepAux,program,loopCfg,cfg,testStart]

theorem clear_selector_true (v : Control)
    (current next wordRemainder selector stream fuel base wordBase : List Bool) :
    advance program
      (loopCfg (some (.inr (.inr (.inr .clearSelector)))) v
        current next wordRemainder (true::selector) stream fuel base wordBase) =
      loopCfg (some (.inr (.inr (.inr .clearSelector)))) (true,v.2)
        current next wordRemainder selector stream fuel base wordBase := by
  simp [advance,TM2.step,TM2.stepAux,program,loopCfg,cfg]
  funext k
  fin_cases k <;> rfl

theorem clear_selector_nil (v : Control)
    (current next wordRemainder stream fuel base wordBase : List Bool) :
    advance program
      (loopCfg (some (.inr (.inr (.inr .clearSelector)))) v
        current next wordRemainder [] stream fuel base wordBase) =
      loopCfg (some (.inr (.inr (.inr .clearWord)))) (false,v.2)
        current next wordRemainder [] stream fuel base wordBase := by
  simp [advance,TM2.step,TM2.stepAux,program,loopCfg,cfg]

theorem clear_word_true (v : Control)
    (current next wordRemainder selector stream fuel base wordBase : List Bool) :
    advance program
      (loopCfg (some (.inr (.inr (.inr .clearWord)))) v
        current next (true::wordRemainder) selector stream fuel base wordBase) =
      loopCfg (some (.inr (.inr (.inr .clearWord)))) (true,v.2)
        current next wordRemainder selector stream fuel base wordBase := by
  simp [advance,TM2.step,TM2.stepAux,program,loopCfg,cfg]
  funext k
  fin_cases k <;> rfl

theorem clear_word_nil (v : Control)
    (current next selector stream fuel base wordBase : List Bool) :
    advance program
      (loopCfg (some (.inr (.inr (.inr .clearWord)))) v
        current next [] selector stream fuel base wordBase) =
      loopCfg (some (.inr (.inr (.inr .move)))) (false,v.2)
        current next [] selector stream fuel base wordBase := by
  simp [advance,TM2.step,TM2.stepAux,program,loopCfg,cfg]

theorem move_true (v : Control)
    (current next wordRemainder selector stream fuel base wordBase : List Bool) :
    advance program
      (loopCfg (some (.inr (.inr (.inr .move)))) v
        current (true::next) wordRemainder selector stream fuel base wordBase) =
      loopCfg (some (.inr (.inr (.inr .move)))) (true,v.2)
        (true::current) next wordRemainder selector stream fuel base wordBase := by
  simp [advance,TM2.step,TM2.stepAux,program,loopCfg,cfg]
  funext k
  fin_cases k <;> rfl

theorem move_nil (v : Control)
    (current wordRemainder selector stream fuel base wordBase : List Bool) :
    advance program
      (loopCfg (some (.inr (.inr (.inr .move)))) v
        current [] wordRemainder selector stream fuel base wordBase) =
      loopCfg (some firstStart) (false,none)
        current [] wordRemainder selector stream fuel base wordBase := by
  simp [advance,TM2.step,TM2.stepAux,program,loopCfg,cfg,firstStart]

theorem clear_selector_run (k : ℕ) (v : Control)
    (current next wordRemainder stream fuel base wordBase : List Bool) :
    run (k+1)
      (loopCfg (some (.inr (.inr (.inr .clearSelector)))) v
        current next wordRemainder (List.replicate k true)
        stream fuel base wordBase) =
      loopCfg (some (.inr (.inr (.inr .clearWord)))) (false,v.2)
        current next wordRemainder [] stream fuel base wordBase := by
  induction k generalizing v with
  | zero =>
    simpa only [List.replicate_zero] using
      run_succ (loopCfg (some (.inr (.inr (.inr .clearSelector)))) v
        current next wordRemainder [] stream fuel base wordBase) 0 |>.trans
        (clear_selector_nil v current next wordRemainder stream fuel base wordBase)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ,clear_selector_true]
    exact ih (true,v.2)

theorem clear_word_run (k : ℕ) (v : Control)
    (current next selector stream fuel base wordBase : List Bool) :
    run (k+1)
      (loopCfg (some (.inr (.inr (.inr .clearWord)))) v
        current next (List.replicate k true) selector
        stream fuel base wordBase) =
      loopCfg (some (.inr (.inr (.inr .move)))) (false,v.2)
        current next [] selector stream fuel base wordBase := by
  induction k generalizing v with
  | zero =>
    simpa only [List.replicate_zero] using
      run_succ (loopCfg (some (.inr (.inr (.inr .clearWord)))) v
        current next [] selector stream fuel base wordBase) 0 |>.trans
        (clear_word_nil v current next selector stream fuel base wordBase)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ,clear_word_true]
    exact ih (true,v.2)

theorem move_run (n m : ℕ) (v : Control)
    (wordRemainder selector stream fuel base wordBase : List Bool) :
    run (n+1)
      (loopCfg (some (.inr (.inr (.inr .move)))) v
        (List.replicate m true) (List.replicate n true)
        wordRemainder selector stream fuel base wordBase) =
      loopCfg (some firstStart) (false,none)
        (List.replicate (n+m) true) []
        wordRemainder selector stream fuel base wordBase := by
  induction n generalizing m v with
  | zero =>
    simpa only [List.replicate_zero,Nat.zero_add] using
      run_succ (loopCfg (some (.inr (.inr (.inr .move)))) v
        (List.replicate m true) [] wordRemainder selector
        stream fuel base wordBase) 0 |>.trans
        (move_nil v (List.replicate m true) wordRemainder selector
          stream fuel base wordBase)
  | succ n ih =>
    rw [run_succ]
    simp only [List.replicate_succ,move_true]
    simpa only [← List.replicate_succ, Nat.succ_add] using
      ih (m+1) (true,v.2)

theorem admin_next_run (alpha rem next : ℕ)
    (stream fuel base wordBase : List Bool) :
    run (alpha+rem+next+4)
      (loopCfg (some testStart) (false,none)
        [] (List.replicate next true)
        (List.replicate rem true) (List.replicate alpha true)
        stream (true::fuel) base wordBase) =
      loopCfg (some firstStart) (false,none)
        (List.replicate next true) [] [] [] stream fuel base wordBase := by
  have h1 : run 1
      (loopCfg (some testStart) (false,none)
        [] (List.replicate next true)
        (List.replicate rem true) (List.replicate alpha true)
        stream (true::fuel) base wordBase) =
      loopCfg (some (.inr (.inr (.inr .clearSelector)))) (true,none)
        [] (List.replicate next true)
        (List.replicate rem true) (List.replicate alpha true)
        stream fuel base wordBase := by
    simpa only [run,Function.iterate_one] using
      test_cons (false,none) [] (List.replicate next true)
        (List.replicate rem true) (List.replicate alpha true)
        stream fuel base wordBase
  have h2 := clear_selector_run alpha (true,none)
    [] (List.replicate next true) (List.replicate rem true)
    stream fuel base wordBase
  have h3 := clear_word_run rem (false,none)
    [] (List.replicate next true) [] stream fuel base wordBase
  have h4 := move_run next 0 (false,none)
    [] [] stream fuel base wordBase
  simp only [List.replicate_zero,Nat.add_zero] at h4
  have h12 := run_add h1 (alpha+1)
  rw [h2] at h12
  have h123 := run_add h12 (rem+1)
  rw [h3] at h123
  have h1234 := run_add h123 (next+1)
  rw [h4] at h1234
  simpa only [List.replicate_zero,Nat.add_zero,
    show 1+(alpha+1)+(rem+1)+(next+1) = alpha+rem+next+4 by omega]
    using h1234

def firstFrame (wordBase stream fuel : List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg firstStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixUnaryDivision.Label.start)) none
      (fun i : Fin 8 => ![wordBase,[],[],[],[],stream,[],fuel] i) c)

theorem first_division_run (n base : ℕ)
    (wordBase stream fuel : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n base,
      run t (cfg (some firstStart) (false,none)
        (List.replicate n true) (List.replicate base true)
        [] [] [] [] wordBase [] [] [] [] stream [] fuel) =
      cfg (some secondStart) (false,none)
        [] (List.replicate base true) []
        (List.replicate (n%base) true)
        (List.replicate (n/base) true) [] wordBase [] [] [] []
        stream [] fuel := by
  let localCfg := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate n true) (List.replicate base true) [] [] [] []
  have hlocal := MatrixUnaryDivision.division_total_run n base
  have hhalt : (MatrixUnaryDivision.run
      (MatrixUnaryDivision.totalTime n base) localCfg).l = none := by
    rw [hlocal]
    rfl
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed firstStacks
    (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryDivision.program program
    (some (.inl MatrixUnaryDivision.Label.start))
    (fun _ => rfl) none
    (fun i : Fin 8 => ![wordBase,[],[],[],[],stream,[],fuel] i)
    localCfg (MatrixUnaryDivision.totalTime n base) hhalt
  have hi : firstFrame wordBase stream fuel localCfg =
      cfg (some firstStart) (false,none)
        (List.replicate n true) (List.replicate base true)
        [] [] [] [] wordBase [] [] [] [] stream [] fuel := by
    unfold firstFrame localCfg renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : firstFrame wordBase stream fuel
      (MatrixUnaryDivision.cfg none false [] (List.replicate base true)
        [] (List.replicate (n%base) true)
        (List.replicate (n/base) true) []) =
      cfg (some secondStart) (false,none)
        [] (List.replicate base true) []
        (List.replicate (n%base) true)
        (List.replicate (n/base) true) [] wordBase [] [] [] []
        stream [] fuel := by
    unfold firstFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  refine ⟨t,ht,?_⟩
  change run t (firstFrame wordBase stream fuel localCfg) =
    firstFrame wordBase stream fuel
      (MatrixUnaryDivision.run (MatrixUnaryDivision.totalTime n base) localCfg) at hr
  rw [hi,hlocal,hf] at hr
  exact hr

def secondFrame (base next stream fuel : List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg secondStacks secondLabels (Equiv.refl _)
    (liftCfg (some (.inr (.inl MatrixStage4WordPrepend.Label.mark))) none
      (fun i : Fin 8 => ![[],base,[],next,[],stream,[],fuel] i) c)

theorem second_division_run (digit wordBase : ℕ)
    (base next stream fuel : List Bool) :
    ∃ t ≤ MatrixUnaryDivision.totalTime digit wordBase,
      run t (cfg (some secondStart) (false,none)
        [] base [] (List.replicate digit true) next []
        (List.replicate wordBase true) [] [] [] [] stream [] fuel) =
      cfg (some prependStart) (false,none)
        [] base [] [] next [] (List.replicate wordBase true) []
        (List.replicate (digit%wordBase) true)
        (List.replicate (digit/wordBase) true) [] stream [] fuel := by
  let localCfg := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate digit true) (List.replicate wordBase true) [] [] [] []
  have hlocal := MatrixUnaryDivision.division_total_run digit wordBase
  have hhalt : (MatrixUnaryDivision.run
      (MatrixUnaryDivision.totalTime digit wordBase) localCfg).l = none := by
    rw [hlocal]
    rfl
  let foreign : Fin 8 → List Bool :=
    fun i => ![[],base,[],next,[],stream,[],fuel] i
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed secondStacks
    secondLabels (Equiv.refl _)
    MatrixUnaryDivision.program program
    (some (.inr (.inl MatrixStage4WordPrepend.Label.mark)))
    (fun _ => rfl) none foreign localCfg
    (MatrixUnaryDivision.totalTime digit wordBase) hhalt
  have hi : secondFrame base next stream fuel localCfg =
      cfg (some secondStart) (false,none)
        [] base [] (List.replicate digit true) next []
        (List.replicate wordBase true) [] [] [] [] stream [] fuel := by
    unfold secondFrame localCfg renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : secondFrame base next stream fuel
      (MatrixUnaryDivision.cfg none false [] (List.replicate wordBase true)
        [] (List.replicate (digit%wordBase) true)
        (List.replicate (digit/wordBase) true) []) =
      cfg (some prependStart) (false,none)
        [] base [] [] next [] (List.replicate wordBase true) []
        (List.replicate (digit%wordBase) true)
        (List.replicate (digit/wordBase) true) [] stream [] fuel := by
    unfold secondFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  refine ⟨t,ht,?_⟩
  change run t (secondFrame base next stream fuel localCfg) =
    secondFrame base next stream fuel
      (MatrixUnaryDivision.run
        (MatrixUnaryDivision.totalTime digit wordBase) localCfg) at hr
  rw [hi,hlocal,hf] at hr
  exact hr

def prependFrame (base next wordBase wordRemainder fuel : List Bool)
    (c : MatrixStage4WordPrepend.Config) : Config :=
  renameCfg prependStacks prependLabels prependControl
    (liftCfg (some (.inr (.inr Admin.test))) false
      (fun i : Fin 11 => ![[],base,[],[],next,[],wordBase,[],
        wordRemainder,[],fuel] i) c)

theorem prepend_selector_run (selector : ℕ)
    (base next wordBase wordRemainder stream fuel : List Bool) :
    ∃ t ≤ 2*selector+3,
      run t (cfg (some prependStart) (false,none)
        [] base [] [] next [] wordBase [] wordRemainder
        (List.replicate selector true) [] stream [] fuel) =
      cfg (some testStart) (false,none)
        [] base [] [] next [] wordBase [] wordRemainder
        (List.replicate selector true) []
        (List.replicate selector true ++ false::stream) [] fuel := by
  let localCfg := MatrixStage4WordPrepend.cfg (some .mark) none
    (List.replicate selector true) stream []
  have hlocal := MatrixStage4WordPrepend.prepend_run selector stream
  have hlocal' : MatrixStage4WordPrepend.run (2*selector+3) localCfg =
      MatrixStage4WordPrepend.cfg none none
        (List.replicate selector true)
        (List.replicate selector true ++ false::stream) [] := by
    simpa only [localCfg,show 1+(selector+1)+(selector+1) =
      2*selector+3 by omega] using hlocal
  have hhalt : (MatrixStage4WordPrepend.run (2*selector+3) localCfg).l = none := by
    rw [hlocal']
    rfl
  let foreign : Fin 11 → List Bool :=
    fun i => ![[],base,[],[],next,[],wordBase,[],wordRemainder,[],fuel] i
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed prependStacks
    prependLabels prependControl
    MatrixStage4WordPrepend.program program
    (some (.inr (.inr Admin.test)))
    (fun _ => rfl) false foreign localCfg
    (2*selector+3) hhalt
  have hi : prependFrame base next wordBase wordRemainder fuel localCfg =
      cfg (some prependStart) (false,none)
        [] base [] [] next [] wordBase [] wordRemainder
        (List.replicate selector true) [] stream [] fuel := by
    unfold prependFrame localCfg renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : prependFrame base next wordBase wordRemainder fuel
      (MatrixStage4WordPrepend.cfg none none
        (List.replicate selector true)
        (List.replicate selector true ++ false::stream) []) =
      cfg (some testStart) (false,none)
        [] base [] [] next [] wordBase [] wordRemainder
        (List.replicate selector true) []
        (List.replicate selector true ++ false::stream) [] fuel := by
    unfold prependFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  refine ⟨t, ?_, ?_⟩
  · omega
  · change run t (prependFrame base next wordBase wordRemainder fuel localCfg) =
      prependFrame base next wordBase wordRemainder fuel
        (MatrixStage4WordPrepend.run (2*selector+3) localCfg) at hr
    rw [hi,hlocal',hf] at hr
    exact hr

theorem round_run (n base wordBase : ℕ)
    (stream fuel : List Bool) :
    let digit := n%base
    let selector := digit/wordBase
    ∃ t ≤ MatrixUnaryDivision.totalTime n base+
      MatrixUnaryDivision.totalTime digit wordBase+
      (2*selector+3),
      run t (loopCfg (some firstStart) (false,none)
        (List.replicate n true) [] [] [] stream fuel
        (List.replicate base true) (List.replicate wordBase true)) =
      loopCfg (some testStart) (false,none)
        [] (List.replicate (n/base) true)
        (List.replicate (digit%wordBase) true)
        (List.replicate selector true)
        (List.replicate selector true ++ false::stream) fuel
        (List.replicate base true) (List.replicate wordBase true) := by
  dsimp
  obtain ⟨t₁,ht₁,h₁⟩ := first_division_run n base
    (List.replicate wordBase true) stream fuel
  obtain ⟨t₂,ht₂,h₂⟩ := second_division_run (n%base) wordBase
    (List.replicate base true) (List.replicate (n/base) true) stream fuel
  obtain ⟨t₃,ht₃,h₃⟩ := prepend_selector_run ((n%base)/wordBase)
    (List.replicate base true) (List.replicate (n/base) true)
    (List.replicate wordBase true)
    (List.replicate ((n%base)%wordBase) true) stream fuel
  have h12 := run_add h₁ t₂
  rw [h₂] at h12
  have h123 := run_add h12 t₃
  rw [h₃] at h123
  refine ⟨t₁+t₂+t₃, by omega, ?_⟩
  simpa only [loopCfg] using h123

def selector (n base wordBase : ℕ) : ℕ := (n%base)/wordBase
def remainder (n base wordBase : ℕ) : ℕ := (n%base)%wordBase
def prepend (p : ℕ) (stream : List Bool) : List Bool :=
  List.replicate p true ++ false::stream

def roundCost (n base wordBase : ℕ) : ℕ :=
  MatrixUnaryDivision.totalTime n base+
    MatrixUnaryDivision.totalTime (n%base) wordBase+
    (2*selector n base wordBase+3)

def adminCost (n base wordBase : ℕ) : ℕ :=
  selector n base wordBase + remainder n base wordBase + n/base + 4

def timeBudget (n base wordBase : ℕ) : ℕ → ℕ
  | 0 => roundCost n base wordBase + 1
  | k+1 => roundCost n base wordBase + adminCost n base wordBase +
      timeBudget (n/base) base wordBase k

def terminal (n base wordBase : ℕ) (stream : List Bool) : ℕ → Config
  | 0 => loopCfg none (false,none)
      [] (List.replicate (n/base) true)
      (List.replicate (remainder n base wordBase) true)
      (List.replicate (selector n base wordBase) true)
      (prepend (selector n base wordBase) stream) []
      (List.replicate base true) (List.replicate wordBase true)
  | k+1 => terminal (n/base) base wordBase
      (prepend (selector n base wordBase) stream) k

theorem rounds_run (extra n base wordBase : ℕ) (stream : List Bool) :
    ∃ t ≤ timeBudget n base wordBase extra,
      run t (loopCfg (some firstStart) (false,none)
        (List.replicate n true) [] [] [] stream
        (List.replicate extra true)
        (List.replicate base true) (List.replicate wordBase true)) =
      terminal n base wordBase stream extra := by
  induction extra generalizing n stream with
  | zero =>
    obtain ⟨tr,htr,hr⟩ := round_run n base wordBase stream []
    have hstop : run 1
        (loopCfg (some testStart) (false,none)
          [] (List.replicate (n/base) true)
          (List.replicate (remainder n base wordBase) true)
          (List.replicate (selector n base wordBase) true)
          (prepend (selector n base wordBase) stream) []
          (List.replicate base true) (List.replicate wordBase true)) =
        terminal n base wordBase stream 0 := by
      simpa only [run,Function.iterate_one,terminal,selector,remainder,prepend]
        using test_nil (false,none) []
          (List.replicate (n/base) true)
          (List.replicate ((n%base)%wordBase) true)
          (List.replicate ((n%base)/wordBase) true)
          (List.replicate ((n%base)/wordBase) true ++ false::stream)
          (List.replicate base true) (List.replicate wordBase true)
    have h := run_add hr 1
    dsimp [selector,remainder,prepend] at hstop
    rw [hstop] at h
    refine ⟨tr+1, ?_, ?_⟩
    · dsimp [timeBudget,roundCost,selector] at htr ⊢
      omega
    · simpa only [List.replicate_zero,selector,remainder,prepend] using h
  | succ k ih =>
    let alpha := selector n base wordBase
    let rem := remainder n base wordBase
    let next := n/base
    let stream' := prepend alpha stream
    obtain ⟨tr,htr,hr⟩ := round_run n base wordBase stream
      (List.replicate (k+1) true)
    have ha := admin_next_run alpha rem next stream' (List.replicate k true)
      (List.replicate base true) (List.replicate wordBase true)
    obtain ⟨ti,hti,hi⟩ := ih next stream'
    dsimp [next] at hti
    have h1 := run_add hr (adminCost n base wordBase)
    have h2 := run_add h1 ti
    refine ⟨tr+adminCost n base wordBase+ti, ?_, ?_⟩
    · dsimp [timeBudget,roundCost,adminCost,selector,remainder] at htr ha hti ⊢
      omega
    · dsimp [alpha,rem,next,stream',selector,remainder,prepend] at ha hi
      dsimp [adminCost,selector,remainder] at h2
      simp only [List.replicate_succ] at h2
      rw [ha,hi] at h2
      simpa only [terminal,List.replicate_succ,
        selector,remainder,prepend] using h2

def selectorsHigh (n base wordBase : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => selectorsHigh (n/base) base wordBase k ++
      [selector n base wordBase]

def topSelector (n base wordBase : ℕ) : ℕ → ℕ
  | 0 => selector n base wordBase
  | k+1 => topSelector (n/base) base wordBase k

private theorem words_append (xs ys : List ℕ) :
    MatrixStage4AlignmentStream.words (xs++ys) =
      MatrixStage4AlignmentStream.words xs ++
        MatrixStage4AlignmentStream.words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [MatrixStage4AlignmentStream.words,ih,List.append_assoc]

theorem terminal_halts (extra n base wordBase : ℕ) (stream : List Bool) :
    (terminal n base wordBase stream extra).l = none := by
  induction extra generalizing n stream with
  | zero => rfl
  | succ k ih => exact ih (n/base) (prepend (selector n base wordBase) stream)

theorem terminal_selector (extra n base wordBase : ℕ) (stream : List Bool) :
    (terminal n base wordBase stream extra).stk 9 =
      List.replicate (topSelector n base wordBase extra) true := by
  induction extra generalizing n stream with
  | zero => rfl
  | succ k ih => exact ih (n/base) (prepend (selector n base wordBase) stream)

theorem terminal_scratch (extra n base wordBase : ℕ) (stream : List Bool) :
    (terminal n base wordBase stream extra).stk 12 = [] := by
  induction extra generalizing n stream with
  | zero => rfl
  | succ k ih => exact ih (n/base) (prepend (selector n base wordBase) stream)

theorem terminal_stream (extra n base wordBase : ℕ) (stream : List Bool) :
    (terminal n base wordBase stream extra).stk 11 =
      MatrixStage4AlignmentStream.words
        (selectorsHigh n base wordBase (extra+1)) ++ stream := by
  induction extra generalizing n stream with
  | zero =>
    simp [terminal,selectorsHigh,MatrixStage4AlignmentStream.words,
      prepend,loopCfg,cfg,List.append_assoc]
  | succ k ih =>
    change (terminal (n/base) base wordBase
      (prepend (selector n base wordBase) stream) k).stk 11 = _
    rw [ih]
    simp [selectorsHigh,words_append,
      MatrixStage4AlignmentStream.words,List.append_assoc,prepend]

theorem selectorsHigh_digits (s n base wordBase : ℕ) :
    selectorsHigh n base wordBase s =
      List.ofFn (fun p : Fin s =>
        ((n / base^(s-1-p.val)) % base)/wordBase) := by
  induction s generalizing n with
  | zero => rfl
  | succ s ih =>
    rw [selectorsHigh,List.ofFn_succ',ih]
    rw [List.concat_eq_append]
    congr 1
    · congr 1
      funext p
      simp only [Fin.val_castSucc]
      have he : s + 1 - 1 - p.val = (s - 1 - p.val) + 1 := by
        have hp := p.isLt
        omega
      rw [he, pow_succ, Nat.div_div_eq_div_mul]
      rw [mul_comm]
    · simp [selector]

theorem topSelector_digit (extra n base wordBase : ℕ) :
    topSelector n base wordBase extra =
      ((n / base^extra) % base)/wordBase := by
  induction extra generalizing n with
  | zero => simp [topSelector,selector]
  | succ k ih =>
    rw [topSelector,ih,pow_succ,Nat.div_div_eq_div_mul,mul_comm]

open MatrixStage4Codes MatrixStage4Digits MatrixStage4AlignmentDigits
open Construction

theorem raw_bin_stream_run {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    let base := binBase a s q cy
    let wordSize := wordBase a s cy
    let n := code.val % base^s
    let c := loopCfg (some firstStart) (false,none)
      (List.replicate n true) [] [] [] []
      (List.replicate (s-1) true)
      (List.replicate base true) (List.replicate wordSize true)
    ∃ t ≤ timeBudget n base wordSize (s-1),
      (run t c).l = none ∧
      (run t c).stk 12 = [] ∧
      (run t c).stk 9 =
        List.replicate
          (selectorDigit code (firstBin s hs)) true ∧
      (run t c).stk 11 =
        MatrixStage4AlignmentStream.words
          (MatrixStage4AlignmentCorrect.selectorWords code) := by
  dsimp
  let base := binBase a s q cy
  let wordSize := wordBase a s cy
  let n := code.val % base^s
  let extra := s-1
  have hsize : extra+1=s := by dsimp [extra]; omega
  obtain ⟨t,ht,hr⟩ := rounds_run extra n base wordSize []
  have hsel : topSelector n base wordSize extra =
      selectorDigit code (firstBin s hs) := by
    rw [topSelector_digit]
    simp only [MatrixStage4AlignmentDigits.selectorDigit,
      MatrixStage4Digits.binDigit,firstBin]
    simp only [Nat.sub_zero]
    dsimp [extra,n,base,wordSize]
  have hwords : selectorsHigh n base wordSize (extra+1) =
      MatrixStage4AlignmentCorrect.selectorWords code := by
    rw [hsize,selectorsHigh_digits]
    rfl
  refine ⟨t,ht,?_,?_,?_,?_⟩
  · rw [hr]
    exact terminal_halts extra n base wordSize []
  · rw [hr]
    exact terminal_scratch extra n base wordSize []
  · rw [hr,terminal_selector,hsel]
  · rw [hr,terminal_stream,hwords]
    simp

end EthInapproximability.CurrentPaper.MatrixStage4LowDigitStream
