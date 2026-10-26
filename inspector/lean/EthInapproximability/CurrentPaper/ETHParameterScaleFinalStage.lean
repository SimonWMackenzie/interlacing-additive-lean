import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineMax
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.Parameters
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
Physical final single-scale stage. It receives a unary scale-bound word,
preserves it, computes its unary ceiling logarithm, emits the fixed
`2^24` floor, takes the actual unary maximum, and clears the temporary
logarithm bank. Source: locked v8 Appendix G `eq:paper-parameter-scale`.
-/

namespace EthInapproximability.CurrentPaper.ScaleFinalScratch

noncomputable section

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

abbrev LM := ETHParameterScaleMachineLogCopy.logMachine
def floorSize : ℕ := 2^24

abbrev Stack := ETHParameterScaleMachineLogCopy.Stack ⊕ Fin 2
def logKey (k : ETHParameterScaleMachineLogCopy.Stack) : Stack := .inl k
def floorKey : Stack := .inr 0
def answerKey : Stack := .inr 1
def sourceKey : Stack := logKey (.inl 0)
def logOutputKey : Stack := logKey (ETHParameterScaleMachineLogCopy.logStack LM.output)

def logEmbed : ETHParameterScaleMachineLogCopy.Stack ↪ Stack :=
  ⟨logKey, by intro a b h; exact Sum.inl_injective h⟩

def maxEmbed : Fin 3 ↪ Stack where
  toFun := ![logOutputKey, floorKey, answerKey]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [logOutputKey,floorKey,answerKey,logKey]

def cleanupCount : ℕ := LM.stackCount+1
def cleanupKey (i : Fin cleanupCount) : Stack :=
  if h : i.val < LM.stackCount then
    logKey (.inr (.inl ⟨i.val,h⟩))
  else logKey (.inr (.inr 0))

theorem cleanupKey_injective : Function.Injective cleanupKey := by
  intro a b he
  by_cases ha : a.val < LM.stackCount <;>
    by_cases hb : b.val < LM.stackCount
  · simp only [cleanupKey, dif_pos ha, dif_pos hb, logKey] at he
    have hv : a.val = b.val := by
      have h' := Sum.inl_injective he
      have h'' := Sum.inr_injective h'
      have h''' := Sum.inl_injective h''
      exact congrArg (fun z : Fin LM.stackCount => z.val) h'''
    exact Fin.ext hv
  · simp [cleanupKey,ha,hb,logKey] at he
  · simp [cleanupKey,ha,hb,logKey] at he
  · have hla : a.val = LM.stackCount := by have := a.isLt; simp [cleanupCount] at this; omega
    have hlb : b.val = LM.stackCount := by have := b.isLt; simp [cleanupCount] at this; omega
    exact Fin.ext (by omega)

inductive Label where
  | log (l : ETHParameterScaleMachineLogCopy.Label)
  | floorStart
  | floor (l : SourceClauseFixedUnary.Label floorSize)
  | maximum
  | clear (i : Fin (cleanupCount+1))
  | done
  deriving DecidableEq, Fintype

abbrev BaseControl := ETHParameterScaleMachineLogCopy.Control × ETHParameterScaleMachineMax.Control
abbrev Control := BaseControl × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def base : BaseControl := (ETHParameterScaleMachineLogCopy.copyControl none,(none,none))
def logControl (v : ETHParameterScaleMachineLogCopy.Control) : Control := ((v,(none,none)),none)
def readLog (v : Control) : ETHParameterScaleMachineLogCopy.Control := v.1.1
def floorControl (_ : Unit) : Control := (base,none)
def readFloor (_ : Control) : Unit := ()
def maxControl (v : ETHParameterScaleMachineMax.Control) : Control :=
  ((ETHParameterScaleMachineLogCopy.copyControl none,v),none)
def readMax (v : Control) : ETHParameterScaleMachineMax.Control := v.1.2

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .log l => stmt logEmbed Label.log logControl readLog
      (some .floorStart) (ETHParameterScaleMachineLogCopy.program l)
  | .floorStart => load (fun _ => (base,none)) (goto (fun _ => .floor 0))
  | .floor l => BitMachineInline.stmt Label.floor floorControl readFloor
      (some .maximum) (SourceClauseFixedUnary.program floorKey floorSize l)
  | .maximum => stmt maxEmbed (fun _ : Unit => .maximum)
      maxControl readMax (some (.clear 0))
      (ETHParameterScaleMachineMax.consumeProgram ())
  | .clear i => if h : i.val < cleanupCount then
      BitMachineClearBank.clearStep (cleanupKey ⟨i.val,h⟩)
        (.clear i) (.clear ⟨i.val+1,by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => base) .done
  | .done => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def initialBank (n : ℕ) : Stack → List Bool :=
  bank logEmbed (fun _ => [])
    (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).stk

def afterLogBank (n : ℕ) (c : LM.Config) : Stack → List Bool :=
  bank logEmbed (initialBank n)
    (ETHParameterScaleMachineLogCopy.afterLog (List.replicate n true) c).stk

def afterFloorBank (n : ℕ) (c : LM.Config) : Stack → List Bool :=
  Function.update (afterLogBank n c) floorKey (List.replicate floorSize true)

def afterMaxBank (n : ℕ) (c : LM.Config) : Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update (afterFloorBank n c) logOutputKey []) floorKey [])
    answerKey (List.replicate (max (Nat.clog 2 n) floorSize) true)

def finalBank (n : ℕ) (c : LM.Config) : Stack → List Bool :=
  BitMachineClearBank.cleared cleanupKey (afterMaxBank n c)

def logCost (n : ℕ) : ℕ :=
  2*n+2 + (UnaryBinaryEncoding.coefficient+6)*(n+1)^2

def cleanupCost (n : ℕ) (c : LM.Config) : ℕ :=
  (∑ i : Fin cleanupCount, ((afterMaxBank n c) (cleanupKey i)).length) +
    cleanupCount + 2

def totalCost (n : ℕ) (c : LM.Config) : ℕ :=
  logCost n + 1 + (floorSize+1) + (max (Nat.clog 2 n) floorSize+1) +
    cleanupCost n c

def preCost (n : ℕ) : ℕ :=
  logCost n + 1 + (floorSize+1) + (max (Nat.clog 2 n) floorSize+1)

def inputClock (n : ℕ) : ℕ :=
  preCost n + cleanupCount *
    (BitMachineStackGrowth.perStep program * preCost n) +
    cleanupCount + 2

theorem log_phase (n : ℕ) :
    ∃ (t : ℕ) (c : LM.Config),
      t ≤ logCost n ∧
      run t ⟨some (.log (.inl .scan)),
        logControl (ETHParameterScaleMachineLogCopy.copyControl none),
        initialBank n⟩ =
        ⟨some .floorStart,
          logControl (ETHParameterScaleMachineLogCopy.afterLog
            (List.replicate n true) c).var,
          afterLogBank n c⟩ ∧
      c.l = none ∧
      c.stk LM.output = List.replicate (Nat.clog 2 n) true := by
  obtain ⟨t,c,ht,hr,hh,ho⟩ :=
    ETHParameterScaleMachineLogCopy.copied_log_run n
  let q := List.replicate n true
  let localStart := ETHParameterScaleMachineLogCopy.start q
  have hrun : (((advance ETHParameterScaleMachineLogCopy.program)^[t])
      localStart) = ETHParameterScaleMachineLogCopy.afterLog q c := by
    simpa only [ETHParameterScaleMachineLogCopy.run] using hr
  have hhalt : ((((advance ETHParameterScaleMachineLogCopy.program)^[t])
      localStart).l) = none := by rw [hrun]; simp [ETHParameterScaleMachineLogCopy.afterLog,
        BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
        BitMachineInline.cfg,hh]
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs
    logEmbed (initialBank n) Label.log logControl readLog
    (by intro v; rfl) (some .floorStart)
    ETHParameterScaleMachineLogCopy.program program (by intro l; rfl)
    localStart t hhalt
  rw [hrun] at he
  have hbank : bank logEmbed (initialBank n) localStart.stk = initialBank n := by
    apply bank_eq_self
    intro k
    simp only [initialBank,bank_at,q,localStart]
  refine ⟨u,c,hu.trans (by simpa only [logCost] using ht),?_,hh,ho⟩
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg] at he
  have hs : localStart.l = some (.inl BitMachineCopy.Label.scan) := rfl
  have hend : (ETHParameterScaleMachineLogCopy.afterLog q c).l = none := by
    simp [ETHParameterScaleMachineLogCopy.afterLog,
      BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg,hh]
  simp only [hs,hend] at he
  have hv : localStart.var = ETHParameterScaleMachineLogCopy.copyControl none := rfl
  rw [hv] at he
  change run u ⟨some (.log (.inl .scan)),logControl localStart.var,
      bank logEmbed (initialBank n) localStart.stk⟩ =
    ⟨some .floorStart,
      logControl (ETHParameterScaleMachineLogCopy.afterLog q c).var,
      bank logEmbed (initialBank n)
        (ETHParameterScaleMachineLogCopy.afterLog q c).stk⟩ at he
  simpa only [hbank,hv,afterLogBank,q] using he

theorem afterLog_floor (n : ℕ) (c : LM.Config) :
    afterLogBank n c floorKey = [] := by
  have hout : ¬ ∃ k : ETHParameterScaleMachineLogCopy.Stack,
      logEmbed k = floorKey := by
    rintro ⟨k,h⟩
    exact Sum.inl_ne_inr h
  rw [afterLogBank,bank_outside _ _ _ _ hout]
  have hout' : ¬ ∃ k : ETHParameterScaleMachineLogCopy.Stack,
      logEmbed k = floorKey := hout
  rw [initialBank,bank_outside _ _ _ _ hout']

theorem floor_start_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .floorStart,v,S⟩ =
      ⟨some (.floor 0),(base,none),S⟩ := by
  simp [run,advance,program,TM2.step,TM2.stepAux]

theorem floor_phase (n : ℕ) (c : LM.Config) :
    ∃ t ≤ floorSize+1,
      run t ⟨some (.floor 0),(base,none),afterLogBank n c⟩ =
        ⟨some .maximum,(base,none),afterFloorBank n c⟩ := by
  let S := afterLogBank n c
  let P := SourceClauseFixedUnary.program floorKey floorSize
  let localStart : TM2.Cfg (fun _ : Stack => Bool)
      (SourceClauseFixedUnary.Label floorSize) Unit := ⟨some 0,(),S⟩
  have hr : (((advance P)^[floorSize+1]) localStart) =
      ⟨none,(),Function.update S floorKey
        (List.replicate floorSize true)⟩ := by
    exact SourceClauseFixedUnary.run floorKey S floorSize (afterLog_floor n c)
  have hh : ((((advance P)^[floorSize+1]) localStart).l) = none := by rw [hr]
  obtain ⟨t,ht,he⟩ := BitMachineInline.outputs
    Label.floor floorControl readFloor (by intro x; cases x; rfl)
    (some .maximum) P program (by intro l; rfl)
    localStart (floorSize+1) hh
  rw [hr] at he
  refine ⟨t,ht,?_⟩
  simpa only [run,BitMachineInline.cfg,localStart,S,afterFloorBank] using he

theorem afterFloor_log (n : ℕ) (c : LM.Config)
    (ho : c.stk LM.output = List.replicate (Nat.clog 2 n) true) :
    afterFloorBank n c logOutputKey =
      List.replicate (Nat.clog 2 n) true := by
  rw [afterFloorBank,Function.update_of_ne]
  · rw [afterLogBank]
    change bank logEmbed (initialBank n)
      (ETHParameterScaleMachineLogCopy.afterLog (List.replicate n true) c).stk
      (logEmbed (ETHParameterScaleMachineLogCopy.logStack LM.output)) = _
    rw [bank_at]
    exact (ETHParameterScaleMachineLogCopy.afterLog_output n c).trans ho
  · decide

theorem afterFloor_floor (n : ℕ) (c : LM.Config) :
    afterFloorBank n c floorKey = List.replicate floorSize true := by
  simp [afterFloorBank]

theorem afterFloor_answer (n : ℕ) (c : LM.Config) :
    afterFloorBank n c answerKey = [] := by
  rw [afterFloorBank,Function.update_of_ne]
  · have hout : ¬ ∃ k : ETHParameterScaleMachineLogCopy.Stack,
        logEmbed k = answerKey := by
      rintro ⟨k,h⟩
      exact Sum.inl_ne_inr h
    rw [afterLogBank,bank_outside _ _ _ _ hout,
      initialBank,bank_outside _ _ _ _ hout]
  · decide

theorem max_phase (n : ℕ) (c : LM.Config)
    (ho : c.stk LM.output = List.replicate (Nat.clog 2 n) true) :
    ∃ t ≤ max (Nat.clog 2 n) floorSize+1,
      run t ⟨some .maximum,(base,none),afterFloorBank n c⟩ =
        ⟨some (.clear 0),(base,none),afterMaxBank n c⟩ := by
  let S := afterFloorBank n c
  let a := List.replicate (Nat.clog 2 n) true
  let b := List.replicate floorSize true
  let localStart := ETHParameterScaleMachineMax.consumeCfg
    (some ()) (none,none) a b []
  have hr : ETHParameterScaleMachineMax.consumeRun
      (max a.length b.length+1) localStart =
      ETHParameterScaleMachineMax.consumeCfg none (none,none) [] []
        (List.replicate (max a.length b.length) true) := by
    simpa only [List.append_nil] using
      ETHParameterScaleMachineMax.consume_run a b [] (none,none)
  have hh : ((((advance ETHParameterScaleMachineMax.consumeProgram)^[
      max a.length b.length+1]) localStart).l) = none := by
    change (ETHParameterScaleMachineMax.consumeRun
      (max a.length b.length+1) localStart).l = none
    rw [hr]
    rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs maxEmbed S
    (fun _ : Unit => Label.maximum) maxControl readMax (by intro v; rfl)
    (some (.clear 0)) ETHParameterScaleMachineMax.consumeProgram program
    (by intro l; cases l; rfl) localStart (max a.length b.length+1) hh
  change run t (BitMachineStackEmbedding.cfg _ _ _ _ _ localStart) =
    BitMachineStackEmbedding.cfg _ _ _ _ _
      (ETHParameterScaleMachineMax.consumeRun _ localStart) at he
  rw [hr] at he
  have hbank : bank maxEmbed S localStart.stk = S := by
    apply bank_eq_self
    intro k
    fin_cases k <;>
      simp [localStart,ETHParameterScaleMachineMax.consumeCfg,
        maxEmbed,S,a,b,afterFloor_log n c ho,
        afterFloor_floor,afterFloor_answer]
  have hlocal :
      (ETHParameterScaleMachineMax.consumeCfg none (none,none) [] []
        (List.replicate (max a.length b.length) true)).stk =
      Function.update
        (Function.update
          (Function.update localStart.stk 0 []) 1 []) 2
        (List.replicate (max a.length b.length) true) := by
    funext k
    fin_cases k <;> simp [localStart,ETHParameterScaleMachineMax.consumeCfg]
  have hbank' : bank maxEmbed S
      (ETHParameterScaleMachineMax.consumeCfg none (none,none) [] []
        (List.replicate (max a.length b.length) true)).stk =
      afterMaxBank n c := by
    rw [hlocal,bank_update,bank_update,bank_update,hbank]
    simp only [show maxEmbed (0 : Fin 3) = logOutputKey by rfl,
      show maxEmbed (1 : Fin 3) = floorKey by rfl,
      show maxEmbed (2 : Fin 3) = answerKey by rfl,
      afterMaxBank,S,a,b,List.length_replicate]
  refine ⟨t,by simpa only [a,b,List.length_replicate] using ht,?_⟩
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg] at he
  change run t ⟨some .maximum,maxControl (none,none),
      bank maxEmbed S localStart.stk⟩ =
    ⟨some (.clear 0),maxControl (none,none),
      bank maxEmbed S
        (ETHParameterScaleMachineMax.consumeCfg none (none,none) [] []
          (List.replicate (max a.length b.length) true)).stk⟩ at he
  simpa only [hbank,hbank',S,maxControl,base] using he

theorem cleanup_phase (n : ℕ) (c : LM.Config) :
    run (cleanupCost n c)
      ⟨some (.clear 0),(base,none),afterMaxBank n c⟩ =
      ⟨none,(base,none),finalBank n c⟩ := by
  have hsteps : ∀ i : Fin cleanupCount,
      program (.clear i.castSucc) =
        BitMachineClearBank.clearStep (cleanupKey i)
          (.clear i.castSucc) (.clear i.succ) := by
    intro i
    simp only [program,show i.castSucc.val < cleanupCount from i.isLt,
      dite_true]
    rfl
  have hfinish : program (.clear (Fin.last cleanupCount)) =
      BitMachineClearBank.finishStep (fun _ : BaseControl => base) .done := by
    simp [program,cleanupCount]
  have hr := BitMachineClearBank.clear_bank_run program
    (fun _ : BaseControl => base) .done cleanupCount cleanupKey
    cleanupKey_injective Label.clear hsteps hfinish base
    (afterMaxBank n c)
  change run ((∑ i : Fin cleanupCount,
      (afterMaxBank n c (cleanupKey i)).length) + cleanupCount + 1)
    ⟨some (.clear 0),(base,none),afterMaxBank n c⟩ =
      ⟨some .done,(base,none),finalBank n c⟩ at hr
  simp only [run] at hr
  have hd : advance program
      (⟨some .done,(base,none),finalBank n c⟩ : Config) =
      ⟨none,(base,none),finalBank n c⟩ := rfl
  unfold run cleanupCost
  rw [show (∑ i : Fin cleanupCount, (afterMaxBank n c (cleanupKey i)).length) +
      cleanupCount + 2 =
      ((∑ i : Fin cleanupCount, (afterMaxBank n c (cleanupKey i)).length) +
      cleanupCount + 1) + 1 by omega,
    Function.iterate_succ_apply',hr,hd]

theorem afterLog_source (n : ℕ) (c : LM.Config) :
    afterLogBank n c sourceKey = List.replicate n true := by
  rw [afterLogBank]
  change bank logEmbed (initialBank n)
    (ETHParameterScaleMachineLogCopy.afterLog (List.replicate n true) c).stk
    (logEmbed (.inl (0 : Fin 1))) = _
  rw [bank_at]
  exact ETHParameterScaleMachineLogCopy.afterLog_source n c

theorem cleanupKey_ne_source (i : Fin cleanupCount) :
    cleanupKey i ≠ sourceKey := by
  intro h
  unfold cleanupKey sourceKey logKey at h
  split at h <;> cases h

theorem local_start_other (q : List Bool)
    (k : ETHParameterScaleMachineLogCopy.Stack)
    (hk : k ≠ .inl (0 : Fin 1)) :
    (ETHParameterScaleMachineLogCopy.start q).stk k = [] := by
  dsimp only [ETHParameterScaleMachineLogCopy.start,
    BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg]
  by_cases h : ∃ j : Fin 3, ETHParameterScaleMachineLogCopy.copyStack j = k
  · obtain ⟨j,rfl⟩ := h
    rw [bank_at]
    fin_cases j
    · exact (hk rfl).elim
    · rfl
    · rfl
  · rw [bank_outside _ _ _ _ h]

theorem initialBank_source (n : ℕ) :
    initialBank n sourceKey = List.replicate n true := by
  rw [initialBank]
  change bank logEmbed (fun _ => [])
    (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).stk
    (logEmbed (.inl (0 : Fin 1))) = _
  rw [bank_at]
  dsimp only [ETHParameterScaleMachineLogCopy.start,
    BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg]
  change bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
    (BitMachineCopy.cfg (some .scan) none (List.replicate n true) [] []).stk
    (ETHParameterScaleMachineLogCopy.copyStack (0 : Fin 3)) = _
  rw [bank_at]
  rfl

theorem initialBank_other (n : ℕ) (k : Stack) (hk : k ≠ sourceKey) :
    initialBank n k = [] := by
  by_cases h : ∃ j : ETHParameterScaleMachineLogCopy.Stack, logEmbed j = k
  · obtain ⟨j,rfl⟩ := h
    rw [initialBank,bank_at]
    apply local_start_other
    intro he
    subst j
    exact hk rfl
  · rw [initialBank,bank_outside _ _ _ _ h]

theorem initialBank_spec (n : ℕ) :
    initialBank n = fun k => if k = sourceKey then
      List.replicate n true else [] := by
  funext k
  by_cases hk : k = sourceKey
  · subst k
    simpa using initialBank_source n
  · simpa [hk] using initialBank_other n k hk

theorem initialBank_cleanup (n : ℕ) (i : Fin cleanupCount) :
    initialBank n (cleanupKey i) = [] := by
  by_cases hi : i.val < LM.stackCount
  · simp only [cleanupKey,dif_pos hi]
    rw [initialBank]
    change bank logEmbed (fun _ => [])
      (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).stk
      (logEmbed (.inr (.inl ⟨i.val,hi⟩))) = []
    rw [bank_at]
    exact local_start_other _ _ (by simp)
  · simp only [cleanupKey,dif_neg hi]
    rw [initialBank]
    change bank logEmbed (fun _ => [])
      (ETHParameterScaleMachineLogCopy.start (List.replicate n true)).stk
      (logEmbed (.inr (.inr 0))) = []
    rw [bank_at]
    exact local_start_other _ _ (by simp)

theorem final_source (n : ℕ) (c : LM.Config) :
    finalBank n c sourceKey = List.replicate n true := by
  have hout : ∀ i : Fin cleanupCount, cleanupKey i ≠ sourceKey := by
    intro i h
    unfold cleanupKey sourceKey logKey at h
    split at h <;> cases h
  rw [finalBank,BitMachineClearBank.cleared_foreign _ _ _ hout]
  simp only [afterMaxBank,Function.update_of_ne (by decide : sourceKey ≠ answerKey),
    Function.update_of_ne (by decide : sourceKey ≠ logOutputKey),
    afterFloorBank,Function.update_of_ne (by decide : sourceKey ≠ floorKey)]
  exact afterLog_source n c

theorem final_answer (n : ℕ) (c : LM.Config) :
    finalBank n c answerKey =
      List.replicate (max (Nat.clog 2 n) floorSize) true := by
  have hout : ∀ i : Fin cleanupCount, cleanupKey i ≠ answerKey := by
    intro i h
    unfold cleanupKey answerKey logKey at h
    split at h <;> cases h
  rw [finalBank,BitMachineClearBank.cleared_foreign _ _ _ hout]
  simp [afterMaxBank]

theorem final_floor (n : ℕ) (c : LM.Config) :
    finalBank n c floorKey = [] := by
  have hout : ∀ i : Fin cleanupCount, cleanupKey i ≠ floorKey := by
    intro i h
    unfold cleanupKey floorKey logKey at h
    split at h <;> cases h
  rw [finalBank,BitMachineClearBank.cleared_foreign _ _ _ hout]
  simp [afterMaxBank,answerKey,floorKey]

theorem final_internal (n : ℕ) (c : LM.Config) (i : Fin cleanupCount) :
    finalBank n c (cleanupKey i) = [] := by
  exact BitMachineClearBank.cleared_bank cleanupKey (afterMaxBank n c) i

private theorem run_add {a b : Config} {t : ℕ}
    (h : run t a = b) (u : ℕ) : run (t+u) a = run u b := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

theorem prefix_scale_run (n : ℕ) :
    ∃ (t : ℕ) (c : LM.Config),
      t ≤ preCost n ∧
      run t ⟨some (.log (.inl .scan)),
        logControl (ETHParameterScaleMachineLogCopy.copyControl none),
        initialBank n⟩ =
        ⟨some (.clear 0),(base,none),afterMaxBank n c⟩ ∧
      c.stk LM.output = List.replicate (Nat.clog 2 n) true := by
  obtain ⟨tl,c,hl,el,_,ho⟩ := log_phase n
  have es := floor_start_step (afterLogBank n c)
    (logControl (ETHParameterScaleMachineLogCopy.afterLog
      (List.replicate n true) c).var)
  obtain ⟨tf,hf,ef⟩ := floor_phase n c
  obtain ⟨tm,hm,em⟩ := max_phase n c ho
  have h01 := run_add el 1
  rw [es] at h01
  have h012 := run_add h01 tf
  rw [ef] at h012
  have h0123 := run_add h012 tm
  rw [em] at h0123
  refine ⟨tl+1+tf+tm,c,?_,?_,ho⟩
  · dsimp only [preCost]
    omega
  · simpa only [Nat.add_assoc] using h0123

theorem cleanupCost_bound (n t : ℕ) (c : LM.Config)
    (ht : t ≤ preCost n)
    (hr : run t ⟨some (.log (.inl .scan)),
      logControl (ETHParameterScaleMachineLogCopy.copyControl none),
      initialBank n⟩ =
      ⟨some (.clear 0),(base,none),afterMaxBank n c⟩) :
    cleanupCost n c ≤ cleanupCount *
      (BitMachineStackGrowth.perStep program * preCost n) +
      cleanupCount + 2 := by
  have hcell (i : Fin cleanupCount) :
      ((afterMaxBank n c) (cleanupKey i)).length ≤
        BitMachineStackGrowth.perStep program * preCost n := by
    have hg := BitMachineStackGrowth.run_growth program
      (⟨some (.log (.inl .scan)),
        logControl (ETHParameterScaleMachineLogCopy.copyControl none),
        initialBank n⟩ : Config) t (cleanupKey i)
    change ((run t ⟨some (.log (.inl .scan)),
      logControl (ETHParameterScaleMachineLogCopy.copyControl none),
      initialBank n⟩).stk (cleanupKey i)).length ≤
      (initialBank n (cleanupKey i)).length +
        BitMachineStackGrowth.perStep program * t at hg
    rw [hr,initialBank_cleanup] at hg
    simp only [List.length_nil,Nat.zero_add] at hg
    exact hg.trans (Nat.mul_le_mul_left _ ht)
  have hsum :
      (∑ i : Fin cleanupCount,
        ((afterMaxBank n c) (cleanupKey i)).length) ≤
      cleanupCount * (BitMachineStackGrowth.perStep program * preCost n) := by
    calc
      _ ≤ ∑ _i : Fin cleanupCount,
          BitMachineStackGrowth.perStep program * preCost n := by
            apply Finset.sum_le_sum
            intro i _
            exact hcell i
      _ = _ := by simp
  unfold cleanupCost
  omega

/-- The actual four-stage finite controller, starting from one unary input
and otherwise blank stage bank. The witnessed `c` is the real log-machine
terminal state, used only to express the exact charged cleanup cost. -/
theorem final_scale_run (n : ℕ) :
    ∃ (t : ℕ) (c : LM.Config),
      t ≤ totalCost n c ∧
      run t ⟨some (.log (.inl .scan)),
        logControl (ETHParameterScaleMachineLogCopy.copyControl none),
        initialBank n⟩ =
        ⟨none,(base,none),finalBank n c⟩ ∧
      finalBank n c sourceKey = List.replicate n true ∧
      finalBank n c answerKey =
        List.replicate (max (2^24) (Nat.clog 2 n)) true ∧
      finalBank n c floorKey = [] ∧
      (∀ i : Fin cleanupCount, finalBank n c (cleanupKey i) = []) := by
  obtain ⟨tl,c,hl,el,_,ho⟩ := log_phase n
  have es := floor_start_step (afterLogBank n c)
    (logControl (ETHParameterScaleMachineLogCopy.afterLog
      (List.replicate n true) c).var)
  obtain ⟨tf,hf,ef⟩ := floor_phase n c
  obtain ⟨tm,hm,em⟩ := max_phase n c ho
  have ec := cleanup_phase n c
  have h01 := run_add el 1
  rw [es] at h01
  have h012 := run_add h01 tf
  rw [ef] at h012
  have h0123 := run_add h012 tm
  rw [em] at h0123
  have h01234 := run_add h0123 (cleanupCost n c)
  rw [ec] at h01234
  refine ⟨tl+1+tf+tm+cleanupCost n c,c,?_,?_,final_source n c,?_,
    final_floor n c,final_internal n c⟩
  · dsimp only [totalCost]
    omega
  · simpa only [Nat.add_assoc] using h01234
  · simpa only [floorSize,max_comm] using final_answer n c

theorem final_scale_input (i : Parameters.Input) :
    ∃ (t : ℕ) (c : LM.Config),
      t ≤ totalCost (Parameters.scaleBound i) c ∧
      run t ⟨some (.log (.inl .scan)),
        logControl (ETHParameterScaleMachineLogCopy.copyControl none),
        initialBank (Parameters.scaleBound i)⟩ =
        ⟨none,(base,none),finalBank (Parameters.scaleBound i) c⟩ ∧
      finalBank (Parameters.scaleBound i) c sourceKey =
        List.replicate (Parameters.scaleBound i) true ∧
      finalBank (Parameters.scaleBound i) c answerKey =
        List.replicate (Parameters.scale i) true ∧
      finalBank (Parameters.scaleBound i) c floorKey = [] ∧
      (∀ j : Fin cleanupCount,
        finalBank (Parameters.scaleBound i) c (cleanupKey j) = []) := by
  simpa only [Parameters.scale] using final_scale_run (Parameters.scaleBound i)

/-- Input-only polynomial clock. `perStep program` and `cleanupCount` are
fixed constants of this one finite controller, including its fixed floor
emitter; neither depends on the unary input length. -/
theorem final_scale_input_clock (n : ℕ) :
    ∃ (t : ℕ) (c : LM.Config),
      t ≤ inputClock n ∧
      run t ⟨some (.log (.inl .scan)),
        logControl (ETHParameterScaleMachineLogCopy.copyControl none),
        initialBank n⟩ =
        ⟨none,(base,none),finalBank n c⟩ ∧
      finalBank n c sourceKey = List.replicate n true ∧
      finalBank n c answerKey =
        List.replicate (max (2^24) (Nat.clog 2 n)) true ∧
      finalBank n c floorKey = [] ∧
      (∀ i : Fin cleanupCount, finalBank n c (cleanupKey i) = []) := by
  obtain ⟨tp,c,ht,hp,_⟩ := prefix_scale_run n
  have hc := cleanupCost_bound n tp c ht hp
  have hrun := run_add hp (cleanupCost n c)
  rw [cleanup_phase] at hrun
  refine ⟨tp+cleanupCost n c,c,?_,hrun,final_source n c,?_,
    final_floor n c,final_internal n c⟩
  · dsimp only [inputClock]
    omega
  · simpa only [floorSize,max_comm] using final_answer n c

theorem final_scale_input_clock_for (i : Parameters.Input) :
    ∃ (t : ℕ) (c : LM.Config),
      t ≤ inputClock (Parameters.scaleBound i) ∧
      run t ⟨some (.log (.inl .scan)),
        logControl (ETHParameterScaleMachineLogCopy.copyControl none),
        initialBank (Parameters.scaleBound i)⟩ =
        ⟨none,(base,none),finalBank (Parameters.scaleBound i) c⟩ ∧
      finalBank (Parameters.scaleBound i) c sourceKey =
        List.replicate (Parameters.scaleBound i) true ∧
      finalBank (Parameters.scaleBound i) c answerKey =
        List.replicate (Parameters.scale i) true ∧
      finalBank (Parameters.scaleBound i) c floorKey = [] ∧
      (∀ j : Fin cleanupCount,
        finalBank (Parameters.scaleBound i) c (cleanupKey j) = []) := by
  simpa only [Parameters.scale] using
    final_scale_input_clock (Parameters.scaleBound i)


end
end EthInapproximability.CurrentPaper.ScaleFinalScratch
