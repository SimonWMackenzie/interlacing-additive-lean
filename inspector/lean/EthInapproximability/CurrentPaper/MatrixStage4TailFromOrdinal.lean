import EthInapproximability.CurrentPaper.MatrixStage4GraphChoose
import EthInapproximability.CurrentPaper.MatrixStage4TupleMachine
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical tail digit from the original raw-column ordinal

This fixed controller divides the raw-column ordinal by the unary bin-tuple
base power, then passes the physically computed quotient to the existing
four-division tuple-digit controller. The remaining unary powers are input
scalars whose charged construction is still required. No quotient or digit
is supplied to finite control.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TailFromOrdinal

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 22
abbrev Label := MatrixUnaryDivision.Label ⊕
  (MatrixStage4ColumnMachine.Label ⊕ Unit)
abbrev Control := Bool × MatrixStage4ColumnMachine.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def splitStart : Label := .inl .start
def digitStart : Label := .inr (.inl MatrixStage4ColumnMachine.outerStart)
def done : Label := .inr (.inr ())

def splitPermutation : Stack ≃ Stack where
  toFun := ![16,17,18,19,0,20,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,21]
  invFun := ![4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,0,1,2,3,5,21]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def splitStacks : Fin 6 ⊕ Fin 16 ≃ Stack :=
  finSumFinEquiv.trans splitPermutation
def digitStacks : Fin 16 ⊕ Fin 6 ≃ Stack := finSumFinEquiv

def digitLabels : MatrixStage4ColumnMachine.Label ⊕
    (MatrixUnaryDivision.Label ⊕ Unit) ≃ Label where
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
  | .inl l => renameStmt splitStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4ColumnMachine.outerStart))
        (MatrixUnaryDivision.program l))
  | .inr (.inl l) => renameStmt digitStacks digitLabels (Equiv.prodComm _ _)
      (liftStmt (some (.inr ())) (MatrixStage4ColumnMachine.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def splitFrame (columnScalars : Fin 16 → List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg splitStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4ColumnMachine.outerStart))
      MatrixStage4ColumnMachine.initial columnScalars c)

theorem split_phase (foreign : Fin 16 → List Bool)
    (c : MatrixUnaryDivision.Config) (bound : ℕ)
    (hhalt : (MatrixUnaryDivision.run bound c).l = none) :
    ∃ t ≤ bound, run t (splitFrame foreign c) =
      splitFrame foreign (MatrixUnaryDivision.run bound c) := by
  apply lift_outputs_renamed splitStacks (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryDivision.program program
    (some (.inl MatrixStage4ColumnMachine.outerStart))
  · intro l
    rfl
  · exact hhalt

def digitFrame (foreign : Fin 6 → List Bool)
    (splitControl : Bool) (c : MatrixStage4ColumnMachine.Config) : Config :=
  renameCfg digitStacks digitLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) splitControl foreign c)

theorem digit_phase (foreign : Fin 6 → List Bool)
    (splitControl : Bool) (c : MatrixStage4ColumnMachine.Config)
    (bound : ℕ) (hhalt : (MatrixStage4ColumnMachine.run bound c).l = none) :
    ∃ t ≤ bound, run t (digitFrame foreign splitControl c) =
      digitFrame foreign splitControl
        (MatrixStage4ColumnMachine.run bound c) := by
  apply lift_outputs_renamed digitStacks digitLabels (Equiv.prodComm _ _)
    MatrixStage4ColumnMachine.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def digitForeign (c : Config) : Fin 6 → List Bool :=
  fun j => c.stk (digitStacks (.inr j))

theorem bridge (outer stride base wordSize : List Bool)
    (c : MatrixUnaryDivision.Config) (hc : c.l = none) :
    splitFrame (fun i : Fin 16 =>
      ![outer,stride,base,wordSize,[],[],[],[],[],[],[],[],[],[],[],[]] i) c =
      digitFrame (digitForeign
        (splitFrame (fun i : Fin 16 =>
          ![outer,stride,base,wordSize,[],[],[],[],[],[],[],[],[],[],[],[]] i) c))
        c.var
        (MatrixStage4ColumnMachine.cfg
          (some MatrixStage4ColumnMachine.outerStart)
          MatrixStage4ColumnMachine.initial
          (c.stk 4) outer stride base wordSize
          [] [] [] [] [] [] [] []) := by
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      unfold splitFrame digitFrame digitForeign
        renameCfg liftCfg MatrixStage4ColumnMachine.cfg
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

open MatrixStage4Codes MatrixStage4Digits Construction MatrixMaterialization

theorem raw_tail_digit_run {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (j : Fin (s+1)) :
    let base := binBase a s q cy
    let tailCode := (tupleCode cy (s+1))
      (((rawColumnCode a s q cy).symm code).1)
    let input := splitFrame (fun i : Fin 16 =>
      ![List.replicate (cy^(s+1)) true,
        List.replicate (cy^(s-j.val)) true,
        List.replicate cy true,[true],[],[],[],[],[],[],[],[],[],[],[],[]] i)
      (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate code.val true) (List.replicate (base^s) true)
        [] [] [] [])
    ∃ t ≤ MatrixUnaryDivision.totalTime code.val (base^s) +
      MatrixUnaryDivision.totalTime tailCode.val (cy^(s+1)) +
      MatrixUnaryDivision.totalTime
        (tailCode.val % cy^(s+1)) (cy^(s-j.val)) +
      MatrixUnaryDivision.totalTime
        ((tailCode.val % cy^(s+1))/(cy^(s-j.val))) cy +
      MatrixUnaryDivision.totalTime
        (((tailCode.val % cy^(s+1))/(cy^(s-j.val))) % cy) 1 + 3,
      (run t input).l = none ∧
      (run t input).stk 15 =
        List.replicate
          (((rawColumnCode a s q cy).symm code).1 j).val true := by
  dsimp
  let base := binBase a s q cy
  let tailCode := (tupleCode cy (s+1))
    (((rawColumnCode a s q cy).symm code).1)
  have hmod : tailCode.val % cy^(s+1) = tailCode.val :=
    Nat.mod_eq_of_lt tailCode.isLt
  have hdigit : tailCode.val/(cy^(s-j.val)) % cy =
      (((rawColumnCode a s q cy).symm code).1 j).val := by
    simpa only [tailCode,Equiv.symm_apply_apply] using
      (MatrixLabelArithmetic.tuple_digit tailCode j).symm
  let splitInput := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate code.val true) (List.replicate (base^s) true)
    [] [] [] []
  let splitOutput := MatrixUnaryDivision.cfg none false []
    (List.replicate (base^s) true) []
    (List.replicate (code.val%(base^s)) true)
    (List.replicate tailCode.val true) []
  have htail : code.val/(base^s) = tailCode.val := by
    simpa only [base,tailCode] using (column_tail_code code).symm
  have hdiv : MatrixUnaryDivision.run
      (MatrixUnaryDivision.totalTime code.val (base^s)) splitInput =
      splitOutput := by
    simpa only [splitInput,splitOutput,htail] using
      MatrixUnaryDivision.division_total_run code.val (base^s)
  let foreign : Fin 16 → List Bool := fun i =>
    ![List.replicate (cy^(s+1)) true,
      List.replicate (cy^(s-j.val)) true,
      List.replicate cy true,[true],[],[],[],[],[],[],[],[],[],[],[],[]] i
  obtain ⟨t₁,ht₁,h₁⟩ := split_phase foreign splitInput
    (MatrixUnaryDivision.totalTime code.val (base^s)) (by rw [hdiv]; rfl)
  rw [hdiv] at h₁
  let tailForeign := digitForeign (splitFrame foreign splitOutput)
  let digitInput := MatrixStage4ColumnMachine.cfg
    (some MatrixStage4ColumnMachine.outerStart)
    MatrixStage4ColumnMachine.initial
    (List.replicate tailCode.val true)
    (List.replicate (cy^(s+1)) true)
    (List.replicate (cy^(s-j.val)) true)
    (List.replicate cy true) [true] [] [] [] [] [] [] [] []
  have hb : splitFrame foreign splitOutput =
      digitFrame tailForeign false digitInput := by
    simpa only [foreign,tailForeign,digitInput,splitOutput] using
      bridge (List.replicate (cy^(s+1)) true)
        (List.replicate (cy^(s-j.val)) true)
        (List.replicate cy true) [true] splitOutput (by rfl)
  obtain ⟨td,htd,hd⟩ := MatrixStage4ColumnMachine.column_run
    tailCode.val (cy^(s+1)) (cy^(s-j.val)) cy 1
  have hhalt : (MatrixStage4ColumnMachine.run td digitInput).l = none := by
    change (MatrixStage4ColumnMachine.run td
      (MatrixStage4ColumnMachine.cfg
        (some MatrixStage4ColumnMachine.outerStart)
        MatrixStage4ColumnMachine.initial
        (List.replicate tailCode.val true)
        (List.replicate (cy^(s+1)) true)
        (List.replicate (cy^(s-j.val)) true)
        (List.replicate cy true)
        (List.replicate 1 true) [] [] [] [] [] [] [] [])).l = none
    rw [hd]
    rfl
  obtain ⟨t₂,ht₂,h₂⟩ := digit_phase tailForeign false digitInput td hhalt
  let terminal := digitFrame tailForeign false
    (MatrixStage4ColumnMachine.run td digitInput)
  have hlabel : terminal.l = some done := by
    dsimp [terminal,digitFrame,renameCfg,liftCfg]
    rw [hhalt]
    rfl
  have hfinal := finish terminal hlabel
  have h12 := run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := run_add h12 1
  rw [hfinal] at h123
  refine ⟨t₁+t₂+1,?_,?_,?_⟩
  · dsimp [base,tailCode] at ht₁ htd ⊢
    omega
  · rw [h123]
  · rw [h123]
    have hout := congrArg
      (fun c : MatrixStage4ColumnMachine.Config => c.stk 15) hd
    simpa only [terminal,digitFrame,renameCfg,liftCfg,digitInput,
      MatrixStage4ColumnMachine.cfg,hmod,hdigit,Nat.div_one,
      Matrix.cons_val_fin_one] using hout

end EthInapproximability.CurrentPaper.MatrixStage4TailFromOrdinal
