import EthInapproximability.CurrentPaper.MatrixStage4TailFromOrdinal
import EthInapproximability.CurrentPaper.MatrixWeightedPower
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Charged selected tail stride

Given unary `s`, a chosen tail index `j ≤ s`, and unary base `cy`, this
fixed eleven-stack controller subtracts `j` using the threshold machine
and computes `cy^(s-j)` using the variable-exponent unary-power machine.
The stride is a physical output, not a supplied power. Supplying `s`, `j`,
and `cy` themselves remains the caller's responsibility.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4SelectedPower

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 11
abbrev Label := MatrixUnaryCut.Label ⊕ (MatrixWeightedPower.Label ⊕ Unit)
abbrev Control := MatrixUnaryCut.Control × MatrixWeightedPower.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def cutStart : Label := .inl .scan
def powerStart : Label := .inr (.inl (.inr .test))
def done : Label := .inr (.inr ())

def cutPermutation : Stack ≃ Stack where
  toFun := ![6,7,8,9,0,1,2,3,4,5,10]
  invFun := ![4,5,6,7,8,9,0,1,2,3,10]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def cutStacks : Fin 4 ⊕ Fin 7 ≃ Stack :=
  finSumFinEquiv.trans cutPermutation
def powerStacks : MatrixWeightedPower.Stack ⊕ Fin 4 ≃ Stack :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

def powerLabels : MatrixWeightedPower.Label ⊕
    (MatrixUnaryCut.Label ⊕ Unit) ≃ Label where
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
  | .inl l => renameStmt cutStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl (.inr .test))) (MatrixUnaryCut.program l))
  | .inr (.inl l) => renameStmt powerStacks powerLabels
      (Equiv.prodComm _ _)
      (liftStmt (some (.inr ())) (MatrixWeightedPower.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def cutFrame (base : List Bool) (c : MatrixUnaryCut.Config) : Config :=
  renameCfg cutStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl (.inr .test))) (false,false)
      (fun i : Fin 7 => ![[true],base,[],[],[],[],[]] i) c)

theorem cut_phase (base : List Bool) (c : MatrixUnaryCut.Config)
    (bound : ℕ) (hhalt : (MatrixUnaryCut.run bound c).l = none) :
    ∃ t ≤ bound, run t (cutFrame base c) =
      cutFrame base (MatrixUnaryCut.run bound c) := by
  apply lift_outputs_renamed cutStacks (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryCut.program program (some (.inl (.inr .test)))
  · intro l
    rfl
  · exact hhalt

def powerFrame (foreign : Fin 4 → List Bool)
    (cutControl : MatrixUnaryCut.Control)
    (c : MatrixWeightedPower.Config) : Config :=
  renameCfg powerStacks powerLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) cutControl foreign c)

theorem power_phase (foreign : Fin 4 → List Bool)
    (cutControl : MatrixUnaryCut.Control)
    (c : MatrixWeightedPower.Config) (bound : ℕ)
    (hhalt : (MatrixWeightedPower.run bound c).l = none) :
    ∃ t ≤ bound, run t (powerFrame foreign cutControl c) =
      powerFrame foreign cutControl (MatrixWeightedPower.run bound c) := by
  apply lift_outputs_renamed powerStacks powerLabels (Equiv.prodComm _ _)
    MatrixWeightedPower.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def powerForeign (c : Config) : Fin 4 → List Bool :=
  fun j => c.stk (powerStacks (.inr j))

theorem bridge (base : List Bool) (c : MatrixUnaryCut.Config)
    (hc : c.l = none) :
    cutFrame base c =
      powerFrame (powerForeign (cutFrame base c)) c.var
        (MatrixWeightedPower.cfg (some (.inr .test)) (false,false)
          [true] base [] (c.stk 0)) := by
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      unfold cutFrame powerFrame powerForeign renameCfg liftCfg
        MatrixWeightedPower.cfg MatrixWeightedPower.bank
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

theorem selected_power_run (base s : ℕ) (j : Fin (s+1)) :
    let input := cutFrame (List.replicate base true)
      (MatrixUnaryCut.cfg (some .scan) (false,true)
        (List.replicate s true) (List.replicate j.val true) [] [])
    ∃ t ≤ 3*j.val+4+MatrixWeightedPower.powerBound base (s-j.val)+2,
      (run t input).l = none ∧
      (run t input).stk 0 = List.replicate (base^(s-j.val)) true := by
  dsimp
  let cutInput := MatrixUnaryCut.cfg (some .scan) (false,true)
    (List.replicate s true) (List.replicate j.val true) [] []
  let cutOutput := MatrixUnaryCut.cfg none (true,false)
    (List.replicate (s-j.val) true) (List.replicate j.val true) [] []
  have hj : j.val ≤ s := by have := j.isLt; omega
  obtain ⟨tc,htc,hc⟩ := MatrixUnaryCut.cut_run s j.val
  have hcut : MatrixUnaryCut.run tc cutInput = cutOutput := by
    simpa [cutInput,cutOutput,hj,show ¬ s < j.val by omega] using hc
  have hbound : tc ≤ 3*j.val+4 := by
    simpa only [Nat.min_eq_right hj] using htc
  obtain ⟨t₁,ht₁,h₁⟩ := cut_phase (List.replicate base true)
    cutInput tc (by rw [hcut]; rfl)
  rw [hcut] at h₁
  let foreign := powerForeign
    (cutFrame (List.replicate base true) cutOutput)
  let powerInput := MatrixWeightedPower.cfg (some (.inr .test))
    (false,false) [true] (List.replicate base true) []
    (List.replicate (s-j.val) true)
  have hb : cutFrame (List.replicate base true) cutOutput =
      powerFrame foreign (true,false) powerInput := by
    simpa only [foreign,powerInput,cutOutput] using
      bridge (List.replicate base true) cutOutput (by rfl)
  obtain ⟨tp,htp,hp⟩ := MatrixWeightedPower.power_run base (s-j.val)
  have hhalt : (MatrixWeightedPower.run tp powerInput).l = none := by
    have hh := congrArg (fun c : MatrixWeightedPower.Config => c.l) hp
    simpa only [powerInput,List.replicate_one] using hh
  obtain ⟨t₂,ht₂,h₂⟩ := power_phase foreign (true,false)
    powerInput tp hhalt
  let terminal := powerFrame foreign (true,false)
    (MatrixWeightedPower.run tp powerInput)
  have hlabel : terminal.l = some done := by
    dsimp [terminal,powerFrame,renameCfg,liftCfg]
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
    have hout := congrArg
      (fun c : MatrixWeightedPower.Config => c.stk (.inl 0)) hp
    simpa only [terminal,powerFrame,renameCfg,liftCfg,powerInput,
      MatrixWeightedPower.cfg,MatrixWeightedPower.bank,
      Sum.elim_inl,
      List.replicate_one] using hout

end EthInapproximability.CurrentPaper.MatrixStage4SelectedPower
