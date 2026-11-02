import EthInapproximability.CurrentPaper.MatrixStage4ColumnMachine
import EthInapproximability.CurrentPaper.MatrixStage4WordPrepend
import EthInapproximability.CurrentPaper.MatrixStage4AlignmentDigits
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical selected-bin column decode followed by unary word serialization

This fixed Fin-17 controller runs the four-division selected-bin decoder,
then serializes its selector output into a foreign stream. The column ordinal,
stride, and bases are supplied as unary stacks; their production and the
variable-bin outer loop remain separate obligations.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4ColumnSerialize

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 17
abbrev Label := MatrixStage4ColumnMachine.Label ⊕
  (MatrixStage4WordPrepend.Label ⊕ Unit)
abbrev Control := MatrixStage4ColumnMachine.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def columnStart : Label := .inl MatrixStage4ColumnMachine.outerStart
def wordStart : Label := .inr (.inl .mark)
def done : Label := .inr (.inr ())

def columnStacks : Fin 16 ⊕ Fin 1 ≃ Stack := finSumFinEquiv

def wordPermutation : Stack ≃ Stack where
  toFun := ![15,16,11,0,1,2,3,4,5,6,7,8,9,10,12,13,14]
  invFun := ![3,4,5,6,7,8,9,10,11,12,13,2,14,15,16,0,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def wordStacks : Fin 3 ⊕ Fin 14 ≃ Stack :=
  finSumFinEquiv.trans wordPermutation

def wordLabels : MatrixStage4WordPrepend.Label ⊕
    (MatrixStage4ColumnMachine.Label ⊕ Unit) ≃ Label where
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

def wordControl : Option Bool × MatrixStage4ColumnMachine.Control ≃ Control :=
  Equiv.prodComm _ _

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt columnStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4WordPrepend.Label.mark))
        (MatrixStage4ColumnMachine.program l))
  | .inr (.inl l) => renameStmt wordStacks wordLabels wordControl
      (liftStmt (some (.inr ())) (MatrixStage4WordPrepend.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def columnFrame (stream : List Bool) (c : MatrixStage4ColumnMachine.Config) :
    Config :=
  renameCfg columnStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4WordPrepend.Label.mark)) none
      (fun _ : Fin 1 => stream) c)

theorem column_phase (stream : List Bool)
    (c : MatrixStage4ColumnMachine.Config) (bound : ℕ)
    (hhalt : (MatrixStage4ColumnMachine.run bound c).l = none) :
    ∃ t ≤ bound, run t (columnFrame stream c) =
      columnFrame stream (MatrixStage4ColumnMachine.run bound c) := by
  apply lift_outputs_renamed columnStacks (Equiv.refl _) (Equiv.refl _)
    MatrixStage4ColumnMachine.program program
    (some (.inl MatrixStage4WordPrepend.Label.mark))
  · intro l
    rfl
  · exact hhalt

def wordFrame (bank : Fin 14 → List Bool)
    (columnControl : MatrixStage4ColumnMachine.Control)
    (c : MatrixStage4WordPrepend.Config) : Config :=
  renameCfg wordStacks wordLabels wordControl
    (liftCfg (some (.inr ())) columnControl bank c)

theorem word_phase (bank : Fin 14 → List Bool)
    (columnControl : MatrixStage4ColumnMachine.Control)
    (c : MatrixStage4WordPrepend.Config) (bound : ℕ)
    (hhalt : (MatrixStage4WordPrepend.run bound c).l = none) :
    ∃ t ≤ bound, run t (wordFrame bank columnControl c) =
      wordFrame bank columnControl (MatrixStage4WordPrepend.run bound c) := by
  apply lift_outputs_renamed wordStacks wordLabels wordControl
    MatrixStage4WordPrepend.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def wordForeign (c : Config) : Fin 14 → List Bool :=
  fun j => c.stk (wordStacks (.inr j))

theorem bridge (stream : List Bool) (c : MatrixStage4ColumnMachine.Config)
    (hc : c.l = none) :
    columnFrame stream c =
      wordFrame (wordForeign (columnFrame stream c)) c.var
        (MatrixStage4WordPrepend.cfg (some .mark) none
          (c.stk 15) stream (c.stk 11)) := by
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      unfold columnFrame wordFrame wordForeign renameCfg liftCfg
      congr 1
      funext k
      fin_cases k <;> rfl

theorem done_run (v : Control) (S : Stack → List Bool) :
    run 1 (⟨some done,v,S⟩ : Config) = ⟨none,v,S⟩ := by
  simp [run,advance,done,program,TM2.step,TM2.stepAux]

theorem selected_bin_serialize
    (c : MatrixStage4ColumnMachine.Config)
    (stream : List Bool) (bound p : ℕ)
    (hhalt : (MatrixStage4ColumnMachine.run bound c).l = none)
    (hsource : (MatrixStage4ColumnMachine.run bound c).stk 15 =
      List.replicate p true)
    (hscratch : (MatrixStage4ColumnMachine.run bound c).stk 11 = []) :
    let d := MatrixStage4ColumnMachine.run bound c
    let bank := wordForeign (columnFrame stream d)
    ∃ t ≤ bound + (2*p+4),
      run t (columnFrame stream c) =
        ⟨none, (d.var,none),
          (wordFrame bank d.var
            (MatrixStage4WordPrepend.cfg none none
              (List.replicate p true)
              (List.replicate p true ++ false::stream) [])).stk⟩ := by
  dsimp
  obtain ⟨t₁,ht₁,h₁⟩ := column_phase stream c bound hhalt
  let d := MatrixStage4ColumnMachine.run bound c
  let bank := wordForeign (columnFrame stream d)
  have hb : columnFrame stream d = wordFrame bank d.var
      (MatrixStage4WordPrepend.cfg (some .mark) none
        (List.replicate p true) stream []) := by
    simpa only [d,bank,hsource,hscratch] using bridge stream d hhalt
  have hw := MatrixStage4WordPrepend.prepend_run p stream
  obtain ⟨t₂,ht₂,h₂⟩ := word_phase bank d.var
    (MatrixStage4WordPrepend.cfg (some .mark) none
      (List.replicate p true) stream [])
    (1+(p+1)+(p+1)) (by rw [hw]; rfl)
  rw [hw] at h₂
  let terminal := wordFrame bank d.var
    (MatrixStage4WordPrepend.cfg none none
      (List.replicate p true)
      (List.replicate p true ++ false::stream) [])
  have hterminal : terminal.l = some done := rfl
  have hd : run 1 terminal = ⟨none,terminal.var,terminal.stk⟩ := by
    change run 1 (⟨some done,terminal.var,terminal.stk⟩ : Config) = _
    exact done_run terminal.var terminal.stk
  refine ⟨t₁+t₂+1, ?_, ?_⟩
  · omega
  · have h12 := run_add h₁ t₂
    rw [hb,h₂] at h12
    have h123 := run_add h12 1
    rw [hd] at h123
    simpa only [terminal,wordFrame] using h123

theorem selected_bin_serialize_outputs
    (c : MatrixStage4ColumnMachine.Config)
    (stream : List Bool) (bound p : ℕ)
    (hhalt : (MatrixStage4ColumnMachine.run bound c).l = none)
    (hsource : (MatrixStage4ColumnMachine.run bound c).stk 15 =
      List.replicate p true)
    (hscratch : (MatrixStage4ColumnMachine.run bound c).stk 11 = []) :
    ∃ t ≤ bound + (2*p+4),
      (run t (columnFrame stream c)).l = none ∧
      (run t (columnFrame stream c)).stk 15 = List.replicate p true ∧
      (run t (columnFrame stream c)).stk 16 =
        List.replicate p true ++ false::stream := by
  obtain ⟨t,ht,he⟩ := selected_bin_serialize c stream bound p
    hhalt hsource hscratch
  refine ⟨t,ht,?_,?_,?_⟩
  all_goals rw [he]
  all_goals rfl

open MatrixStage4Codes MatrixStage4Digits MatrixStage4AlignmentDigits
open Construction

theorem raw_column_serialize {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s)
    (stream : List Bool) :
    let base := binBase a s q cy
    let stride := base^(s-1-p.val)
    let outer := base^s
    let wordSize := wordBase a s cy
    let b := code.val%outer
    let k := b/stride
    let d := k%base
    let init := MatrixStage4ColumnMachine.cfg
      (some MatrixStage4ColumnMachine.outerStart)
      MatrixStage4ColumnMachine.initial
      (List.replicate code.val true) (List.replicate outer true)
      (List.replicate stride true) (List.replicate base true)
      (List.replicate wordSize true) [] [] [] [] [] [] [] []
    ∃ t ≤ MatrixUnaryDivision.totalTime code.val outer+
      MatrixUnaryDivision.totalTime b stride+
      MatrixUnaryDivision.totalTime k base+
      MatrixUnaryDivision.totalTime d wordSize+1+
      (2*selectorDigit code p+4),
      (run t (columnFrame stream init)).l = none ∧
      (run t (columnFrame stream init)).stk 15 =
        List.replicate (selectorDigit code p) true ∧
      (run t (columnFrame stream init)).stk 16 =
        List.replicate (selectorDigit code p) true ++ false::stream := by
  dsimp
  obtain ⟨tc,htc,hc⟩ := MatrixStage4ColumnMachine.raw_column_run code p
  let init := MatrixStage4ColumnMachine.cfg
    (some MatrixStage4ColumnMachine.outerStart)
    MatrixStage4ColumnMachine.initial
    (List.replicate code.val true)
    (List.replicate (binBase a s q cy ^ s) true)
    (List.replicate (binBase a s q cy ^ (s - 1 - p.val)) true)
    (List.replicate (binBase a s q cy) true)
    (List.replicate (wordBase a s cy) true) [] [] [] [] [] [] [] []
  have hh : (MatrixStage4ColumnMachine.run tc init).l = none := by
    rw [hc]
    rfl
  have hs : (MatrixStage4ColumnMachine.run tc init).stk 15 =
      List.replicate (selectorDigit code p) true := by
    rw [hc]
    rw [← selector_value]
    rfl
  have hz : (MatrixStage4ColumnMachine.run tc init).stk 11 = [] := by
    rw [hc]
    rfl
  obtain ⟨t,ht,h1,h2,h3⟩ :=
    selected_bin_serialize_outputs init stream tc
      (selectorDigit code p) hh hs hz
  refine ⟨t, ?_, h1, h2, h3⟩
  dsimp at htc ⊢
  omega

end EthInapproximability.CurrentPaper.MatrixStage4ColumnSerialize
