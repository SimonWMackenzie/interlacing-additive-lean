import EthInapproximability.CurrentPaper.MatrixStage4AlignmentFull
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical alignment directly from the raw-column ordinal

The first subroutine divides the unary raw ordinal by the supplied unary
bin-tuple base power. Its remainder enters the variable-bin decoder; its
quotient (the tail tuple code) remains in a foreign bank. Production of the
base-power scalar itself remains a separate charged stage.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4AlignmentFromOrdinal

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 19
abbrev Label := MatrixUnaryDivision.Label ⊕
  (MatrixStage4AlignmentFull.Label ⊕ Unit)
abbrev Control := Bool × MatrixStage4AlignmentFull.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def splitStart : Label := .inl .start
def alignmentStart : Label := .inr (.inl MatrixStage4AlignmentFull.lowStart)
def done : Label := .inr (.inr ())

def splitPermutation : Stack ≃ Stack where
  toFun := ![15,16,17,0,14,18,1,2,3,4,5,6,7,8,9,10,11,12,13]
  invFun := ![3,6,7,8,9,10,11,12,13,14,15,16,17,18,4,0,1,2,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def splitStacks : Fin 6 ⊕ Fin 13 ≃ Stack :=
  finSumFinEquiv.trans splitPermutation

def alignmentStacks : Fin 14 ⊕ Fin 5 ≃ Stack := finSumFinEquiv

def alignmentLabels : MatrixStage4AlignmentFull.Label ⊕
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

def alignmentControl : MatrixStage4AlignmentFull.Control × Bool ≃ Control :=
  Equiv.prodComm _ _

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt splitStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4AlignmentFull.lowStart))
        (MatrixUnaryDivision.program l))
  | .inr (.inl l) => renameStmt alignmentStacks alignmentLabels alignmentControl
      (liftStmt (some (.inr ())) (MatrixStage4AlignmentFull.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def splitFrame (base wordSize fuel : List Bool)
    (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg splitStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4AlignmentFull.lowStart))
      ((false,none),MatrixStage4AlignmentStream.initial)
      (fun i : Fin 13 => ![base,[],[],[],[],wordSize,[],[],[],[],[],[],fuel] i)
      c)

theorem split_phase (base wordSize fuel : List Bool)
    (c : MatrixUnaryDivision.Config) (bound : ℕ)
    (hhalt : (MatrixUnaryDivision.run bound c).l = none) :
    ∃ t ≤ bound, run t (splitFrame base wordSize fuel c) =
      splitFrame base wordSize fuel (MatrixUnaryDivision.run bound c) := by
  apply lift_outputs_renamed splitStacks (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryDivision.program program
    (some (.inl MatrixStage4AlignmentFull.lowStart))
  · intro l
    rfl
  · exact hhalt

def alignmentFrame (foreign : Fin 5 → List Bool)
    (splitControl : Bool) (c : MatrixStage4AlignmentFull.Config) : Config :=
  renameCfg alignmentStacks alignmentLabels alignmentControl
    (liftCfg (some (.inr ())) splitControl foreign c)

theorem alignment_phase (foreign : Fin 5 → List Bool)
    (splitControl : Bool) (c : MatrixStage4AlignmentFull.Config)
    (bound : ℕ) (hhalt : (MatrixStage4AlignmentFull.run bound c).l = none) :
    ∃ t ≤ bound, run t (alignmentFrame foreign splitControl c) =
      alignmentFrame foreign splitControl
        (MatrixStage4AlignmentFull.run bound c) := by
  apply lift_outputs_renamed alignmentStacks alignmentLabels alignmentControl
    MatrixStage4AlignmentFull.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def alignmentForeign (c : Config) : Fin 5 → List Bool :=
  fun j => c.stk (alignmentStacks (.inr j))

theorem bridge (base wordSize fuel : List Bool)
    (c : MatrixUnaryDivision.Config) (hc : c.l = none) :
    splitFrame base wordSize fuel c =
      alignmentFrame (alignmentForeign (splitFrame base wordSize fuel c)) c.var
        (MatrixStage4AlignmentFull.lowFrame
          (MatrixStage4LowDigitStream.loopCfg
            (some MatrixStage4LowDigitStream.firstStart) (false,none)
            (c.stk 3) [] [] [] [] fuel base wordSize)) := by
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      unfold splitFrame alignmentFrame alignmentForeign
        MatrixStage4AlignmentFull.lowFrame
        renameCfg liftCfg
      congr 1
      funext k
      fin_cases k <;> rfl

theorem done_run (v : Control) (S : Stack → List Bool) :
    run 1 (⟨some done,v,S⟩ : Config) = ⟨none,v,S⟩ := by
  simp [run,advance,done,program,TM2.step,TM2.stepAux]

theorem finish (c : Config) (hc : c.l = some done) :
    run 1 c = ⟨none,c.var,c.stk⟩ := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp at hc
    | some l =>
      have hl : l = done := Option.some.inj hc
      subst l
      exact done_run v S

open MatrixStage4Codes MatrixStage4Digits MatrixStage4AlignmentDigits
open Construction

theorem raw_ordinal_alignment_run {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    let base := binBase a s q cy
    let wordSize := wordBase a s cy
    let outer := base^s
    let n := code.val%outer
    let reference := selectorDigit code (firstBin s hs)
    let input := splitFrame
      (List.replicate base true) (List.replicate wordSize true)
      (List.replicate (s-1) true)
      (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate code.val true) (List.replicate outer true)
        [] [] [] [])
    ∃ t ≤ MatrixUnaryDivision.totalTime code.val outer+
      MatrixStage4LowDigitStream.timeBudget n base wordSize (s-1)+
      MatrixStage4AlignmentStream.budget
        (MatrixStage4AlignmentCorrect.selectorWords code) reference+3,
      (run t input).l = none ∧
      ((run t input).var.2.2.1 = true ↔
        aligned hs ((rawColumnCode a s q cy).symm code)) ∧
      (run t input).stk 14 = List.replicate (code.val/outer) true := by
  dsimp
  let base := binBase a s q cy
  let wordSize := wordBase a s cy
  let outer := base^s
  let n := code.val%outer
  let splitInput := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate code.val true) (List.replicate outer true)
    [] [] [] []
  let splitOutput := MatrixUnaryDivision.cfg none false
    [] (List.replicate outer true) []
    (List.replicate n true) (List.replicate (code.val/outer) true) []
  have hdiv : MatrixUnaryDivision.run
      (MatrixUnaryDivision.totalTime code.val outer) splitInput =
      splitOutput := MatrixUnaryDivision.division_total_run code.val outer
  obtain ⟨t₁,ht₁,h₁⟩ := split_phase
    (List.replicate base true) (List.replicate wordSize true)
    (List.replicate (s-1) true) splitInput
    (MatrixUnaryDivision.totalTime code.val outer)
    (by rw [hdiv]; rfl)
  rw [hdiv] at h₁
  let foreign := alignmentForeign
    (splitFrame (List.replicate base true)
      (List.replicate wordSize true) (List.replicate (s-1) true)
      splitOutput)
  let lowInput := MatrixStage4LowDigitStream.loopCfg
    (some MatrixStage4LowDigitStream.firstStart) (false,none)
    (List.replicate n true) [] [] [] []
    (List.replicate (s-1) true)
    (List.replicate base true) (List.replicate wordSize true)
  have hb : splitFrame (List.replicate base true)
      (List.replicate wordSize true) (List.replicate (s-1) true)
      splitOutput =
      alignmentFrame foreign false
        (MatrixStage4AlignmentFull.lowFrame lowInput) := by
    simpa only [splitOutput,foreign,lowInput] using
      bridge (List.replicate base true)
        (List.replicate wordSize true) (List.replicate (s-1) true)
        splitOutput (by rfl)
  obtain ⟨ta,hta,haltA,hbitA⟩ :=
    MatrixStage4AlignmentFull.raw_bin_alignment_run hs code
  obtain ⟨t₂,ht₂,h₂⟩ := alignment_phase foreign false
    (MatrixStage4AlignmentFull.lowFrame lowInput) ta
    (by simpa only [lowInput] using haltA)
  let terminal := alignmentFrame foreign false
    (MatrixStage4AlignmentFull.run ta
      (MatrixStage4AlignmentFull.lowFrame lowInput))
  have hlabel : terminal.l = some done := by
    dsimp [terminal,alignmentFrame,renameCfg,liftCfg]
    rw [show (MatrixStage4AlignmentFull.run ta
      (MatrixStage4AlignmentFull.lowFrame lowInput)).l = none by
        simpa only [lowInput] using haltA]
    rfl
  have hd := finish terminal hlabel
  have h12 := run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := run_add h12 1
  rw [hd] at h123
  refine ⟨t₁+t₂+1, ?_, ?_, ?_, ?_⟩
  · dsimp [outer,base,wordSize,n] at ht₁ hta ⊢
    omega
  · rw [h123]
  · rw [h123]
    simpa only [terminal,alignmentFrame,renameCfg,liftCfg,lowInput]
      using hbitA
  · rw [h123]
    rfl

end EthInapproximability.CurrentPaper.MatrixStage4AlignmentFromOrdinal
