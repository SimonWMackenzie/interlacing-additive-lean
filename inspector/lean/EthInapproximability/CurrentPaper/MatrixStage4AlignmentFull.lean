import EthInapproximability.CurrentPaper.MatrixStage4LowDigitStream
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Fixed variable-bin stream producer followed by physical alignment comparison

The input bank contains the unary raw bin code, bin base, word base, and
bin-count fuel. This controller itself does not yet split the original raw
column ordinal into its bin code and tail code.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4AlignmentFull

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 14
abbrev Label := MatrixStage4LowDigitStream.Label ⊕
  (MatrixStage4AlignmentStream.Label ⊕ Unit)
abbrev Control := MatrixStage4LowDigitStream.Control ×
  MatrixStage4AlignmentStream.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def lowStart : Label := .inl MatrixStage4LowDigitStream.firstStart
def alignStart : Label := .inr (.inl .start)
def done : Label := .inr (.inr ())

def lowStacks : Fin 14 ⊕ Fin 0 ≃ Stack := finSumFinEquiv

def alignPermutation : Stack ≃ Stack where
  toFun := ![11,9,12,0,1,2,3,4,5,6,7,8,10,13]
  invFun := ![3,4,5,6,7,8,9,10,11,1,12,0,2,13]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def alignStacks : Fin 3 ⊕ Fin 11 ≃ Stack :=
  finSumFinEquiv.trans alignPermutation

def alignLabels : MatrixStage4AlignmentStream.Label ⊕
    (MatrixStage4LowDigitStream.Label ⊕ Unit) ≃ Label where
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

def alignControl : MatrixStage4AlignmentStream.Control ×
    MatrixStage4LowDigitStream.Control ≃ Control := Equiv.prodComm _ _

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt lowStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixStage4AlignmentStream.Label.start))
        (MatrixStage4LowDigitStream.program l))
  | .inr (.inl l) => renameStmt alignStacks alignLabels alignControl
      (liftStmt (some (.inr ())) (MatrixStage4AlignmentStream.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def lowFrame (c : MatrixStage4LowDigitStream.Config) : Config :=
  renameCfg lowStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixStage4AlignmentStream.Label.start))
      MatrixStage4AlignmentStream.initial
      (fun j : Fin 0 => nomatch j) c)

theorem low_phase (c : MatrixStage4LowDigitStream.Config) (bound : ℕ)
    (hhalt : (MatrixStage4LowDigitStream.run bound c).l = none) :
    ∃ t ≤ bound, run t (lowFrame c) =
      lowFrame (MatrixStage4LowDigitStream.run bound c) := by
  apply lift_outputs_renamed lowStacks (Equiv.refl _) (Equiv.refl _)
    MatrixStage4LowDigitStream.program program
    (some (.inl MatrixStage4AlignmentStream.Label.start))
  · intro l
    rfl
  · exact hhalt

def alignFrame (bank : Fin 11 → List Bool)
    (lowControl : MatrixStage4LowDigitStream.Control)
    (c : MatrixStage4AlignmentStream.Config) : Config :=
  renameCfg alignStacks alignLabels alignControl
    (liftCfg (some (.inr ())) lowControl bank c)

theorem align_phase (bank : Fin 11 → List Bool)
    (lowControl : MatrixStage4LowDigitStream.Control)
    (c : MatrixStage4AlignmentStream.Config) (bound : ℕ)
    (hhalt : (MatrixStage4AlignmentStream.run bound c).l = none) :
    ∃ t ≤ bound, run t (alignFrame bank lowControl c) =
      alignFrame bank lowControl (MatrixStage4AlignmentStream.run bound c) := by
  apply lift_outputs_renamed alignStacks alignLabels alignControl
    MatrixStage4AlignmentStream.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def alignForeign (c : Config) : Fin 11 → List Bool :=
  fun j => c.stk (alignStacks (.inr j))

theorem bridge (c : MatrixStage4LowDigitStream.Config) (hc : c.l = none) :
    lowFrame c =
      alignFrame (alignForeign (lowFrame c)) c.var
        (MatrixStage4AlignmentStream.cfg (some .start)
          MatrixStage4AlignmentStream.initial
          (c.stk 11) (c.stk 9) (c.stk 12)) := by
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      unfold lowFrame alignFrame alignForeign renameCfg liftCfg
      congr 1
      funext k
      fin_cases k <;> rfl

theorem done_run (v : Control) (S : Stack → List Bool) :
    run 1 (⟨some done,v,S⟩ : Config) = ⟨none,v,S⟩ := by
  simp [run,advance,done,program,TM2.step,TM2.stepAux]

theorem align_after_low (c : MatrixStage4LowDigitStream.Config)
    (bound q : ℕ) (ps : List ℕ)
    (hhalt : (MatrixStage4LowDigitStream.run bound c).l = none)
    (hstream : (MatrixStage4LowDigitStream.run bound c).stk 11 =
      MatrixStage4AlignmentStream.words ps)
    (href : (MatrixStage4LowDigitStream.run bound c).stk 9 =
      List.replicate q true)
    (hscratch : (MatrixStage4LowDigitStream.run bound c).stk 12 = []) :
    ∃ t ≤ bound + MatrixStage4AlignmentStream.budget ps q + 2,
      (run t (lowFrame c)).l = none ∧
      (run t (lowFrame c)).var.2.1 =
        ps.all (fun p => decide (p=q)) := by
  let d := MatrixStage4LowDigitStream.run bound c
  let bank := alignForeign (lowFrame d)
  obtain ⟨t₁,ht₁,h₁⟩ := low_phase c bound hhalt
  have hb : lowFrame d = alignFrame bank d.var
      (MatrixStage4AlignmentStream.cfg (some .start)
        MatrixStage4AlignmentStream.initial
        (MatrixStage4AlignmentStream.words ps)
        (List.replicate q true) []) := by
    simpa only [d,bank,hstream,href,hscratch] using bridge d hhalt
  obtain ⟨ta,hta,ha⟩ := MatrixStage4AlignmentStream.words_halt ps q
  have hahalt : (MatrixStage4AlignmentStream.run ta
      (MatrixStage4AlignmentStream.cfg (some .start)
        MatrixStage4AlignmentStream.initial
        (MatrixStage4AlignmentStream.words ps)
        (List.replicate q true) [])).l = none := by
    rw [ha]
    rfl
  obtain ⟨t₂,ht₂,h₂⟩ := align_phase bank d.var
    (MatrixStage4AlignmentStream.cfg (some .start)
      MatrixStage4AlignmentStream.initial
      (MatrixStage4AlignmentStream.words ps)
      (List.replicate q true) []) ta hahalt
  rw [ha] at h₂
  let terminal := alignFrame bank d.var
    (MatrixStage4AlignmentStream.cfg none
      (ps.all (fun p => decide (p=q)),none,none)
      [] (List.replicate q true) [])
  have hd : run 1 terminal = ⟨none,terminal.var,terminal.stk⟩ := by
    change run 1 (⟨some done,terminal.var,terminal.stk⟩ : Config) = _
    exact done_run terminal.var terminal.stk
  have h12 := run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := run_add h12 1
  rw [hd] at h123
  refine ⟨t₁+t₂+1, by omega, ?_, ?_⟩
  · rw [h123]
  · rw [h123]
    rfl

open MatrixStage4Codes MatrixStage4Digits MatrixStage4AlignmentDigits
open Construction

theorem raw_bin_alignment_run {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    let base := binBase a s q cy
    let wordSize := wordBase a s cy
    let n := code.val % base^s
    let reference := selectorDigit code (firstBin s hs)
    let c := MatrixStage4LowDigitStream.loopCfg
      (some MatrixStage4LowDigitStream.firstStart) (false,none)
      (List.replicate n true) [] [] [] []
      (List.replicate (s-1) true)
      (List.replicate base true) (List.replicate wordSize true)
    ∃ t ≤ MatrixStage4LowDigitStream.timeBudget n base wordSize (s-1)+
      MatrixStage4AlignmentStream.budget
        (MatrixStage4AlignmentCorrect.selectorWords code) reference+2,
      (run t (lowFrame c)).l = none ∧
      ((run t (lowFrame c)).var.2.1 = true ↔
        aligned hs ((rawColumnCode a s q cy).symm code)) := by
  dsimp
  obtain ⟨tb,htb,hhalt,hscratch,href,hstream⟩ :=
    MatrixStage4LowDigitStream.raw_bin_stream_run hs code
  let base := binBase a s q cy
  let wordSize := wordBase a s cy
  let n := code.val % base^s
  let c := MatrixStage4LowDigitStream.loopCfg
    (some MatrixStage4LowDigitStream.firstStart) (false,none)
    (List.replicate n true) [] [] [] []
    (List.replicate (s-1) true)
    (List.replicate base true) (List.replicate wordSize true)
  obtain ⟨t,ht,he,hbit⟩ := align_after_low c tb
    (selectorDigit code (firstBin s hs))
    (MatrixStage4AlignmentCorrect.selectorWords code)
    hhalt hstream href hscratch
  refine ⟨t, by omega, he, ?_⟩
  rw [hbit]
  exact MatrixStage4AlignmentCorrect.selectorWords_all_iff hs code

end EthInapproximability.CurrentPaper.MatrixStage4AlignmentFull
