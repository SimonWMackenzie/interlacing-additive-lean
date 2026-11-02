import EthInapproximability.CurrentPaper.MatrixStage4SelectedPower
import EthInapproximability.CurrentPaper.MatrixStage4PayloadRead
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Literal source-table read after raw-column tail decoding

The fixed controller first computes a selected tail coordinate from the
original raw-column ordinal, then feeds the resulting unary coordinate to
the literal row-major lookup machine. It never receives the source answer
or a precomputed tail digit. The source-row index and several unary scalar
powers remain caller inputs, and this is not yet the full graph/template
raw-matrix entry callback.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TailSourceRead

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 31
abbrev Label := MatrixStage4TailFromOrdinal.Label ⊕
  (MatrixTableLookup.Label ⊕ Unit)
abbrev Control := MatrixStage4TailFromOrdinal.Control ×
  MatrixTableLookup.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def tailStart : Label := .inl MatrixStage4TailFromOrdinal.splitStart
def readStart : Label := .inr (.inl MatrixTableLookup.start)
def done : Label := .inr (.inr ())

def tailStacks : Fin 22 ⊕ Fin 9 ≃ Stack := finSumFinEquiv

def readPermutation : Stack ≃ Stack where
  toFun := ![22,23,15,24,25,26,27,28,29,30,
    0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,18,19,20,21]
  invFun := ![10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,
    2,25,26,27,28,29,30,0,1,3,4,5,6,7,8,9]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def readStacks : Fin 10 ⊕ Fin 21 ≃ Stack :=
  finSumFinEquiv.trans readPermutation

def readLabels : MatrixTableLookup.Label ⊕
    (MatrixStage4TailFromOrdinal.Label ⊕ Unit) ≃ Label where
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
  | .inl l => renameStmt tailStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixTableLookup.start))
        (MatrixStage4TailFromOrdinal.program l))
  | .inr (.inl l) => renameStmt readStacks readLabels
      (Equiv.prodComm _ _)
      (liftStmt (some (.inr ())) (MatrixTableLookup.program l))
  | .inr (.inr ()) => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

def tailFrame (row width source out : List Bool)
    (c : MatrixStage4TailFromOrdinal.Config) : Config :=
  renameCfg tailStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixTableLookup.start))
      MatrixTableLookup.initial
      (fun i : Fin 9 => ![row,width,[],[],[],source,out,[],[]] i) c)

theorem tail_phase (row width source out : List Bool)
    (c : MatrixStage4TailFromOrdinal.Config) (bound : ℕ)
    (hhalt : (MatrixStage4TailFromOrdinal.run bound c).l = none) :
    ∃ t ≤ bound, run t (tailFrame row width source out c) =
      tailFrame row width source out
        (MatrixStage4TailFromOrdinal.run bound c) := by
  apply lift_outputs_renamed tailStacks (Equiv.refl _) (Equiv.refl _)
    MatrixStage4TailFromOrdinal.program program
    (some (.inl MatrixTableLookup.start))
  · intro l
    rfl
  · exact hhalt

def readFrame (foreign : Fin 21 → List Bool)
    (tailControl : MatrixStage4TailFromOrdinal.Control)
    (c : MatrixTableLookup.Config) : Config :=
  renameCfg readStacks readLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr ())) tailControl foreign c)

theorem read_phase (foreign : Fin 21 → List Bool)
    (tailControl : MatrixStage4TailFromOrdinal.Control)
    (c : MatrixTableLookup.Config) (bound : ℕ)
    (hhalt : (MatrixTableLookup.run bound c).l = none) :
    ∃ t ≤ bound, run t (readFrame foreign tailControl c) =
      readFrame foreign tailControl (MatrixTableLookup.run bound c) := by
  apply lift_outputs_renamed readStacks readLabels (Equiv.prodComm _ _)
    MatrixTableLookup.program program (some (.inr ()))
  · intro l
    rfl
  · exact hhalt

def readForeign (c : Config) : Fin 21 → List Bool :=
  fun j => c.stk (readStacks (.inr j))

theorem bridge (row width source out : List Bool)
    (c : MatrixStage4TailFromOrdinal.Config) (hc : c.l = none) :
    tailFrame row width source out c =
      readFrame (readForeign (tailFrame row width source out c))
        c.var
        (MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial row width (c.stk 15) [] source out) := by
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      unfold tailFrame readFrame readForeign renameCfg liftCfg
        MatrixTableLookup.cfg
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

def tailBudget {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (j : Fin (s+1)) : ℕ :=
  let base := binBase a s q cy
  let tailCode := (tupleCode cy (s+1))
    (((rawColumnCode a s q cy).symm code).1)
  MatrixUnaryDivision.totalTime code.val (base^s) +
    MatrixUnaryDivision.totalTime tailCode.val (cy^(s+1)) +
    MatrixUnaryDivision.totalTime
      (tailCode.val % cy^(s+1)) (cy^(s-j.val)) +
    MatrixUnaryDivision.totalTime
      ((tailCode.val % cy^(s+1))/(cy^(s-j.val))) cy +
    MatrixUnaryDivision.totalTime
      (((tailCode.val % cy^(s+1))/(cy^(s-j.val))) % cy) 1 + 3

def tailInput {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (j : Fin (s+1)) :
    MatrixStage4TailFromOrdinal.Config :=
  MatrixStage4TailFromOrdinal.splitFrame (fun i : Fin 16 =>
      ![List.replicate (cy^(s+1)) true,
        List.replicate (cy^(s-j.val)) true,
        List.replicate cy true,[true],[],[],[],[],[],[],[],[],[],[],[],[]] i)
    (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate code.val true)
      (List.replicate ((binBase a s q cy)^s) true) [] [] [] [])

theorem source_after_tail_run {a s q rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (j : Fin (s+1))
    (x : Fin rx) (out : List Bool) :
    let y := ((rawColumnCode a s q cy).symm code).1 j
    let input := tailFrame (List.replicate x.val true)
      (List.replicate cy true) (rowMajor R) out (tailInput code j)
    ∃ t ≤ tailBudget code j +
      32*(x.val+cy+y.val+rx*cy+1)^2+2,
      (run t input).l = none ∧
      (run t input).stk 28 = R x y :: out := by
  dsimp
  let y := ((rawColumnCode a s q cy).symm code).1 j
  obtain ⟨tt,htt,hl,hy⟩ :=
    MatrixStage4TailFromOrdinal.raw_tail_digit_run code j
  obtain ⟨t₁,ht₁,h₁⟩ := tail_phase
    (List.replicate x.val true) (List.replicate cy true)
    (rowMajor R) out (tailInput code j) tt
    (by simpa only [tailInput] using hl)
  let tailResult := MatrixStage4TailFromOrdinal.run tt (tailInput code j)
  let foreign := readForeign (tailFrame (List.replicate x.val true)
    (List.replicate cy true) (rowMajor R) out tailResult)
  let readInput := MatrixTableLookup.cfg (some MatrixTableLookup.start)
    MatrixTableLookup.initial
    (List.replicate x.val true) (List.replicate cy true)
    (List.replicate y.val true) [] (rowMajor R) out
  have hb : tailFrame (List.replicate x.val true)
      (List.replicate cy true) (rowMajor R) out tailResult =
      readFrame foreign tailResult.var readInput := by
    have hbridge := bridge (List.replicate x.val true)
      (List.replicate cy true) (rowMajor R) out tailResult
      (by simpa only [tailResult,tailInput] using hl)
    simpa only [foreign,readInput,tailResult,
      show (MatrixStage4TailFromOrdinal.run tt (tailInput code j)).stk 15 =
        List.replicate y.val true by simpa only [tailInput,y] using hy]
      using hbridge
  obtain ⟨tr,htr,hr⟩ := MatrixStage4PayloadRead.source_run R x y out
  have hhalt : (MatrixTableLookup.run tr readInput).l = none := by
    simpa only [readInput] using congrArg
      (fun c : MatrixTableLookup.Config => c.l) hr
  obtain ⟨t₂,ht₂,h₂⟩ := read_phase foreign tailResult.var
    readInput tr hhalt
  let terminal := readFrame foreign tailResult.var
    (MatrixTableLookup.run tr readInput)
  have hlabel : terminal.l = some done := by
    dsimp [terminal,readFrame,renameCfg,liftCfg]
    rw [hhalt]
    rfl
  have hfinal := finish terminal hlabel
  have h12 := run_add h₁ t₂
  rw [hb,h₂] at h12
  have h123 := run_add h12 1
  rw [hfinal] at h123
  refine ⟨t₁+t₂+1,?_,?_,?_⟩
  · dsimp [tailBudget,y] at htt ⊢
    dsimp [y] at htr
    omega
  · rw [h123]
  · rw [h123]
    have hout := congrArg (fun c : MatrixTableLookup.Config => c.stk 7) hr
    simpa only [terminal,readFrame,renameCfg,liftCfg,readInput,
      MatrixTableLookup.cfg] using hout

end EthInapproximability.CurrentPaper.MatrixStage4TailSourceRead
