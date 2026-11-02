import CurrentAdditive.GaussFetchFromBackups64

/-! A fixed four-fetch circuit for one Gauss cell request. The inputs are one
canonical nested V2 matrix and four immutable unary index backups. -/

namespace CurrentAdditive.GaussFourOperands64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

def stageStart : GaussFetchFromBackups64.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0)))

def stageControl : GaussFetchFromBackups64.Control :=
  (((((), none), ((), none)), ((), none)),
    (GaussFetchSave64.fetchControl, ((), none)))

def stage00 := GaussFetchFromBackups64.program 0 0 24
def stage01 := GaussFetchFromBackups64.program 0 1 25
def stage10 := GaussFetchFromBackups64.program 1 0 26
def stage11 := GaussFetchFromBackups64.program 1 1 27

def firstTwo := BitMachineRawSequence.program
  stage00 stage01 stageStart stageControl stageControl

def firstThree := BitMachineRawSequence.program
  firstTwo stage10 stageStart (stageControl, stageControl) stageControl

def program := BitMachineRawSequence.program
  firstThree stage11 stageStart
    ((stageControl, stageControl), stageControl) stageControl

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      GaussFetchFromBackups64.Label
      GaussFetchFromBackups64.Label)
    GaussFetchFromBackups64.Label)
  GaussFetchFromBackups64.Label

abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control
    (BitMachineRawSequence.Control
      GaussFetchFromBackups64.Control
      GaussFetchFromBackups64.Control)
    GaussFetchFromBackups64.Control)
  GaussFetchFromBackups64.Control

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial (S : Stack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel stageStart))),
    (((stageControl, stageControl), stageControl), stageControl), S⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem stage_initial (S : Stack → List Bool) :
    GaussFetchFromBackups64.initial S =
      ⟨some stageStart, stageControl, S⟩ := rfl

theorem stage_run_exact (rowChoice columnChoice : Fin 2)
    (target : Stack) (S : Stack → List Bool) (t : Nat)
    (hhalt : (GaussFetchFromBackups64.run rowChoice columnChoice
      target t (GaussFetchFromBackups64.initial S)).l = none) :
    let F := GaussFetchFromBackups64.run rowChoice columnChoice
      target t (GaussFetchFromBackups64.initial S)
    ((advance (GaussFetchFromBackups64.program
      rowChoice columnChoice target))^[t])
      (⟨some stageStart, stageControl, S⟩ :
        GaussFetchFromBackups64.Config) =
      ⟨none, F.var, F.stk⟩ := by
  dsimp only
  rw [← stage_initial S]
  change GaussFetchFromBackups64.run rowChoice columnChoice target t
    (GaussFetchFromBackups64.initial S) = _
  cases hF : GaussFetchFromBackups64.run rowChoice columnChoice target t
      (GaussFetchFromBackups64.initial S) with
  | mk l v T =>
    cases l with
    | none => rfl
    | some l =>
      rw [hF] at hhalt
      contradiction

#print axioms stage_run_exact

def fourClock (S S1 S2 S3 : Stack → List Bool)
    (matrix current columnCell rowCell pivotCell : List Bool)
    (rowA rowB colJ colC : Nat) : Nat :=
  GaussFetchFromBackups64.clock 0 0 S rowA colJ matrix current +
  GaussFetchFromBackups64.clock 0 1 S1 rowA colC matrix columnCell +
  GaussFetchFromBackups64.clock 1 0 S2 rowB colJ matrix rowCell +
  GaussFetchFromBackups64.clock 1 1 S3 rowB colC matrix pivotCell + 3

theorem four_operands
    (S : Stack → List Bool)
    (matrix current columnCell rowCell pivotCell : List Bool)
    (rowA rowB colJ colC : Nat)
    (hmat : S 8 = matrix)
    (hcurrent : GaussFetchFromBackups64.CellAt matrix rowA colJ current)
    (hcolumnCell : GaussFetchFromBackups64.CellAt matrix rowA colC columnCell)
    (hrowCell : GaussFetchFromBackups64.CellAt matrix rowB colJ rowCell)
    (hpivotCell : GaussFetchFromBackups64.CellAt matrix rowB colC pivotCell)
    (hrowA : S 17 = List.replicate rowA true)
    (hrowB : S 18 = List.replicate rowB true)
    (hcolJ : S 19 = List.replicate colJ true)
    (hcolC : S 20 = List.replicate colC true)
    (htemp : S 63 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (h26 : S 26 = []) (h27 : S 27 = []) :
    ∃ t : Nat, ∃ S1 S2 S3 : Stack → List Bool,
      t ≤ fourClock S S1 S2 S3 matrix current columnCell
        rowCell pivotCell rowA rowB colJ colC ∧
      (run t (initial S)).l = none ∧
      (run t (initial S)).stk 8 = matrix ∧
      (run t (initial S)).stk 24 = current ∧
      (run t (initial S)).stk 25 = columnCell ∧
      (run t (initial S)).stk 26 = rowCell ∧
      (run t (initial S)).stk 27 = pivotCell ∧
      (run t (initial S)).stk 63 = [] ∧
      (∀ j : Stack, j.val < 32 → j ≠ 15 → j ≠ 16 →
        j ≠ 24 → j ≠ 25 → j ≠ 26 → j ≠ 27 →
        (run t (initial S)).stk j = S j) := by
  obtain ⟨t0, ht0, hh0, hc0, hm0, hf0, he0⟩ :=
    GaussFetchFromBackups64.fetch_cell_at 0 0 24
      (by decide) (by decide) matrix current rowA colJ S
      hmat hcurrent
      (by simpa [GaussLoadIndices64.rowBank] using hrowA)
      (by simpa [GaussLoadIndices64.columnBank] using hcolJ)
      htemp h24
  let F0 := GaussFetchFromBackups64.run 0 0 24 t0
    (GaussFetchFromBackups64.initial S)
  let S1 := F0.stk
  have hS1other (j : Stack) (hj : j.val < 32)
      (hj24 : j ≠ 24) (hj15 : j ≠ 15) (hj16 : j ≠ 16) :
      S1 j = S j := hf0 j hj hj24 hj15 hj16
  have hS1rowA : S1 17 = List.replicate rowA true :=
    (hS1other 17 (by decide) (by decide) (by decide) (by decide)).trans hrowA
  have hS1colC : S1 20 = List.replicate colC true :=
    (hS1other 20 (by decide) (by decide) (by decide) (by decide)).trans hcolC
  have hS1blank25 : S1 25 = [] :=
    (hS1other 25 (by decide) (by decide) (by decide) (by decide)).trans h25
  obtain ⟨t1, ht1, hh1, hc1, hm1, hf1, he1⟩ :=
    GaussFetchFromBackups64.fetch_cell_at 0 1 25
      (by decide) (by decide) matrix columnCell rowA colC S1
      hm0 hcolumnCell
      (by simpa [GaussLoadIndices64.rowBank] using hS1rowA)
      (by simpa [GaussLoadIndices64.columnBank] using hS1colC)
      he0 hS1blank25
  let F1 := GaussFetchFromBackups64.run 0 1 25 t1
    (GaussFetchFromBackups64.initial S1)
  let S2 := F1.stk
  have hS2other (j : Stack) (hj : j.val < 32)
      (hj24 : j ≠ 24) (hj25 : j ≠ 25)
      (hj15 : j ≠ 15) (hj16 : j ≠ 16) :
      S2 j = S j :=
    (hf1 j hj hj25 hj15 hj16).trans (hS1other j hj hj24 hj15 hj16)
  have hS2rowB : S2 18 = List.replicate rowB true :=
    (hS2other 18 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hrowB
  have hS2colJ : S2 19 = List.replicate colJ true :=
    (hS2other 19 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hcolJ
  have hS2blank26 : S2 26 = [] :=
    (hS2other 26 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h26
  obtain ⟨t2, ht2, hh2, hc2, hm2, hf2, he2⟩ :=
    GaussFetchFromBackups64.fetch_cell_at 1 0 26
      (by decide) (by decide) matrix rowCell rowB colJ S2
      hm1 hrowCell
      (by simpa [GaussLoadIndices64.rowBank] using hS2rowB)
      (by simpa [GaussLoadIndices64.columnBank] using hS2colJ)
      he1 hS2blank26
  let F2 := GaussFetchFromBackups64.run 1 0 26 t2
    (GaussFetchFromBackups64.initial S2)
  let S3 := F2.stk
  have hS3other (j : Stack) (hj : j.val < 32)
      (hj24 : j ≠ 24) (hj25 : j ≠ 25) (hj26 : j ≠ 26)
      (hj15 : j ≠ 15) (hj16 : j ≠ 16) :
      S3 j = S j :=
    (hf2 j hj hj26 hj15 hj16).trans
      (hS2other j hj hj24 hj25 hj15 hj16)
  have hS3rowB : S3 18 = List.replicate rowB true :=
    (hS3other 18 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hrowB
  have hS3colC : S3 20 = List.replicate colC true :=
    (hS3other 20 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hcolC
  have hS3blank27 : S3 27 = [] :=
    (hS3other 27 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h27
  obtain ⟨t3, ht3, hh3, hc3, hm3, hf3, he3⟩ :=
    GaussFetchFromBackups64.fetch_cell_at 1 1 27
      (by decide) (by decide) matrix pivotCell rowB colC S3
      hm2 hpivotCell
      (by simpa [GaussLoadIndices64.rowBank] using hS3rowB)
      (by simpa [GaussLoadIndices64.columnBank] using hS3colC)
      he2 hS3blank27
  let F3 := GaussFetchFromBackups64.run 1 1 27 t3
    (GaussFetchFromBackups64.initial S3)
  let S4 := F3.stk
  have hS4current : S4 24 = current :=
    (hf3 24 (by decide) (by decide) (by decide) (by decide)).trans
      ((hf2 24 (by decide) (by decide) (by decide) (by decide)).trans
        ((hf1 24 (by decide) (by decide) (by decide) (by decide)).trans hc0))
  have hS4column : S4 25 = columnCell :=
    (hf3 25 (by decide) (by decide) (by decide) (by decide)).trans
      ((hf2 25 (by decide) (by decide) (by decide) (by decide)).trans hc1)
  have hS4row : S4 26 = rowCell :=
    (hf3 26 (by decide) (by decide) (by decide) (by decide)).trans hc2
  have hS4pivot : S4 27 = pivotCell := hc3
  have hRun0 :
      ((advance stage00)^[t0])
        (⟨some stageStart, stageControl, S⟩ :
          GaussFetchFromBackups64.Config) =
        ⟨none, F0.var, S1⟩ := by
    simpa [stage00] using stage_run_exact 0 0 24 S t0 hh0
  have hRun1 :
      ((advance stage01)^[t1])
        (⟨some stageStart, stageControl, S1⟩ :
          GaussFetchFromBackups64.Config) =
        ⟨none, F1.var, S2⟩ := by
    simpa [stage01] using stage_run_exact 0 1 25 S1 t1 hh1
  have hRun2 :
      ((advance stage10)^[t2])
        (⟨some stageStart, stageControl, S2⟩ :
          GaussFetchFromBackups64.Config) =
        ⟨none, F2.var, S3⟩ := by
    simpa [stage10] using stage_run_exact 1 0 26 S2 t2 hh2
  have hRun3 :
      ((advance stage11)^[t3])
        (⟨some stageStart, stageControl, S3⟩ :
          GaussFetchFromBackups64.Config) =
        ⟨none, F3.var, S4⟩ := by
    simpa [stage11] using stage_run_exact 1 1 27 S3 t3 hh3
  obtain ⟨u, hu, h01⟩ := BitMachineRawSequence.runs
    stage00 stage01 stageStart stageStart
    stageControl F0.var stageControl F1.var
    S S1 S2 t0 t1 hRun0 hRun1
  obtain ⟨v, hv, h012⟩ := BitMachineRawSequence.runs
    firstTwo stage10 (BitMachineRawSequence.leftLabel stageStart)
    stageStart (stageControl, stageControl)
    (stageControl, F1.var) stageControl F2.var
    S S2 S3 u t2 h01 hRun2
  obtain ⟨t, ht, h0123⟩ := BitMachineRawSequence.runs
    firstThree stage11
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel stageStart))
    stageStart ((stageControl, stageControl), stageControl)
    ((stageControl, stageControl), F2.var)
    stageControl F3.var
    S S3 S4 v t3 h012 hRun3
  have heq : run t (initial S) =
      ⟨none, (((stageControl, stageControl), stageControl), F3.var),
        S4⟩ := by
    simpa [run, initial, program, firstThree, firstTwo] using h0123
  refine ⟨t, S1, S2, S3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold fourClock
    omega
  · rw [heq]
  · rw [heq]
    exact hm3
  · rw [heq]
    exact hS4current
  · rw [heq]
    exact hS4column
  · rw [heq]
    exact hS4row
  · rw [heq]
    exact hS4pivot
  · rw [heq]
    exact he3
  · intro j hj hj15 hj16 hj24 hj25 hj26 hj27
    rw [heq]
    exact (hf3 j hj hj27 hj15 hj16).trans
      (hS3other j hj hj24 hj25 hj26 hj15 hj16)

#print axioms four_operands

end CurrentAdditive.GaussFourOperands64
