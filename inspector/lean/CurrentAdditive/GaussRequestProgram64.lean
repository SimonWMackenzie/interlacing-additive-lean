import CurrentAdditive.GaussOperandSerialize64

/-! One fixed Fin64 program fetches the four encoded operands from the stored
matrix and serializes their five-field Bank12 arithmetic request. -/

namespace CurrentAdditive.GaussRequestProgram64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

def firstStart : GaussFourOperands64.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel GaussFourOperands64.stageStart))

def firstControl : GaussFourOperands64.Control :=
  (((GaussFourOperands64.stageControl,
      GaussFourOperands64.stageControl),
      GaussFourOperands64.stageControl),
      GaussFourOperands64.stageControl)

def program := BitMachineRawSequence.program
  GaussFourOperands64.program GaussOperandSerialize64.program
  (BitMachineBankSerialize.Label.emit 0) firstControl none

abbrev Label := BitMachineRawSequence.Label
  GaussFourOperands64.Label GaussOperandSerialize64.Label

abbrev Control := BitMachineRawSequence.Control
  GaussFourOperands64.Control GaussOperandSerialize64.Control

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial (S : Stack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel firstStart),
    (firstControl, none), S⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem first_initial (S : Stack → List Bool) :
    GaussFourOperands64.initial S =
      ⟨some firstStart, firstControl, S⟩ := rfl

theorem physical_request
    (S : Stack → List Bool)
    (matrix current columnCell rowCell pivotCell : List Bool)
    (rowA rowB colJ colC : Nat) (flag : Bool)
    (hmat : S 8 = matrix)
    (hcurrent : GaussFetchFromBackups64.CellAt matrix rowA colJ current)
    (hcolumnCell : GaussFetchFromBackups64.CellAt matrix rowA colC columnCell)
    (hrowCell : GaussFetchFromBackups64.CellAt matrix rowB colJ rowCell)
    (hpivotCell : GaussFetchFromBackups64.CellAt matrix rowB colC pivotCell)
    (hrowA : S 17 = List.replicate rowA true)
    (hrowB : S 18 = List.replicate rowB true)
    (hcolJ : S 19 = List.replicate colJ true)
    (hcolC : S 20 = List.replicate colC true)
    (hflag : S 28 = [flag])
    (hemptyFields : ∀ j : Stack, j.val < 7 → S j = [])
    (h21 : S 21 = []) (h22 : S 22 = []) (h23 : S 23 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (h26 : S 26 = []) (h27 : S 27 = [])
    (h63 : S 63 = []) :
    ∃ t : Nat, ∃ S1 S2 S3 : Stack → List Bool,
      t ≤ GaussFourOperands64.fourClock S S1 S2 S3
          matrix current columnCell rowCell pivotCell
          rowA rowB colJ colC +
        2 * (GaussOperandSerialize64.packet
          flag current columnCell rowCell pivotCell).length + 3 ∧
      (run t (initial S)).l = none ∧
      (run t (initial S)).stk 23 =
        GaussOperandSerialize64.packet
          flag current columnCell rowCell pivotCell ∧
      (run t (initial S)).stk 8 = matrix := by
  obtain ⟨tFour, S1, S2, S3, htFour, hhFour, hmFour,
    hcFour, hcolFour, hrFour, hpFour, h63Four, hforeign⟩ :=
    GaussFourOperands64.four_operands S matrix current columnCell
      rowCell pivotCell rowA rowB colJ colC hmat hcurrent
      hcolumnCell hrowCell hpivotCell hrowA hrowB hcolJ hcolC
      h63 h24 h25 h26 h27
  let F := GaussFourOperands64.run tFour (GaussFourOperands64.initial S)
  let T := F.stk
  have hflagT : T 28 = [flag] :=
    (hforeign 28 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hflag
  have hemptyT : ∀ j : Stack, j.val < 7 → T j = [] := by
    intro j hj
    exact (hforeign j (by omega)
      (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)).trans
      (hemptyFields j hj)
  have h21T : T 21 = [] :=
    (hforeign 21 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans h21
  have h22T : T 22 = [] :=
    (hforeign 22 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans h22
  have h23T : T 23 = [] :=
    (hforeign 23 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans h23
  have hwords := GaussOperandSerialize64.prepared_words
    flag current columnCell rowCell pivotCell T
    hflagT hcFour hcolFour hrFour hpFour hemptyT
  obtain ⟨tSer, htSer, hhSer, hpacket, hmSer⟩ :=
    GaussOperandSerialize64.physical_packet flag current
      columnCell rowCell pivotCell T hwords h21T h22T h23T
  let G := GaussOperandSerialize64.run tSer
    ⟨some (.emit 0), none, T⟩
  have hFourRun :
      ((advance GaussFourOperands64.program)^[tFour])
        (⟨some firstStart, firstControl, S⟩ :
          GaussFourOperands64.Config) =
        ⟨none, F.var, T⟩ := by
    rw [← first_initial S]
    change F = ⟨none, F.var, T⟩
    cases hF : F with
    | mk l v U =>
      cases l with
      | none => simp [T, hF]
      | some l =>
        have hh : F.l = none := hhFour
        rw [hF] at hh
        contradiction
  have hSerRun :
      ((advance GaussOperandSerialize64.program)^[tSer])
        (⟨some (.emit 0), none, T⟩ :
          GaussOperandSerialize64.Config) =
        ⟨none, G.var, G.stk⟩ := by
    change G = ⟨none, G.var, G.stk⟩
    cases hG : G with
    | mk l v U =>
      cases l with
      | none => rfl
      | some l =>
        have hh : G.l = none := hhSer
        rw [hG] at hh
        contradiction
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    GaussFourOperands64.program GaussOperandSerialize64.program
    firstStart (.emit 0) firstControl F.var none G.var
    S T G.stk tFour tSer hFourRun hSerRun
  have heq : run t (initial S) =
      ⟨none, (firstControl, G.var), G.stk⟩ := by
    simpa [run, initial, program] using hfull
  refine ⟨t, S1, S2, S3, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [heq]
  · rw [heq]
    exact hpacket
  · rw [heq]
    exact hmSer.trans hmFour

#print axioms physical_request

end CurrentAdditive.GaussRequestProgram64
