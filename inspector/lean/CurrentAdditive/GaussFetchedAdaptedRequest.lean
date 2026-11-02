import CurrentAdditive.GaussAdaptSerialize64
import CurrentAdditive.GaussRequestTypedBridge64


set_option maxHeartbeats 2000000

/-! Concrete fetch, pivot-row adaptation and serialization. The matrix and
four unary addresses are physical inputs; no expanded request is assumed. -/
namespace CurrentAdditive.GaussFetchedAdaptedRequest

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
abbrev Stack := Fin 64

def fourStart : GaussFourOperands64.Label :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel GaussFourOperands64.stageStart))

def fourControl : GaussFourOperands64.Control :=
  (((GaussFourOperands64.stageControl, GaussFourOperands64.stageControl),
    GaussFourOperands64.stageControl), GaussFourOperands64.stageControl)

def fetchedAdapted := BitMachineRawSequence.program
  GaussFourOperands64.program GaussAdaptPrepare64.program
  .start fourControl ((), none)

def program := BitMachineRawSequence.program
  fetchedAdapted GaussOperandSerialize64.program
  (.emit 0) (fourControl, ((), none)) none

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label GaussFourOperands64.Label
    GaussAdaptPrepare64.Label) GaussOperandSerialize64.Label
abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control GaussFourOperands64.Control
    GaussAdaptPrepare64.Control) GaussOperandSerialize64.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial (S : Stack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel fourStart)),
    ((fourControl, ((), none)), none), S⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def adjustedCurrent (flag : Bool) (current : List Bool) :=
  if flag then GaussAdaptPrepare64.zeroWord else current

def adjustedColumn (flag : Bool) (column : List Bool) :=
  if flag then GaussAdaptPrepare64.minusOneWord else column

def packet (flag : Bool) (current column row pivot : List Bool) :=
  GaussOperandSerialize64.packet false
    (adjustedCurrent flag current) (adjustedColumn flag column) row pivot

theorem physical_request
    (S : Stack → List Bool)
    (matrix current column row pivot : List Bool)
    (rowA rowB colJ colC : Nat) (flag : Bool)
    (hmat : S 8 = matrix)
    (hcurrent : GaussFetchFromBackups64.CellAt matrix rowA colJ current)
    (hcolumn : GaussFetchFromBackups64.CellAt matrix rowA colC column)
    (hrow : GaussFetchFromBackups64.CellAt matrix rowB colJ row)
    (hpivot : GaussFetchFromBackups64.CellAt matrix rowB colC pivot)
    (hrowA : S 17 = List.replicate rowA true)
    (hrowB : S 18 = List.replicate rowB true)
    (hcolJ : S 19 = List.replicate colJ true)
    (hcolC : S 20 = List.replicate colC true)
    (hflag : S 28 = [flag])
    (hempty : ∀ j : Stack, j.val < 7 → S j = [])
    (h21 : S 21 = []) (h22 : S 22 = []) (h23 : S 23 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (h26 : S 26 = []) (h27 : S 27 = []) (h63 : S 63 = []) :
    ∃ t : Nat, ∃ S1 S2 S3 : Stack → List Bool,
      t ≤ GaussFourOperands64.fourClock S S1 S2 S3
          matrix current column row pivot rowA rowB colJ colC +
        GaussAdaptPrepare64.time flag current column +
        2 * (packet flag current column row pivot).length + 4 ∧
      (run t (initial S)).l = none ∧
      (run t (initial S)).stk 23 = packet flag current column row pivot ∧
      (run t (initial S)).stk 8 = matrix ∧
      (∀ z : Stack, 7 ≤ z.val → z.val < 32 → z ≠ 15 → z ≠ 16 →
        z ≠ 21 → z ≠ 22 → z ≠ 23 →
        z ≠ 24 → z ≠ 25 → z ≠ 26 → z ≠ 27 → z ≠ 28 →
        (run t (initial S)).stk z = S z) := by
  obtain ⟨a,S1,S2,S3,ha,hh,hm,hcur,hcol,hr,hp,he,hforeign⟩ :=
    GaussFourOperands64.four_operands S matrix current column row pivot
      rowA rowB colJ colC hmat hcurrent hcolumn hrow hpivot
      hrowA hrowB hcolJ hcolC h63 h24 h25 h26 h27
  let F := GaussFourOperands64.run a (GaussFourOperands64.initial S)
  let T := F.stk
  have hTflag : T 28 = [flag] :=
    (hforeign 28 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hflag
  let U := GaussAdaptPrepare64.prepared T flag
  have hUother (z : Stack) (hz24 : z ≠ 24) (hz25 : z ≠ 25)
      (hz28 : z ≠ 28) : U z = T z := by
    cases flag <;> simp [U,GaussAdaptPrepare64.prepared,hz24,hz25,hz28]
  have hUflag : U 28 = [false] := by
    cases flag <;> simp [U,GaussAdaptPrepare64.prepared,hTflag]
  have hUcur : U 24 = adjustedCurrent flag current := by
    cases flag <;> simp [U,GaussAdaptPrepare64.prepared,adjustedCurrent,hcur,T,F]
  have hUcol : U 25 = adjustedColumn flag column := by
    cases flag <;> simp [U,GaussAdaptPrepare64.prepared,adjustedColumn,hcol,T,F]
  have hUrow : U 26 = row := (hUother 26 (by decide) (by decide) (by decide)).trans hr
  have hUpivot : U 27 = pivot := (hUother 27 (by decide) (by decide) (by decide)).trans hp
  have hUempty : ∀ j : Stack, j.val < 7 → U j = [] := by
    intro j hj
    rw [hUother j (by intro h; have := congrArg Fin.val h; omega)
      (by intro h; have := congrArg Fin.val h; omega)
      (by intro h; have := congrArg Fin.val h; omega)]
    exact (hforeign j (by omega)
      (by intro h; have := congrArg Fin.val h; omega)
      (by intro h; have := congrArg Fin.val h; omega)
      (by intro h; have := congrArg Fin.val h; omega)
      (by intro h; have := congrArg Fin.val h; omega)
      (by intro h; have := congrArg Fin.val h; omega)
      (by intro h; have := congrArg Fin.val h; omega)).trans (hempty j hj)
  have hUscratch (z : Stack) (hz : z = 21 ∨ z = 22 ∨ z = 23) : U z = [] := by
    rcases hz with rfl | rfl | rfl
    all_goals rw [hUother _ (by decide) (by decide) (by decide)]
    · exact (hforeign 21 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans h21
    · exact (hforeign 22 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans h22
    · exact (hforeign 23 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans h23
  have hwords := GaussOperandSerialize64.prepared_words false
    (adjustedCurrent flag current) (adjustedColumn flag column) row pivot
    U hUflag hUcur hUcol hUrow hUpivot hUempty
  obtain ⟨b,hb,hser⟩ := GaussAdaptSerialize64.full_run false
    (adjustedCurrent flag current) (adjustedColumn flag column) row pivot U
    hwords (hUscratch 21 (by simp)) (hUscratch 22 (by simp))
      (hUscratch 23 (by simp))
  let V := GaussAdaptSerialize64.finalBank U
    (packet flag current column row pivot) (fun _ => [])
  have hFour : ((advance GaussFourOperands64.program)^[a])
      (⟨some fourStart,fourControl,S⟩ : GaussFourOperands64.Config) =
      ⟨none,F.var,T⟩ := by
    change F = ⟨none,F.var,F.stk⟩
    cases hF : F with
    | mk l v W =>
      cases l with
      | none => rfl
      | some l => have hx : F.l = none := hh; rw [hF] at hx; contradiction
  have hAdapt := GaussAdaptPrepare64.run T flag current column hTflag hcur hcol
  obtain ⟨u,hu,hpair⟩ := BitMachineRawSequence.runs
    GaussFourOperands64.program GaussAdaptPrepare64.program fourStart .start
    fourControl F.var ((),none) ((),none) S T U
    a (GaussAdaptPrepare64.time flag current column) hFour hAdapt
  obtain ⟨t,ht,hall⟩ := BitMachineRawSequence.runs
    fetchedAdapted GaussOperandSerialize64.program
    (BitMachineRawSequence.leftLabel fourStart) (.emit 0)
    (fourControl,((),none)) (fourControl,((),none)) none none S U V
    u b hpair hser
  have hrun : run t (initial S) =
      ⟨none,((fourControl,((),none)),none),V⟩ := by
    simpa only [run, initial, program] using hall
  have hbpacket : b ≤ 2*(packet flag current column row pivot).length+2 := hb
  refine ⟨t,S1,S2,S3,by omega,?_,?_,?_,?_⟩
  · rw [hrun]
  · rw [hrun]
    exact GaussAdaptSerialize64.output_at_23 U _ _
  · rw [hrun]
    change V 8 = matrix
    rw [show V 8 = U 8 from
      GaussAdaptSerialize64.foreign_at U _ _ 8 (by
        rintro ⟨i,hi⟩; cases i with
        | inl i => fin_cases i <;> simp_all [GaussOperandSerialize64.slot,GaussOperandSerialize64.fieldSlot]
        | inr i => fin_cases i <;> simp_all [GaussOperandSerialize64.slot,GaussOperandSerialize64.extraSlot])]
    exact (hUother 8 (by decide) (by decide) (by decide)).trans hm
  · intro z hzlow hz hz15 hz16 hz21 hz22 hz23 hz24 hz25 hz26 hz27 hz28
    rw [hrun]
    change V z = S z
    have hfz : ¬ ∃ i, GaussOperandSerialize64.slot i = z := by
      rintro ⟨i,hi⟩
      cases i with
      | inl i =>
        fin_cases i <;> simp_all [GaussOperandSerialize64.slot,
          GaussOperandSerialize64.fieldSlot]
        all_goals have hv := congrArg Fin.val hi; simp at hv; omega
      | inr i => fin_cases i <;> simp_all [GaussOperandSerialize64.slot,
          GaussOperandSerialize64.extraSlot]
    rw [show V z = U z from GaussAdaptSerialize64.foreign_at U _ _ z hfz,
      hUother z hz24 hz25 hz28]
    exact hforeign z hz hz15 hz16 hz24 hz25 hz26 hz27

#print axioms physical_request
end CurrentAdditive.GaussFetchedAdaptedRequest
