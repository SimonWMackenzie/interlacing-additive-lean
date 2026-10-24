import CurrentAdditive.GaussAdaptSerialize64

/-! One fixed Fin64 adaptation-and-serialization program. -/

namespace CurrentAdditive.GaussAdaptedPacket64

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Stack := Fin 64

def selectedCurrent (flag : Bool) (current : List Bool) : List Bool :=
  if flag then GaussAdaptPrepare64.zeroWord else current

def selectedColumn (flag : Bool) (column : List Bool) : List Bool :=
  if flag then GaussAdaptPrepare64.minusOneWord else column

def packet (flag : Bool) (current column row pivot : List Bool) : List Bool :=
  GaussOperandSerialize64.packet false
    (selectedCurrent flag current) (selectedColumn flag column) row pivot

def program := BitMachineRawSequence.program
  GaussAdaptPrepare64.program GaussOperandSerialize64.program
  (BitMachineBankSerialize.Label.emit 0)
  ((), none) (none : Option Bool)

abbrev Label := BitMachineRawSequence.Label
  GaussAdaptPrepare64.Label GaussOperandSerialize64.Label
abbrev Control := GaussAdaptPrepare64.Control × GaussOperandSerialize64.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def start : Label := BitMachineRawSequence.leftLabel .start
def initialControl : Control := (((), none), none)

theorem prepared_foreign (S : Stack → List Bool) (flag : Bool)
    (k : Stack) (h24 : k ≠ 24) (h25 : k ≠ 25) (h28 : k ≠ 28) :
    GaussAdaptPrepare64.prepared S flag k = S k := by
  cases flag <;> simp [GaussAdaptPrepare64.prepared,
    Function.update_of_ne, h24, h25, h28]

theorem prepared_words (S : Stack → List Bool) (flag : Bool)
    (current column row pivot : List Bool)
    (hflag : S 28 = [flag])
    (hcurrent : S 24 = current) (hcolumn : S 25 = column)
    (hrow : S 26 = row) (hpivot : S 27 = pivot)
    (hempty : ∀ j : Stack, j.val < 7 → S j = []) :
    ∀ i : Fin 12,
      (GaussAdaptPrepare64.prepared S flag)
        (GaussOperandSerialize64.fieldSlot i) =
      GaussOperandSerialize64.wordBank false
        (selectedCurrent flag current)
        (selectedColumn flag column) row pivot i := by
  let P := GaussAdaptPrepare64.prepared S flag
  have h24 : P 24 = selectedCurrent flag current := by
    cases flag <;> simp [P, selectedCurrent,
      GaussAdaptPrepare64.prepared, hcurrent]
  have h25 : P 25 = selectedColumn flag column := by
    cases flag <;> simp [P, selectedColumn,
      GaussAdaptPrepare64.prepared, hcolumn]
  have h28 : P 28 = [false] := by
    cases flag <;> simp [P, GaussAdaptPrepare64.prepared, hflag]
  have h26 : P 26 = row := by
    change GaussAdaptPrepare64.prepared S flag 26 = row
    rw [prepared_foreign S flag 26 (by decide) (by decide) (by decide)]
    exact hrow
  have h27 : P 27 = pivot := by
    change GaussAdaptPrepare64.prepared S flag 27 = pivot
    rw [prepared_foreign S flag 27 (by decide) (by decide) (by decide)]
    exact hpivot
  have hemptyP : ∀ j : Stack, j.val < 7 → P j = [] := by
    intro j hj
    have hne24 : j ≠ 24 := by intro he; have hv := congrArg Fin.val he; omega
    have hne25 : j ≠ 25 := by intro he; have hv := congrArg Fin.val he; omega
    have hne28 : j ≠ 28 := by intro he; have hv := congrArg Fin.val he; omega
    change GaussAdaptPrepare64.prepared S flag j = []
    rw [prepared_foreign S flag j hne24 hne25 hne28]
    exact hempty j hj
  exact GaussOperandSerialize64.prepared_words false
    (selectedCurrent flag current) (selectedColumn flag column) row pivot
    P h28 h24 h25 h26 h27 hemptyP

def timeBound (flag : Bool) (current column row pivot : List Bool) : ℕ :=
  GaussAdaptPrepare64.time flag current column +
    2 * (packet flag current column row pivot).length + 3

theorem run_full (S : Stack → List Bool) (flag : Bool)
    (current column row pivot : List Bool)
    (hflag : S 28 = [flag])
    (hcurrent : S 24 = current) (hcolumn : S 25 = column)
    (hrow : S 26 = row) (hpivot : S 27 = pivot)
    (hempty : ∀ j : Stack, j.val < 7 → S j = [])
    (h21 : S 21 = []) (h22 : S 22 = []) (h23 : S 23 = []) :
    ∃ t ≤ timeBound flag current column row pivot,
      ((advance program)^[t])
        (⟨some start, initialControl, S⟩ : Config) =
      ⟨none, initialControl,
        GaussAdaptSerialize64.finalBank
          (GaussAdaptPrepare64.prepared S flag)
          (packet flag current column row pivot) (fun _ => [])⟩ := by
  let P := GaussAdaptPrepare64.prepared S flag
  have hprep := GaussAdaptPrepare64.run S flag current column
    hflag hcurrent hcolumn
  have hwords := prepared_words S flag current column row pivot
    hflag hcurrent hcolumn hrow hpivot hempty
  have h21P : P 21 = [] := by
    change GaussAdaptPrepare64.prepared S flag 21 = []
    rw [prepared_foreign S flag 21 (by decide) (by decide) (by decide)]
    exact h21
  have h22P : P 22 = [] := by
    change GaussAdaptPrepare64.prepared S flag 22 = []
    rw [prepared_foreign S flag 22 (by decide) (by decide) (by decide)]
    exact h22
  have h23P : P 23 = [] := by
    change GaussAdaptPrepare64.prepared S flag 23 = []
    rw [prepared_foreign S flag 23 (by decide) (by decide) (by decide)]
    exact h23
  obtain ⟨u, hu, hser⟩ := GaussAdaptSerialize64.full_run false
    (selectedCurrent flag current) (selectedColumn flag column)
    row pivot P hwords h21P h22P h23P
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    GaussAdaptPrepare64.program GaussOperandSerialize64.program
    GaussAdaptPrepare64.Label.start (.emit 0)
    ((), none) ((), none) none none
    S P (GaussAdaptSerialize64.finalBank P
      (packet flag current column row pivot) (fun _ => []))
    (GaussAdaptPrepare64.time flag current column) u
    (by simpa only [P] using hprep)
    (by simpa only [P, packet] using hser)
  refine ⟨t, ?_, ?_⟩
  · unfold timeBound
    have hu' : u ≤ 2 * (packet flag current column row pivot).length + 2 := by
      simpa only [packet] using hu
    omega
  · simpa only [program, start, initialControl, P] using hfull

theorem output_at_23 (S : Stack → List Bool) (flag : Bool)
    (current column row pivot : List Bool)
    (U : BitMachineBankSerialize.Bank 12) :
    GaussAdaptSerialize64.finalBank
      (GaussAdaptPrepare64.prepared S flag)
      (packet flag current column row pivot) U 23 =
      packet flag current column row pivot :=
  GaussAdaptSerialize64.output_at_23 _ _ _

theorem matrix_at_8 (S : Stack → List Bool) (flag : Bool)
    (current column row pivot : List Bool)
    (U : BitMachineBankSerialize.Bank 12) :
    GaussAdaptSerialize64.finalBank
      (GaussAdaptPrepare64.prepared S flag)
      (packet flag current column row pivot) U 8 = S 8 := by
  have h8 : ¬ ∃ i, GaussOperandSerialize64.slot i = (8 : Stack) := by
    rintro ⟨i, hi⟩
    cases i with
    | inl i => fin_cases i <;> simp_all [GaussOperandSerialize64.slot,
        GaussOperandSerialize64.fieldSlot]
    | inr i => fin_cases i <;> simp_all [GaussOperandSerialize64.slot,
        GaussOperandSerialize64.extraSlot]
  rw [GaussAdaptSerialize64.foreign_at _ _ _ 8 h8]
  exact prepared_foreign S flag 8 (by decide) (by decide) (by decide)

theorem cleared_field (S : Stack → List Bool) (flag : Bool)
    (current column row pivot : List Bool) (i : Fin 12) :
    GaussAdaptSerialize64.finalBank
      (GaussAdaptPrepare64.prepared S flag)
      (packet flag current column row pivot) (fun _ => [])
      (GaussOperandSerialize64.fieldSlot i) = [] := by
  rw [GaussAdaptSerialize64.field_at]

theorem cleared_scratch (S : Stack → List Bool) (flag : Bool)
    (current column row pivot : List Bool) (i : Fin 3) (hi : i ≠ 2) :
    GaussAdaptSerialize64.finalBank
      (GaussAdaptPrepare64.prepared S flag)
      (packet flag current column row pivot) (fun _ => [])
      (GaussOperandSerialize64.extraSlot i) = [] :=
  GaussAdaptSerialize64.scratch_at _ _ _ i hi

theorem foreign_at (S : Stack → List Bool) (flag : Bool)
    (current column row pivot : List Bool) (k : Stack)
    (hslot : ¬ ∃ i, GaussOperandSerialize64.slot i = k)
    (h24 : k ≠ 24) (h25 : k ≠ 25) (h28 : k ≠ 28) :
    GaussAdaptSerialize64.finalBank
      (GaussAdaptPrepare64.prepared S flag)
      (packet flag current column row pivot) (fun _ => []) k = S k := by
  rw [GaussAdaptSerialize64.foreign_at _ _ _ k hslot]
  exact prepared_foreign S flag k h24 h25 h28

#print axioms run_full
#print axioms output_at_23
#print axioms matrix_at_8
#print axioms cleared_field
#print axioms cleared_scratch
#print axioms foreign_at

end CurrentAdditive.GaussAdaptedPacket64
