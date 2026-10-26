import CurrentAdditive.GaussPivotInputCopy32
import CurrentAdditive.GaussPivotCountExtract32
import CurrentAdditive.GaussPivotFields32

/-! The bank invariant between the charged physical stages. No row count or
field is preloaded: the sole initial nonempty bank is the encoded state. -/

namespace CurrentAdditive.GaussPivotPrepBank

open EthInapproximability.CurrentPaper

abbrev Stack := Fin 32
noncomputable abbrev M := GaussPivotCount32.M

variable {m k : Nat} (s : GaussControlTrace.State m k)

def packet : List Bool := GaussControlTrace.statePacket s

noncomputable def copied : Stack → List Bool :=
  GaussPivotInputCopy32.result (packet s)

noncomputable def countOut : M.Config :=
  M.run (GaussStateRowCount.polynomialClock (packet s).length)
    (M.init (packet s))

noncomputable def counted : Stack → List Bool :=
  BitMachineStackEmbedding.bank GaussPivotCount32.embed (copied s)
    (countOut s).stk

noncomputable def extracted : Stack → List Bool :=
  BitMachineClearBank.cleared GaussPivotCount32.slot
    (GaussPivotCountExtract32.afterCopy (counted s))

noncomputable def parsed : GaussPivotParser32.Config :=
  GaussPivotParser32.frame (extracted s)
    (BitMachineBankCodec.parserCfg none (some true)
      (GaussControlTrace.stateBank s) [] [] [])

noncomputable def prepared : Stack → List Bool :=
  BitMachineClearBank.cleared GaussPivotFields32.clearBank
    (GaussPivotFields32.after3 (parsed s).stk)

theorem copied_13_empty : copied s 13 = [] := by
  have h := SourceClausePreservingBroadcast.other_preserved
    30 31 [28, GaussPivotInputCopy32.target] (packet s)
    (GaussPivotInputCopy32.startBank (packet s)) 13
    (by decide) (by decide)
    (by simp [show (13 : Stack) ≠ GaussPivotInputCopy32.target from
      (GaussPivotCount32.slot_not_13 _).symm])
  simpa [copied, GaussPivotInputCopy32.result,
    GaussPivotInputCopy32.startBank] using h

theorem counted_13_empty : counted s 13 = [] := by
  rw [counted, countOut, packet,
    GaussPivotCount32.ambient_preserved s (copied s) 13 (Or.inl rfl)]
  exact copied_13_empty s

theorem counted_31_empty : counted s 31 = [] := by
  rw [counted, countOut, packet,
    GaussPivotCount32.ambient_preserved s (copied s) 31
    (Or.inr (Or.inr (Or.inr rfl)))]
  exact GaussPivotInputCopy32.temp_empty (packet s)

theorem counted_output :
    counted s (GaussPivotCountExtract32.source) = List.replicate m true := by
  exact GaussPivotCount32.count_output s (copied s)

theorem extracted_13 : extracted s 13 = List.replicate m true := by
  rw [extracted, GaussPivotCountExtract32.final_count
    (counted s) (counted_13_empty s)]
  exact counted_output s

theorem extracted_28 : extracted s 28 = packet s := by
  rw [extracted, GaussPivotCountExtract32.final_ambient (counted s) 28 (Or.inl rfl)]
  rw [counted, countOut, packet,
    GaussPivotCount32.ambient_preserved s (copied s) 28
    (Or.inr (Or.inl rfl))]
  exact GaussPivotInputCopy32.saved_source (packet s)

theorem extracted_30 : extracted s 30 = packet s := by
  rw [extracted, GaussPivotCountExtract32.final_ambient (counted s) 30
    (Or.inr rfl)]
  rw [counted, countOut, packet,
    GaussPivotCount32.ambient_preserved s (copied s) 30
    (Or.inr (Or.inr (Or.inl rfl)))]
  exact GaussPivotInputCopy32.source_preserved (packet s)

theorem extracted_31 : extracted s 31 = [] := by
  have h := BitMachineClearBank.cleared_foreign
    GaussPivotCount32.slot (GaussPivotCountExtract32.afterCopy (counted s)) 31
    (fun j => GaussPivotCount32.slot_not_31 j)
  rw [extracted, h]
  exact SourceClausePreservingBroadcast.temp_empty _ _ _ _ _

theorem extracted_other (j : Stack)
    (hj : j ≠ 13 ∧ j ≠ 28 ∧ j ≠ 30 ∧ j ≠ 31) :
    extracted s j = [] := by
  by_cases hslot : ∃ q : Fin M.stackCount, GaussPivotCount32.slot q = j
  · simp [extracted, BitMachineClearBank.cleared, hslot]
  · have hclear := BitMachineClearBank.cleared_foreign
      GaussPivotCount32.slot (GaussPivotCountExtract32.afterCopy (counted s)) j
      (fun q h => hslot ⟨q, h⟩)
    rw [extracted, hclear]
    have hsource : GaussPivotCountExtract32.source ≠ j := by
      intro h; exact hslot ⟨M.output, h⟩
    have hcopy := SourceClausePreservingBroadcast.other_preserved
      GaussPivotCountExtract32.source 31 [13]
      ((counted s) GaussPivotCountExtract32.source) (counted s) j
      hsource.symm hj.2.2.2 (by simp [hj.1])
    have hcopy' : GaussPivotCountExtract32.afterCopy (counted s) j =
        counted s j := by
      simpa [GaussPivotCountExtract32.afterCopy,
        GaussPivotCountExtract32.temp] using hcopy
    rw [hcopy']
    have hbank := BitMachineStackEmbedding.bank_outside
      GaussPivotCount32.embed (copied s) (countOut s).stk j hslot
    rw [counted, hbank]
    have htarget : j ≠ GaussPivotInputCopy32.target := by
      intro h
      exact hslot ⟨M.input, h.symm⟩
    have hraw := SourceClausePreservingBroadcast.other_preserved
      30 31 [28, GaussPivotInputCopy32.target] (packet s)
      (GaussPivotInputCopy32.startBank (packet s)) j
      hj.2.2.1 hj.2.2.2
      (by simp [hj.2.1, htarget])
    rw [copied, GaussPivotInputCopy32.result, hraw]
    simp [GaussPivotInputCopy32.startBank, hj.2.2.1]

theorem parsed_matrix : (parsed s).stk 16 =
    GaussPhysical.encodeTypedMatrix s.B := by
  have h := GaussPivotParser32.parsed_field s (extracted s) (0 : Fin 4)
  simpa [parsed, GaussControlTrace.stateBank] using h

theorem parsed_row : (parsed s).stk 17 = List.replicate s.r true := by
  have h := GaussPivotParser32.parsed_field s (extracted s) (1 : Fin 4)
  simpa [parsed, GaussControlTrace.stateBank] using h

theorem parsed_column : (parsed s).stk 18 = List.replicate s.c true := by
  have h := GaussPivotParser32.parsed_field s (extracted s) (2 : Fin 4)
  simpa [parsed, GaussControlTrace.stateBank] using h

theorem parsed_original : (parsed s).stk 28 = packet s := by
  rw [parsed, GaussPivotParser32.parsed_ambient s (extracted s) 28
    (by decide)]
  exact extracted_28 s

theorem parsed_count : (parsed s).stk 13 = List.replicate m true := by
  rw [parsed, GaussPivotParser32.parsed_ambient s (extracted s) 13
    (by decide)]
  exact extracted_13 s

theorem parsed_empty_8 : (parsed s).stk 8 = [] := by
  rw [parsed, GaussPivotParser32.parsed_ambient s (extracted s) 8
    (by decide)]
  exact extracted_other s 8 (by decide)

theorem parsed_empty_12 : (parsed s).stk 12 = [] := by
  rw [parsed, GaussPivotParser32.parsed_ambient s (extracted s) 12
    (by decide)]
  exact extracted_other s 12 (by decide)

theorem parsed_empty_30 : (parsed s).stk 30 = [] := by
  change BitMachineStackEmbedding.bank GaussPivotParser32.locate (extracted s)
    (BitMachineBankCodec.parserCfg none (some true)
      (GaussControlTrace.stateBank s) [] [] []).stk
    (GaussPivotParser32.locate (.inr 0)) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem parsed_empty_31 : (parsed s).stk 31 = [] := by
  change BitMachineStackEmbedding.bank GaussPivotParser32.locate (extracted s)
    (BitMachineBankCodec.parserCfg none (some true)
      (GaussControlTrace.stateBank s) [] [] []).stk
    (GaussPivotParser32.locate (.inr 1)) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem parsed_dest_empty (p : Fin 4) :
    (parsed s).stk (GaussPivotFields32.dest p) = [] := by
  fin_cases p
  · exact parsed_empty_8 s
  · exact parsed_empty_12 s
  · exact parsed_empty_30 s
  · exact parsed_empty_31 s

theorem prepared_matrix : prepared s 8 =
    GaussPhysical.encodeTypedMatrix s.B := by
  have h := GaussPivotFields32.final_field (parsed s).stk 0
    (parsed_dest_empty s)
  simpa [prepared, GaussPivotFields32.source, GaussPivotFields32.dest]
    using h.trans (parsed_matrix s)

theorem prepared_column : prepared s 12 = List.replicate s.c true := by
  have h := GaussPivotFields32.final_field (parsed s).stk 1
    (parsed_dest_empty s)
  simpa [prepared, GaussPivotFields32.source, GaussPivotFields32.dest]
    using h.trans (parsed_column s)

theorem prepared_row : prepared s 30 = List.replicate s.r true := by
  have h := GaussPivotFields32.final_field (parsed s).stk 2
    (parsed_dest_empty s)
  simpa [prepared, GaussPivotFields32.source, GaussPivotFields32.dest]
    using h.trans (parsed_row s)

theorem prepared_original : prepared s 31 = packet s := by
  have h := GaussPivotFields32.final_field (parsed s).stk 3
    (parsed_dest_empty s)
  simpa [prepared, GaussPivotFields32.source, GaussPivotFields32.dest]
    using h.trans (parsed_original s)

theorem prepared_count : prepared s 13 = List.replicate m true := by
  have hclear := BitMachineClearBank.cleared_foreign
    GaussPivotFields32.clearBank (GaussPivotFields32.after3 (parsed s).stk) 13
    (by intro i; fin_cases i <;> decide)
  rw [prepared, hclear]
  have h0 := SourceClausePreservingBroadcast.other_preserved
    (GaussPivotFields32.source 0) GaussPivotFields32.temp
    [GaussPivotFields32.dest 0] ((parsed s).stk (GaussPivotFields32.source 0))
    (parsed s).stk 13 (by decide) (by decide) (by decide)
  have h1 := SourceClausePreservingBroadcast.other_preserved
    (GaussPivotFields32.source 1) GaussPivotFields32.temp
    [GaussPivotFields32.dest 1] ((parsed s).stk (GaussPivotFields32.source 1))
    (GaussPivotFields32.after0 (parsed s).stk) 13
    (by decide) (by decide) (by decide)
  have h2 := SourceClausePreservingBroadcast.other_preserved
    (GaussPivotFields32.source 2) GaussPivotFields32.temp
    [GaussPivotFields32.dest 2] ((parsed s).stk (GaussPivotFields32.source 2))
    (GaussPivotFields32.after1 (parsed s).stk) 13
    (by decide) (by decide) (by decide)
  have h3 := SourceClausePreservingBroadcast.other_preserved
    (GaussPivotFields32.source 3) GaussPivotFields32.temp
    [GaussPivotFields32.dest 3] ((parsed s).stk (GaussPivotFields32.source 3))
    (GaussPivotFields32.after2 (parsed s).stk) 13
    (by decide) (by decide) (by decide)
  rw [GaussPivotFields32.after3, h3,
    GaussPivotFields32.after2, h2,
    GaussPivotFields32.after1, h1,
    GaussPivotFields32.after0, h0]
  exact parsed_count s

def sourceClear : Fin 4 → Fin 5 := ![0, 2, 1, 4]

theorem source_clear (p : Fin 4) :
    GaussPivotFields32.clearBank (sourceClear p) =
      GaussPivotFields32.source p := by
  fin_cases p <;> rfl

theorem after3_other (S : Stack → List Bool) (j : Stack)
    (hclear : ∀ i : Fin 5, GaussPivotFields32.clearBank i ≠ j)
    (hdest : ∀ p : Fin 4, GaussPivotFields32.dest p ≠ j)
    (htemp : j ≠ 29) :
    GaussPivotFields32.after3 S j = S j := by
  have hs : ∀ p : Fin 4, j ≠ GaussPivotFields32.source p := by
    intro p he
    exact hclear (sourceClear p) ((source_clear p).trans he.symm)
  have ht : j ≠ GaussPivotFields32.temp := by
    simpa [GaussPivotFields32.temp] using htemp
  have h0 := SourceClausePreservingBroadcast.other_preserved
    (GaussPivotFields32.source 0) GaussPivotFields32.temp
    [GaussPivotFields32.dest 0] (S (GaussPivotFields32.source 0))
    S j (hs 0) ht (by simpa only [List.mem_singleton] using (hdest 0).symm)
  have h1 := SourceClausePreservingBroadcast.other_preserved
    (GaussPivotFields32.source 1) GaussPivotFields32.temp
    [GaussPivotFields32.dest 1] (S (GaussPivotFields32.source 1))
    (GaussPivotFields32.after0 S) j (hs 1) ht
      (by simpa only [List.mem_singleton] using (hdest 1).symm)
  have h2 := SourceClausePreservingBroadcast.other_preserved
    (GaussPivotFields32.source 2) GaussPivotFields32.temp
    [GaussPivotFields32.dest 2] (S (GaussPivotFields32.source 2))
    (GaussPivotFields32.after1 S) j (hs 2) ht
      (by simpa only [List.mem_singleton] using (hdest 2).symm)
  have h3 := SourceClausePreservingBroadcast.other_preserved
    (GaussPivotFields32.source 3) GaussPivotFields32.temp
    [GaussPivotFields32.dest 3] (S (GaussPivotFields32.source 3))
    (GaussPivotFields32.after2 S) j (hs 3) ht
      (by simpa only [List.mem_singleton] using (hdest 3).symm)
  rw [GaussPivotFields32.after3, h3,
    GaussPivotFields32.after2, h2,
    GaussPivotFields32.after1, h1,
    GaussPivotFields32.after0, h0]

theorem prepared_other (j : Stack)
    (hj : j ≠ 8 ∧ j ≠ 12 ∧ j ≠ 13 ∧ j ≠ 30 ∧ j ≠ 31) :
    prepared s j = [] := by
  by_cases hclear : ∃ i : Fin 5, GaussPivotFields32.clearBank i = j
  · simp [prepared, BitMachineClearBank.cleared, hclear]
  · have hc : ∀ i : Fin 5, GaussPivotFields32.clearBank i ≠ j :=
      fun i he => hclear ⟨i, he⟩
    have hf := BitMachineClearBank.cleared_foreign
      GaussPivotFields32.clearBank
      (GaussPivotFields32.after3 (parsed s).stk) j hc
    rw [prepared, hf]
    by_cases hj29 : j = 29
    · subst j
      exact SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
    · have hd : ∀ p : Fin 4, GaussPivotFields32.dest p ≠ j := by
        intro p
        fin_cases p
        · exact (hj.1).symm
        · exact (hj.2.1).symm
        · exact (hj.2.2.2.1).symm
        · exact (hj.2.2.2.2).symm
      rw [after3_other (parsed s).stk j hc hd hj29]
      have hp : j ≠ 16 ∧ j ≠ 17 ∧ j ≠ 18 ∧ j ≠ 19 ∧
          j ≠ 29 ∧ j ≠ 30 ∧ j ≠ 31 := by
        constructor
        · exact (hc 0).symm
        constructor
        · exact (hc 1).symm
        constructor
        · exact (hc 2).symm
        constructor
        · exact (hc 3).symm
        exact ⟨hj29, hj.2.2.2.1, hj.2.2.2.2⟩
      rw [parsed, GaussPivotParser32.parsed_ambient s (extracted s) j hp]
      exact extracted_other s j
        ⟨hj.2.2.1, (hc 4).symm, hj.2.2.2.1, hj.2.2.2.2⟩

theorem prepared_exact (j : Stack) : prepared s j =
    if j = 8 then GaussPhysical.encodeTypedMatrix s.B
    else if j = 12 then List.replicate s.c true
    else if j = 13 then List.replicate m true
    else if j = 30 then List.replicate s.r true
    else if j = 31 then packet s
    else [] := by
  by_cases h8 : j = 8
  · subst j; simp [prepared_matrix s]
  by_cases h12 : j = 12
  · subst j; simp [prepared_column s]
  by_cases h13 : j = 13
  · subst j; simp [prepared_count s]
  by_cases h30 : j = 30
  · subst j; simp [prepared_row s]
  by_cases h31 : j = 31
  · subst j; simp [prepared_original s]
  simp [h8, h12, h13, h30, h31,
    prepared_other s j ⟨h8, h12, h13, h30, h31⟩]

#print axioms extracted_13
#print axioms extracted_28
#print axioms extracted_30
#print axioms extracted_31
#print axioms extracted_other
#print axioms prepared_matrix
#print axioms prepared_column
#print axioms prepared_count
#print axioms prepared_row
#print axioms prepared_original
#print axioms prepared_exact

end CurrentAdditive.GaussPivotPrepBank
