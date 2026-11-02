import CurrentAdditive.GaussPivotPrepRun

/-! A fixed polynomial cap for the physical Gauss-state preparation clock. -/

namespace CurrentAdditive.GaussPivotPrepClock

noncomputable section

open EthInapproximability.CurrentPaper
open scoped BigOperators

noncomputable abbrev M := GaussPivotCount32.M
variable {m k : Nat} (s : GaussControlTrace.State m k)

private def N := (GaussPivotPrepBank.packet s).length
private def C := GaussStateRowCount.polynomialClock (N s)
private def E := N s + C s * M.pushBound

theorem counted_slot_length_le (j : Fin M.stackCount) :
    ((GaussPivotPrepBank.counted s) (GaussPivotCount32.slot j)).length ≤
      E s := by
  rw [GaussPivotPrepBank.counted,
    show GaussPivotCount32.slot j = GaussPivotCount32.embed j from rfl,
    BitMachineStackEmbedding.bank_at]
  have h := BitMachine.run_length M
    (M.init (GaussPivotPrepBank.packet s)) j (C s)
  change ((GaussPivotPrepBank.countOut s).stk j).length ≤
    ((M.init (GaussPivotPrepBank.packet s)).stk j).length + C s * M.pushBound at h
  have hi : ((M.init (GaussPivotPrepBank.packet s)).stk j).length ≤ N s := by
    simp only [BitMachine.Machine.init]
    split <;> simp [N]
  exact h.trans (by dsimp [E]; omega)

theorem after_copy_slot (j : Fin M.stackCount) :
    GaussPivotCountExtract32.afterCopy (GaussPivotPrepBank.counted s)
      (GaussPivotCount32.slot j) =
      (GaussPivotPrepBank.counted s) (GaussPivotCount32.slot j) := by
  by_cases hj : j = M.output
  · subst j
    exact SourceClausePreservingBroadcast.source_restored
      GaussPivotCountExtract32.source 31 [13]
      GaussPivotCountExtract32.source_ne_temp
      ((GaussPivotPrepBank.counted s) GaussPivotCountExtract32.source)
      (GaussPivotPrepBank.counted s)
  · have hs : GaussPivotCount32.slot j ≠ GaussPivotCountExtract32.source := by
      intro he
      exact hj (GaussPivotCount32.slot_injective he)
    have h := SourceClausePreservingBroadcast.other_preserved
      GaussPivotCountExtract32.source 31 [13]
      ((GaussPivotPrepBank.counted s) GaussPivotCountExtract32.source)
      (GaussPivotPrepBank.counted s) (GaussPivotCount32.slot j)
      hs (GaussPivotCount32.slot_not_31 j)
      (by simpa using GaussPivotCount32.slot_not_13 j)
    simpa [GaussPivotCountExtract32.afterCopy,
      GaussPivotCountExtract32.temp] using h

theorem count_scratch_sum_le :
    (∑ j : Fin M.stackCount,
      ((GaussPivotCountExtract32.afterCopy (GaussPivotPrepBank.counted s))
        (GaussPivotCount32.slot j)).length) ≤ M.stackCount * E s := by
  calc
    _ = ∑ j : Fin M.stackCount,
        ((GaussPivotPrepBank.counted s) (GaussPivotCount32.slot j)).length := by
          apply Finset.sum_congr rfl
          intro j _
          rw [after_copy_slot s j]
    _ ≤ ∑ _j : Fin M.stackCount, E s := by
          apply Finset.sum_le_sum
          intro j _
          exact counted_slot_length_le s j
    _ = M.stackCount * E s := by simp

theorem extract_bound_le :
    GaussPivotPrepRun.extractBound s ≤
      (M.stackCount + 2) * (E s + 1) + 5 := by
  have hs := count_scratch_sum_le s
  have ho := counted_slot_length_le s M.output
  change (GaussPivotPrepBank.counted s
    GaussPivotCountExtract32.source).length ≤ E s at ho
  change 2 * (GaussPivotPrepBank.counted s
      GaussPivotCountExtract32.source).length + 3 +
      (∑ j : Fin M.stackCount,
        ((GaussPivotCountExtract32.afterCopy (GaussPivotPrepBank.counted s))
          (GaussPivotCount32.slot j)).length) + M.stackCount + 2 ≤
      (M.stackCount + 2) * (E s + 1) + 5
  nlinarith

theorem parsed_source_length_le (p : Fin 4) :
    ((GaussPivotPrepBank.parsed s).stk
      (GaussPivotFields32.source p)).length ≤ N s := by
  fin_cases p
  · change ((GaussPivotPrepBank.parsed s).stk 16).length ≤ N s
    rw [GaussPivotPrepBank.parsed_matrix]
    have h := BitMachineBankCodec.word_length_le_encode
      (GaussControlTrace.stateBank s) (0 : Fin 4)
    simpa [N, GaussPivotPrepBank.packet,
      GaussControlTrace.statePacket, GaussControlTrace.stateBank] using h
  · change ((GaussPivotPrepBank.parsed s).stk 18).length ≤ N s
    rw [GaussPivotPrepBank.parsed_column]
    have h := BitMachineBankCodec.word_length_le_encode
      (GaussControlTrace.stateBank s) (2 : Fin 4)
    simpa [N, GaussPivotPrepBank.packet,
      GaussControlTrace.statePacket, GaussControlTrace.stateBank] using h
  · change ((GaussPivotPrepBank.parsed s).stk 17).length ≤ N s
    rw [GaussPivotPrepBank.parsed_row]
    have h := BitMachineBankCodec.word_length_le_encode
      (GaussControlTrace.stateBank s) (1 : Fin 4)
    simpa [N, GaussPivotPrepBank.packet,
      GaussControlTrace.statePacket, GaussControlTrace.stateBank] using h
  · exact (congrArg List.length
      (GaussPivotPrepBank.parsed_original s)).le

theorem after3_clear_preserved (S : Fin 32 → List Bool) (i : Fin 5) :
    GaussPivotFields32.after3 S (GaussPivotFields32.clearBank i) =
      S (GaussPivotFields32.clearBank i) := by
  fin_cases i <;>
    simp [GaussPivotFields32.after3, GaussPivotFields32.after2,
      GaussPivotFields32.after1, GaussPivotFields32.after0,
      GaussPivotFields32.clearBank, GaussPivotFields32.source,
      GaussPivotFields32.dest, GaussPivotFields32.temp,
      SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend]

theorem parsed_clear_length_le (i : Fin 5) :
    ((GaussPivotPrepBank.parsed s).stk
      (GaussPivotFields32.clearBank i)).length ≤ N s := by
  fin_cases i
  · simpa [GaussPivotFields32.clearBank, GaussPivotFields32.source]
      using parsed_source_length_le s 0
  · simpa [GaussPivotFields32.clearBank, GaussPivotFields32.source]
      using parsed_source_length_le s 2
  · simpa [GaussPivotFields32.clearBank, GaussPivotFields32.source]
      using parsed_source_length_le s 1
  · have h := GaussPivotParser32.parsed_field s
      (GaussPivotPrepBank.extracted s) (3 : Fin 4)
    have hb := BitMachineBankCodec.word_length_le_encode
      (GaussControlTrace.stateBank s) (3 : Fin 4)
    rw [← h] at hb
    simpa [GaussPivotPrepBank.parsed, N,
      GaussPivotPrepBank.packet, GaussControlTrace.statePacket] using hb
  · exact (congrArg List.length
      (GaussPivotPrepBank.parsed_original s)).le

theorem field_scratch_sum_le :
    (∑ i : Fin 5,
      ((GaussPivotFields32.after3 (GaussPivotPrepBank.parsed s).stk)
        (GaussPivotFields32.clearBank i)).length) ≤ 5 * N s := by
  calc
    _ = ∑ i : Fin 5,
      ((GaussPivotPrepBank.parsed s).stk
        (GaussPivotFields32.clearBank i)).length := by
        apply Finset.sum_congr rfl
        intro i _
        rw [after3_clear_preserved]
    _ ≤ ∑ _i : Fin 5, N s := by
        apply Finset.sum_le_sum
        intro i _
        exact parsed_clear_length_le s i
    _ = 5 * N s := by simp

theorem fields_bound_le : GaussPivotPrepRun.fieldsBound s ≤ 13 * N s + 19 := by
  have h0 := parsed_source_length_le s 0
  have h1 := parsed_source_length_le s 1
  have h2 := parsed_source_length_le s 2
  have h3 := parsed_source_length_le s 3
  have hs := field_scratch_sum_le s
  unfold GaussPivotPrepRun.fieldsBound GaussPivotFields32.copyClock
  omega

def polynomialClock (n : Nat) : Nat :=
  (M.stackCount + 50) *
    (n + GaussStateRowCount.polynomialClock n * (M.pushBound + 1) + 1)

theorem clock_le_polynomial :
    GaussPivotPrepRun.clock s ≤ polynomialClock (N s) := by
  have he := extract_bound_le s
  have hf := fields_bound_le s
  let n := N s
  let c := C s
  let d := M.stackCount
  let p := M.pushBound
  let e := E s
  let f := n + c * (p + 1)
  have heq : e = n + c * p := rfl
  have hfe : f = e + c := by
    dsimp [f, e, E, c, C, n, N, p]
    rw [Nat.mul_add]
    omega
  have hraw : GaussPivotPrepRun.clock s ≤
      (d + 2) * (e + 1) + 24 * n + c + 42 := by
    change GaussPivotPrepRun.extractBound s ≤ (d + 2) * (e + 1) + 5 at he
    change GaussPivotPrepRun.fieldsBound s ≤ 13 * n + 19 at hf
    unfold GaussPivotPrepRun.clock GaussPivotPrepRun.copyBound
      GaussPivotPrepRun.countBound GaussPivotPrepRun.parserBound
    change 2 * n + 3 + 1 + (c + 1) + 1 +
      GaussPivotPrepRun.extractBound s + 1 +
      (9 * (n + 1) + 1) + 1 + GaussPivotPrepRun.fieldsBound s ≤
      (d + 2) * (e + 1) + 24 * n + c + 42
    omega
  have hmul : (d + 2) * (e + 1) ≤ (d + 2) * (f + 1) := by
    apply Nat.mul_le_mul_left
    omega
  have htail : 24 * n + c + 42 ≤ 48 * (f + 1) := by
    rw [hfe]
    have hn : n ≤ e := by dsimp [e, E]; omega
    omega
  unfold polynomialClock
  change GaussPivotPrepRun.clock s ≤ (d + 50) * (f + 1)
  calc
    _ ≤ (d + 2) * (e + 1) + 24 * n + c + 42 := hraw
    _ ≤ (d + 2) * (f + 1) + 48 * (f + 1) := by omega
    _ = (d + 50) * (f + 1) := by ring

theorem outputs_polynomial :
    ∃ t ≤ polynomialClock (N s),
      (GaussPivotPrepController32.run t
        (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s))).l =
          some .done ∧
      ∀ j : Fin 32,
        (GaussPivotPrepController32.run t
          (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s))).stk j =
          if j = 8 then GaussPhysical.encodeTypedMatrix s.B
          else if j = 12 then List.replicate s.c true
          else if j = 13 then List.replicate m true
          else if j = 30 then List.replicate s.r true
          else if j = 31 then GaussPivotPrepBank.packet s
          else [] := by
  obtain ⟨t, ht, hl, hb⟩ := GaussPivotPrepRun.outputs_exact s
  exact ⟨t, ht.trans (clock_le_polynomial s), hl, hb⟩

#print axioms count_scratch_sum_le
#print axioms field_scratch_sum_le
#print axioms clock_le_polynomial
#print axioms outputs_polynomial

end
end CurrentAdditive.GaussPivotPrepClock
