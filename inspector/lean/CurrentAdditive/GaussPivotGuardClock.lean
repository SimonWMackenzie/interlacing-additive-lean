import CurrentAdditive.GaussPivotGuardPacket

/-! A fixed input-length polynomial cap for the prepared-state guard. -/

namespace CurrentAdditive.GaussPivotGuardClock

open EthInapproximability.CurrentPaper

noncomputable section

noncomputable abbrev M := GaussPivotCount32.M

def polynomialClock (N : Nat) : Nat :=
  12 * (N + GaussStateRowCount.polynomialClock N * M.pushBound + 1)

variable {m k : Nat} (s : GaussControlTrace.State m k)

theorem row_le_packet :
    s.r ≤ (GaussPivotPrepBank.packet s).length := by
  rw [GaussPivotPrepBank.packet, GaussControlTrace.statePacket_length]
  omega

theorem count_le_packet_envelope :
    m ≤ (GaussPivotPrepBank.packet s).length +
      GaussStateRowCount.polynomialClock
        (GaussPivotPrepBank.packet s).length * M.pushBound := by
  have h := GaussPivotPrepClock.counted_slot_length_le s M.output
  change (GaussPivotPrepBank.counted s
    GaussPivotCountExtract32.source).length ≤ _ at h
  rw [GaussPivotPrepBank.counted_output s] at h
  simp only [List.length_replicate] at h
  change m ≤ (GaussPivotPrepBank.packet s).length +
    GaussStateRowCount.polynomialClock
      (GaussPivotPrepBank.packet s).length * M.pushBound at h
  exact h

theorem clock_le_polynomial :
    GaussPivotGuardRun.clock s.r m ≤
      polynomialClock (GaussPivotPrepBank.packet s).length := by
  have hr := row_le_packet s
  have hm := count_le_packet_envelope s
  have hmax : max s.r m ≤
      (GaussPivotPrepBank.packet s).length +
        GaussStateRowCount.polynomialClock
          (GaussPivotPrepBank.packet s).length * M.pushBound :=
    max_le (by omega) hm
  unfold GaussPivotGuardRun.clock polynomialClock
  omega

theorem prepared_guard_polynomial :
    ∃ t ≤ polynomialClock (GaussPivotPrepBank.packet s).length,
      GaussPivotGuard32.run t
        (GaussPivotGuard32.initial (GaussPivotPrepBank.prepared s)) =
        ⟨some (if s.r < m then .active else .terminal),
          .choose (some (decide (s.r < m))),
          GaussPivotPrepBank.prepared s⟩ := by
  obtain ⟨t, ht, he⟩ := GaussPivotGuardPacket.prepared_guard s
  exact ⟨t, ht.trans (clock_le_polynomial s), he⟩

#print axioms prepared_guard_polynomial

end
end CurrentAdditive.GaussPivotGuardClock
