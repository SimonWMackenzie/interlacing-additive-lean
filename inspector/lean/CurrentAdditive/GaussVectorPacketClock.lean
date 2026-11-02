import CurrentAdditive.GaussDirectVectorABI
import CurrentAdditive.GaussMatrixClock

/-! Size accounting for the canonical postloop vector word. The bound is
polynomial in the number of columns and a uniform bound on the bit lengths
of its rational entries. -/

namespace CurrentAdditive.GaussVectorPacketClock

open CurrentAdditive.GaussCertificateVectorABI
open CurrentAdditive.GaussFirstFreeCandidate
open EthInapproximability.CurrentPaper

theorem vectorPacket_length (x : Array ℚ) (S : Nat)
    (hbits : ∀ q ∈ x.toList,
      Nat.size q.num.natAbs ≤ S ∧ Nat.size q.den ≤ S) :
    (vectorPacket x).length ≤ 3 * x.size * (4 * S + 6) + 1 := by
  have hentry : ∀ q ∈ x.toList,
      (coefficientPacket q).length ≤ 4 * S + 5 := by
    intro q hq
    exact CurrentAdditive.GaussPhysical.rawOfRat_code_length q S
      (hbits q hq).1 (hbits q hq).2
  have h := SourceListEncoding.encode_map_length_le x.toList
    coefficientPacket (4 * S + 5) hentry
  simpa [vectorPacket, CurrentAdditive.CodeDCodecV2.encodeItems] using h

theorem directCandidate_bits {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k) (hf : f.val ≤ m)
    (S : Nat) (hS : 1 ≤ S)
    (hbits : ∀ i j,
      Nat.size (B i j).num.natAbs ≤ S ∧
      Nat.size (B i j).den ≤ S)
    (j : Fin k) :
    Nat.size (directCandidate B f hf j).num.natAbs ≤ S ∧
      Nat.size (directCandidate B f hf j).den ≤ S := by
  by_cases hj : j.val < f.val
  · have h := hbits (⟨j.val, by omega⟩ : Fin m) f
    simpa [directCandidate, hj, Rat.num_neg_eq_neg_num,
      Rat.den_neg_eq_den, Int.natAbs_neg] using h
  · by_cases heq : j = f
    · simp [directCandidate, heq]
      omega
    · simp [directCandidate, hj, heq]
      omega

theorem directVector_length {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k) (hf : f.val ≤ m)
    (S : Nat) (hS : 1 ≤ S)
    (hbits : ∀ i j,
      Nat.size (B i j).num.natAbs ≤ S ∧
      Nat.size (B i j).den ≤ S) :
    (vectorPacket (Array.ofFn (directCandidate B f hf))).length ≤
      3 * k * (4 * S + 6) + 1 := by
  have h := vectorPacket_length
    (Array.ofFn (directCandidate B f hf)) S (by
      intro q hq
      rw [Array.toList_ofFn] at hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      exact directCandidate_bits B f hf S hS hbits j)
  simpa using h

theorem actual_directVector_length {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (f : Fin k) (hf : f.val ≤ m) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (CurrentAdditive.MaterializedGauss.echelonMaterialized Aq 0 0 k).1
    (vectorPacket (Array.ofFn (directCandidate B f hf))).length ≤
      3 * k * (4 * ((m + 3) * (m + 1) ^ 2 + 1) + 6) + 1 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let B := (CurrentAdditive.MaterializedGauss.echelonMaterialized Aq 0 0 k).1
  have hbits : ∀ i j,
      Nat.size (B i j).num.natAbs ≤ (m + 3) * (m + 1) ^ 2 + 1 ∧
      Nat.size (B i j).den ≤ (m + 3) * (m + 1) ^ 2 + 1 := by
    intro i j
    have h := CurrentAdditive.EliminationEntryBounds.every_actual_step_entry_bits
      A h01 k (by omega) i j
    have hB : B =
        (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq k).B := by
      exact (CurrentAdditive.EliminationEntryBounds.cursorAfter_eq_prefix Aq k).symm
    simpa [Aq, hB] using ⟨h.2, h.1⟩
  exact directVector_length B f hf _ (by omega) hbits

#print axioms vectorPacket_length
#print axioms directCandidate_bits
#print axioms actual_directVector_length

end CurrentAdditive.GaussVectorPacketClock
