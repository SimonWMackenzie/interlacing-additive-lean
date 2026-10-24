import CurrentAdditive.GaussContextSpec

namespace CurrentAdditive.GaussListContext

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussPhysical
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec

theorem packet_length_le (x : CellContext) (L : Nat)
    (hcurrent : (encodeRawRat x.current).length ≤ L)
    (hcolumn : (encodeRawRat x.column).length ≤ L)
    (hrow : (encodeRawRat x.row).length ≤ L)
    (hpivot : (encodeRawRat x.pivot).length ≤ L) :
    (packet x).length ≤ 2 * (12 * (1 + 4 * L)) + 12 := by
  have hfield : ∀ j : Fin 12,
      (cellBank x.pivotRow x.current x.column x.row x.pivot j).length ≤
        1 + 4 * L := by
    intro j
    fin_cases j <;> simp [cellBank] <;> omega
  have hsum : (∑ j : Fin 12,
      (cellBank x.pivotRow x.current x.column x.row x.pivot j).length) ≤
        12 * (1 + 4 * L) := by
    calc
      _ ≤ ∑ _j : Fin 12, (1 + 4 * L) := by
        apply Finset.sum_le_sum
        intro j _
        exact hfield j
      _ = _ := by simp
  rw [packet, cellPacket, encode_length]
  omega

theorem encodedTypedContexts_length_le {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k) (L : Nat)
    (hraw : ∀ i : Fin m, ∀ j : Fin k,
      (encodeRawRat (rawOfRat (B i j))).length ≤ L) :
    (encodedTypedContexts B r c).length ≤
      3 * (m * k) * (2 * (12 * (1 + 4 * L)) + 13) + 1 := by
  have hpacket : ∀ x ∈ typedContexts B r c,
      (packet x).length ≤ 2 * (12 * (1 + 4 * L)) + 12 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := (typedContexts_mem B r c x).mp hx
    exact packet_length_le _ L (hraw i j) (hraw i c)
      (hraw r j) (hraw r c)
  have h := SourceListEncoding.encode_map_length_le
    (typedContexts B r c) packet
    (2 * (12 * (1 + 4 * L)) + 12) hpacket
  simpa only [encodedTypedContexts, typedContexts_length] using h

#print axioms packet_length_le
#print axioms encodedTypedContexts_length_le

end CurrentAdditive.GaussListContext
