import CurrentAdditive.CompactRationalPacket

/-! The concrete coordinate-evaluation seed's indexed row and column
carriers have short binary labels under the compact codec. -/

namespace Paper2.CompactSeedLabelSize

open Paper2.CompactFinCodec

def p (L : ℕ) : ℕ := Paper2.LookupSeed.width L

theorem row_index_length (L : ℕ) (i : Fin (2 ^ p L)) :
    ((codec (2 ^ p L)).encode i).length ≤ 2 * p L + 1 := by
  exact encoded_length_le_log (le_refl (2 ^ p L)) i

theorem column_index_length (L : ℕ) (j : Fin (p L)) :
    ((codec (p L)).encode j).length ≤ 2 * p L + 1 := by
  exact encoded_length_le_log (Nat.le_of_lt (p L).lt_two_pow_self) j

theorem row_index_linear_length (L : ℕ) (i : Fin (2 ^ p L)) :
    ((codec (2 ^ p L)).encode i).length ≤ 256 * (L + 1) + 1 := by
  have hp : p L < 128 * (L + 1) := Paper2.LookupSeed.width_lt L
  have hi := row_index_length L i
  omega

theorem column_index_linear_length (L : ℕ) (j : Fin (p L)) :
    ((codec (p L)).encode j).length ≤ 256 * (L + 1) + 1 := by
  have hp : p L < 128 * (L + 1) := Paper2.LookupSeed.width_lt L
  have hi := column_index_length L j
  omega

#print axioms row_index_linear_length
#print axioms column_index_linear_length

end Paper2.CompactSeedLabelSize
