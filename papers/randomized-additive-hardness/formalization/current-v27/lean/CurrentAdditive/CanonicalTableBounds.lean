import CurrentAdditive.CanonicalPrintedTable
import CurrentAdditive.SmallBiasPublicDegree

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias

def degreeSlope (t : ℕ) : ℕ := 4 * 2 ^ t + 2
def degreeOffset (t : ℕ) : ℕ := 12 * 2 ^ t * t + 5 * t + 2
def tableExponent (t : ℕ) : ℕ :=
  2 ^ (t - 1) + 1 + 2 * degreeSlope t
def tableConstant (t : ℕ) : ℕ :=
  2 ^ (t - 1) * 2 ^ (2 * degreeOffset t)

/-- A coarse but explicit fixed-`t` polynomial bound on all emitted matrix
entries, with the public field degree computed from `b,t`. -/
theorem table_entry_count_polynomial (v b t : ℕ) (ht : 4 ≤ t) :
    rowCount v b t * columnCount b t (publicFieldDegree b t) ≤
      tableConstant t * v * (2 ^ b) ^ tableExponent t := by
  have hd := public_degree_cost_bound b t ht
  have hd' : publicFieldDegree b t ≤ b * degreeSlope t + degreeOffset t := by
    dsimp [degreeSlope, degreeOffset]
    omega
  have hpow :
      2 ^ publicFieldDegree b t ≤
        2 ^ degreeOffset t * (2 ^ b) ^ degreeSlope t := by
    calc
      2 ^ publicFieldDegree b t ≤
          2 ^ (b * degreeSlope t + degreeOffset t) :=
        Nat.pow_le_pow_right (by omega) hd'
      _ = 2 ^ degreeOffset t * (2 ^ b) ^ degreeSlope t := by
        rw [pow_add, pow_mul]
        ring
  have hsq :
      (2 ^ publicFieldDegree b t) ^ 2 ≤
        (2 ^ degreeOffset t * (2 ^ b) ^ degreeSlope t) ^ 2 :=
    Nat.pow_le_pow_left hpow 2
  unfold rowCount columnCount tableConstant tableExponent
  calc
    v * (2 ^ b) ^ (2 ^ (t - 1)) *
        (2 ^ (t - 1) * 2 ^ b * (2 ^ publicFieldDegree b t) ^ 2) ≤
      v * (2 ^ b) ^ (2 ^ (t - 1)) *
        (2 ^ (t - 1) * 2 ^ b *
          (2 ^ degreeOffset t * (2 ^ b) ^ degreeSlope t) ^ 2) := by
      gcongr
    _ = 2 ^ (t - 1) * 2 ^ (2 * degreeOffset t) * v *
        (2 ^ b) ^ (2 ^ (t - 1) + 1 + 2 * degreeSlope t) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, pow_add, pow_add]
      ring

theorem table_bits_polynomial {v e : ℕ} (b t : ℕ) (ht : 4 ≤ t)
    (modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    (table b t (publicFieldDegree b t) modulus he edges).bits.length ≤
      tableConstant t * v * (2 ^ b) ^ tableExponent t := by
  simpa only [table, Paper2.YaoMaterialization.tabulate_length] using
    table_entry_count_polynomial v b t ht

#print axioms table_entry_count_polynomial
#print axioms table_bits_polynomial

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
