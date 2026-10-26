import Paper2.GeneratorSize
import CurrentAdditive.GenericSupportTailFetch

/-! A source-size bound for arbitrary base generator syntax. The bound is
measured against the complete base syntax size, so the rational weights and
the printed table cannot disappear into a dimension-only parameter. -/

namespace Paper2.GenericRecursiveCodeSize

set_option maxHeartbeats 1000000

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource

def baseSize (row₀ col₀ : Code) : ℕ :=
  codeSize row₀ + codeSize col₀ + 1

def scale (n s q₁ q₂ w Q : ℕ) (row₀ col₀ : Code) : ℕ :=
  Paper2.GeneratorSize.scale n (baseSize row₀ col₀) s q₁ q₂ w Q

theorem recursive_size_le_scale (n s q₁ q₂ w Q : ℕ)
    (row₀ col₀ : Code) (k : ℕ) :
    let c := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
    codeSize c.1 + codeSize c.2 + 1 ≤
      (scale n s q₁ q₂ w Q row₀ col₀) ^ (9 * (k + 1)) := by
  let B := baseSize row₀ col₀
  let T := scale n s q₁ q₂ w Q row₀ col₀
  have hT : 513 ≤ T := Paper2.GeneratorSize.scale_ge _ _ _ _ _ _ _
  induction k with
  | zero =>
      have hBT : B ≤ T := by dsimp [B, T, scale, Paper2.GeneratorSize.scale]; omega
      have hpow : T ≤ T ^ 9 := by
        have h1 : 1 ≤ T ^ 8 := Nat.one_le_pow _ _ (by omega)
        calc
          T = T * 1 := by omega
          _ ≤ T * T ^ 8 := Nat.mul_le_mul_left T h1
          _ = T ^ 9 := by ring
      simpa only [recursiveCodes, Nat.zero_add, Nat.mul_one] using
        hBT.trans hpow
  | succ k ih =>
      have hs := Paper2.GeneratorSize.recursive_total_step n B s q₁ q₂ w Q
        row₀ col₀ k
      change codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k + 1)).1 +
          codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k + 1)).2 + 1 ≤
        T ^ (9 * (k + 1 + 1))
      calc
        codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k + 1)).1 +
            codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k + 1)).2 + 1
          ≤ T ^ 9 *
            (codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1 +
              codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 + 1) := hs
        _ ≤ T ^ 9 * T ^ (9 * (k + 1)) := Nat.mul_le_mul_left _ ih
        _ = T ^ (9 * (k + 1 + 1)) := by
          rw [← pow_add]
          congr 1
          omega

/-- If each public scalar and the complete two-code base syntax fit below
`2^L`, then every recursive code pair has singly exponential size in
`(k+1)(L+1)`. -/
theorem recursive_size_le_exp (n s q₁ q₂ w Q L : ℕ)
    (row₀ col₀ : Code) (k : ℕ)
    (hn : n ≤ 2 ^ L) (hs : s ≤ 2 ^ L)
    (hq₁ : q₁ ≤ 2 ^ L) (hq₂ : q₂ ≤ 2 ^ L)
    (hw : w ≤ 2 ^ L) (hQ : Q ≤ 2 ^ L)
    (hbase : baseSize row₀ col₀ ≤ 2 ^ L) :
    let c := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
    codeSize c.1 + codeSize c.2 + 1 ≤
      2 ^ (9 * (k + 1) * (L + 10)) := by
  let T := scale n s q₁ q₂ w Q row₀ col₀
  have h1 : 1 ≤ 2 ^ L := Nat.one_le_pow _ _ (by omega)
  have hT : T ≤ 2 ^ (L + 10) := by
    have hsmall : T ≤ 7 * 2 ^ L + 513 := by
      dsimp [T, scale, Paper2.GeneratorSize.scale]
      omega
    rw [pow_add]
    norm_num
    omega
  have hpow : T ^ (9 * (k + 1)) ≤
      (2 ^ (L + 10)) ^ (9 * (k + 1)) :=
    Nat.pow_le_pow_left hT _
  have hsize := recursive_size_le_scale n s q₁ q₂ w Q row₀ col₀ k
  exact hsize.trans (hpow.trans (by
    rw [← pow_mul, Nat.mul_comm (L + 10) (9 * (k + 1))]))

#print axioms recursive_size_le_scale
#print axioms recursive_size_le_exp

end Paper2.GenericRecursiveCodeSize
