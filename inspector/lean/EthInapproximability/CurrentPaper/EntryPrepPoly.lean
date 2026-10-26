import EthInapproximability.CurrentPaper.SeedTable
import EthInapproximability.CurrentPaper.IndexSeed
import EthInapproximability.CurrentPaper.EffectiveIteration

/-!
# Segment 7 (partial): the seed-table clock is polynomial in `n`

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

`seed_bound_poly`: the clock `SeedTable.bound (width (sourceDepth n))` of owner-6's charged
counting program (`EntrySeedSpec.seed_table_spec`) is at most `7 * ((2 (n+2))^128 * 2^128)^2`, hence at most
`7 * ((4 (n + ℓ + 1))^128 * 2^128)^2` for every `ℓ` (in particular `ℓ = |enc G|`). Coarse constants, as the
plan allows. Source of the growth: `width b < 128 (b+1)` (admitted `IndexSeed.width_lt`) and
`2^(sourceDepth n) ≤ 2 (n+2)` (`Nat.clog`).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepPoly

theorem two_pow_depth (n : ℕ) : 2 ^ EffectiveIteration.sourceDepth n ≤ 2 * (n + 2) := by
  unfold EffectiveIteration.sourceDepth
  have h1 : 1 ≤ Nat.clog 2 (n + 2) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 2)
    rw [h] at this
    simp at this
  have h2 := Nat.pow_pred_clog_lt_self (b := 2) (x := n + 2) (by norm_num) (by omega)
  have h3 : 2 ^ Nat.clog 2 (n + 2) = 2 * 2 ^ (Nat.clog 2 (n + 2)).pred := by
    have e : (Nat.clog 2 (n + 2)).pred + 1 = Nat.clog 2 (n + 2) := Nat.succ_pred_eq_of_pos h1
    rw [← pow_succ', e]
  rw [h3]
  omega

theorem two_pow_width (n : ℕ) :
    2 ^ IndexSeed.width (EffectiveIteration.sourceDepth n) ≤ (2 * (n + 2)) ^ 128 * 2 ^ 128 := by
  have hw := IndexSeed.width_lt (EffectiveIteration.sourceDepth n)
  have hb := two_pow_depth n
  calc 2 ^ IndexSeed.width (EffectiveIteration.sourceDepth n)
      ≤ 2 ^ (128 * EffectiveIteration.sourceDepth n + 128) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ EffectiveIteration.sourceDepth n) ^ 128 * 2 ^ 128 := by
        rw [pow_add, mul_comm 128 _, pow_mul]
    _ ≤ (2 * (n + 2)) ^ 128 * 2 ^ 128 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hb _)

theorem seed_bound_sq (w : ℕ) : SeedTable.bound w ≤ 7 * (2 ^ w) ^ 2 := by
  unfold SeedTable.bound
  have hX : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have hwX : w < 2 ^ w := Nat.lt_two_pow_self
  have hs : 2 ^ w - 1 + 1 = 2 ^ w := Nat.sub_add_cancel hX
  rw [hs]
  nlinarith

/-- The seed-table clock is polynomial in `n` (constants left unevaluated). -/
theorem seed_bound_poly (n : ℕ) :
    SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) ≤
      7 * ((2 * (n + 2)) ^ 128 * 2 ^ 128) ^ 2 :=
  le_trans (seed_bound_sq _) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (two_pow_width n) _))

/-- The same in the public shape `(n + ℓ + 1)^O(1)` (take `ℓ = |enc G|`). -/
theorem seed_bound_poly' (n ℓ : ℕ) :
    SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) ≤
      7 * ((4 * (n + ℓ + 1)) ^ 128 * 2 ^ 128) ^ 2 := by
  refine le_trans (seed_bound_poly n) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ?_ _)) _))
  omega

#print axioms two_pow_depth
#print axioms two_pow_width
#print axioms seed_bound_sq
#print axioms seed_bound_poly
#print axioms seed_bound_poly'

end EthInapproximability.CurrentPaper.EntryPrepPoly
