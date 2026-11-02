import Paper2.YaoLowerBoundTapes

/-!
# Explicit public resource bounds for the Yao construction

Frozen v12 Appendix B, `yao:counts`, `yao:dimensions`,
`yao:materialization`, and `yao:random-bits`.
These bounds concern the actual sample counts, indexed output dimensions,
and Boolean tape positions already used by `matrixFromTape`. The constants
depend only on `t` and `lambda`. Cardinality bounds are not machine-time
bounds; no encoded running-time claim is made here.
-/

namespace Paper2.YaoResources

open Paper2.Yao Paper2.YaoLookup Paper2.YaoLowerBound

/-- A public coefficient for the complete tree's Alice-node count. -/
def treeCoefficient (t : ℕ) : ℕ := 2 ^ (6 * t - 4)

/-- The exact linear selector-count coefficient after absorbing lambda. -/
def selectorCoefficient (t lambda : ℕ) : ℕ :=
  8 * (2 ^ (2 ^ t - 1)) ^ 2 * (2 ^ (t - 1) + lambda)

/-- A quadratic payload-count coefficient, including the integer ceiling. -/
def payloadCoefficient (t lambda : ℕ) : ℕ :=
  (2 ^ t * 2 ^ t + 1) * treeCoefficient t + lambda

def entryCoefficient (t lambda : ℕ) : ℕ :=
  selectorCoefficient t lambda * 2 ^ (t - 1) * payloadCoefficient t lambda

def bitCoefficient (t lambda : ℕ) : ℕ :=
  selectorCoefficient t lambda * 2 ^ (t - 1) +
    payloadCoefficient t lambda * (2 ^ t * 2 ^ t + 1)

/-- Exact number of indexed entries, not the number of distinct values. -/
def tableEntryCount (vertices t b lambda : ℕ) : ℕ :=
  vertices * selectorCount t b lambda * 2 ^ (t - 1) * 2 ^ b * payloadCount t b lambda

theorem height_pos (b : ℕ) : 0 < 2 ^ b := pow_pos (by decide) _

theorem height_ge_one (b : ℕ) : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by decide)

theorem bits_le_height (b : ℕ) : b ≤ 2 ^ b := by
  induction b with
  | zero => norm_num
  | succ b ih =>
      rw [pow_succ]
      have hp := height_ge_one b
      omega

/-- The complete odd-depth tree contributes at most a fixed coefficient
times H squared. The bound includes the `+1` used in the sample count. -/
theorem aliceNodes_add_one_le (t b : ℕ) (ht : 1 ≤ t) :
    aliceNodes (b + 3 * t - 3) + 1 ≤ treeCoefficient t * (2 ^ b) ^ 2 := by
  have hc := aliceNodes_closed (b + 3 * t - 3)
  have he : 2 * (b + 3 * t - 3) + 2 = (6 * t - 4) + b * 2 := by omega
  rw [he, pow_add, pow_mul] at hc
  unfold treeCoefficient
  omega

/-- Delta is at least H. For the source range t>=4 it equals 2^(t-4)H;
natural subtraction also makes this auxiliary bound valid for smaller t. -/
theorem height_le_payloadDelta (t b : ℕ) : 2 ^ b ≤ payloadDelta b t := by
  unfold payloadDelta
  exact Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)

theorem selectorCount_le (t b lambda : ℕ) :
    selectorCount t b lambda ≤ selectorCoefficient t lambda * 2 ^ b := by
  have hh := height_ge_one b
  have hl : lambda ≤ lambda * 2 ^ b := by nlinarith
  unfold selectorCount selectorSampleCount selectorCoefficient
  calc
    _ ≤ 8 * (2 ^ (2 ^ t - 1)) ^ 2 * ((2 ^ (t - 1) + lambda) * 2 ^ b) := by
      apply Nat.mul_le_mul_left
      nlinarith
    _ = _ := by ring

/-- The actual integer ceiling is bounded, rather than replaced by a real
quotient. This controls N_B by a fixed coefficient times H squared. -/
theorem payloadCount_le (t b lambda : ℕ) (ht : 1 ≤ t) :
    payloadCount t b lambda ≤ payloadCoefficient t lambda * (2 ^ b) ^ 2 := by
  have htree := aliceNodes_add_one_le t b ht
  have hh := height_ge_one b
  have hdelta := height_le_payloadDelta t b
  have hnum :
      (2 ^ b * (2 ^ t * 2 ^ t + 1)) * (aliceNodes (b + 3 * t - 3) + 1) + lambda ≤
        2 ^ b * (payloadCoefficient t lambda * (2 ^ b) ^ 2) := by
    have hl : lambda ≤ lambda * (2 ^ b) ^ 3 := by
      have hp : 1 ≤ (2 ^ b) ^ 3 := Nat.one_le_pow _ _ hh
      nlinarith
    calc
      _ ≤ (2 ^ b * (2 ^ t * 2 ^ t + 1)) * (treeCoefficient t * (2 ^ b) ^ 2) +
          lambda * (2 ^ b) ^ 3 := Nat.add_le_add (Nat.mul_le_mul_left _ htree) hl
      _ = _ := by unfold payloadCoefficient; ring
  unfold payloadCount payloadSampleCount
  change _ ⌈/⌉ payloadDelta b t ≤ _
  apply (ceilDiv_le_iff_le_mul (payloadDelta_positive b t)).mpr
  exact hnum.trans (Nat.mul_le_mul_right _ hdelta)

/-- The exact dimension product for the matrix evaluated by matrixFromTape.
This identity holds independently of the tape and the source promise. -/
theorem indexed_entries_eq {V : Type*} [Fintype V] (t b lambda : ℕ) :
    Fintype.card (V × Fin (selectorCount t b lambda)) *
      Fintype.card (Fin (2 ^ (t - 1)) × Fin (2 ^ b) × Fin (payloadCount t b lambda)) =
        tableEntryCount (Fintype.card V) t b lambda := by
  simp [tableEntryCount, Nat.mul_assoc]

/-- Explicit form of the paper's O_{t,lambda}(|V| H^4) output bound. -/
theorem tableEntryCount_le (vertices t b lambda : ℕ) (ht : 1 ≤ t) :
    tableEntryCount vertices t b lambda ≤
      vertices * entryCoefficient t lambda * (2 ^ b) ^ 4 := by
  have ha := selectorCount_le t b lambda
  have hb := payloadCount_le t b lambda ht
  unfold tableEntryCount
  calc
    _ ≤ vertices * (selectorCoefficient t lambda * 2 ^ b) * 2 ^ (t - 1) * 2 ^ b *
        (payloadCoefficient t lambda * (2 ^ b) ^ 2) := by gcongr
    _ = _ := by unfold entryCoefficient; ring

/-- Exact fair-tape length is at most a fixed coefficient times H cubed.
The selector contribution is first bounded by O(H^2), using b<=H. -/
theorem tapeBitCount_le (t b lambda : ℕ) (ht : 1 ≤ t) :
    tapeBitCount t b lambda ≤ bitCoefficient t lambda * (2 ^ b) ^ 3 := by
  have ha := selectorCount_le t b lambda
  have hb := payloadCount_le t b lambda ht
  have hbits := bits_le_height b
  have hh := height_ge_one b
  have hpow : (2 ^ b) ^ 2 ≤ (2 ^ b) ^ 3 := Nat.pow_le_pow_right hh (by decide)
  unfold tapeBitCount
  calc
    _ ≤ (selectorCoefficient t lambda * 2 ^ b) * 2 ^ (t - 1) * 2 ^ b +
        (payloadCoefficient t lambda * (2 ^ b) ^ 2) * 2 ^ b * (2 ^ t * 2 ^ t + 1) := by
      gcongr
    _ = (selectorCoefficient t lambda * 2 ^ (t - 1)) * (2 ^ b) ^ 2 +
        (payloadCoefficient t lambda * (2 ^ t * 2 ^ t + 1)) * (2 ^ b) ^ 3 := by ring
    _ ≤ (selectorCoefficient t lambda * 2 ^ (t - 1)) * (2 ^ b) ^ 3 +
        (payloadCoefficient t lambda * (2 ^ t * 2 ^ t + 1)) * (2 ^ b) ^ 3 := by gcongr
    _ = _ := by unfold bitCoefficient; ring

/-- Rounding the edge count up to a power of two costs less than a factor
of two. The maximum covers the empty source without an exceptional case. -/
theorem paddedEdgeCount_lt (edgeCount : ℕ) :
    paddedEdgeCount edgeCount < 2 * max 1 edgeCount := by
  have hn : 0 < max 1 edgeCount := lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)
  by_cases hsmall : max 1 edgeCount = 1
  · simp [paddedEdgeCount, paddedEdgeBits, hsmall]
  · have hn' : 1 < max 1 edgeCount := by omega
    have hc : 0 < Nat.clog 2 (max 1 edgeCount) := Nat.clog_pos (by decide) hn'
    have hp : 2 ^ (Nat.clog 2 (max 1 edgeCount)).pred < max 1 edgeCount :=
      Nat.pow_pred_clog_lt_self (by decide) hn'
    unfold paddedEdgeCount paddedEdgeBits
    rw [← Nat.succ_pred_eq_of_pos hc, Nat.pow_succ]
    omega

/-- Polynomial output bound in the unpadded edge count, with all constants
displayed. No source promise or random outcome is needed for this bound. -/
theorem padded_tableEntryCount_le (vertices t edgeCount lambda : ℕ) (ht : 1 ≤ t) :
    tableEntryCount vertices t (paddedEdgeBits edgeCount) lambda ≤
      vertices * (16 * entryCoefficient t lambda) * (max 1 edgeCount) ^ 4 := by
  have hh : 2 ^ paddedEdgeBits edgeCount ≤ 2 * max 1 edgeCount :=
    Nat.le_of_lt (paddedEdgeCount_lt edgeCount)
  calc
    _ ≤ vertices * entryCoefficient t lambda * (2 ^ paddedEdgeBits edgeCount) ^ 4 :=
      tableEntryCount_le vertices t _ lambda ht
    _ ≤ vertices * entryCoefficient t lambda * (2 * max 1 edgeCount) ^ 4 := by gcongr
    _ = _ := by ring

/-- The exact fair-bit tape likewise has polynomial length in the source's
edge count; this is a randomness bound, not a time-complexity theorem. -/
theorem padded_tapeBitCount_le (t edgeCount lambda : ℕ) (ht : 1 ≤ t) :
    tapeBitCount t (paddedEdgeBits edgeCount) lambda ≤
      (8 * bitCoefficient t lambda) * (max 1 edgeCount) ^ 3 := by
  have hh : 2 ^ paddedEdgeBits edgeCount ≤ 2 * max 1 edgeCount :=
    Nat.le_of_lt (paddedEdgeCount_lt edgeCount)
  calc
    _ ≤ bitCoefficient t lambda * (2 ^ paddedEdgeBits edgeCount) ^ 3 :=
      tapeBitCount_le t _ lambda ht
    _ ≤ bitCoefficient t lambda * (2 * max 1 edgeCount) ^ 3 := by gcongr
    _ = _ := by ring

/-- Directly bounds the finite set of bit positions read by the actual
generator, using its already proved exact-cardinality identity. -/
theorem tapePosition_card_le (t edgeCount lambda : ℕ) (ht : 1 ≤ t) :
    Fintype.card (TapePosition t (paddedEdgeBits edgeCount) lambda) ≤
      (8 * bitCoefficient t lambda) * (max 1 edgeCount) ^ 3 := by
  rw [card_tapePosition]
  exact padded_tapeBitCount_le t edgeCount lambda ht

end Paper2.YaoResources
