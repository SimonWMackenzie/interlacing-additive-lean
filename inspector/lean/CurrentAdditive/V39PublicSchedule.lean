import CurrentAdditive.V38Schedule

/-! Literal integer schedule and iteration/sample arithmetic for v39.
Source: `sections/amplifier.tex`, `sections/sampling.tex`, and
`appendices/parameters.tex`. These numeric identities do not construct the
iterated matrices or implement the sampler. -/

namespace V39PublicSchedule

open V38Schedule

theorem pow2Ceil_le_iff (a b : ℕ) :
    pow2Ceil a ≤ 2 ^ b ↔ a ≤ 2 ^ b := by
  unfold pow2Ceil
  rw [Nat.pow_le_pow_iff_right (by decide : 1 < 2),
    Nat.clog_le_iff_le_pow (by decide : 1 < 2)]

theorem pow2Ceil_lower (a : ℕ) : a ≤ pow2Ceil a :=
  Nat.le_pow_clog (by decide) a

theorem pow2Ceil_lt_twice (a : ℕ) (ha : 0 < a) : pow2Ceil a < 2 * a := by
  by_cases hsmall : a ≤ 1
  · have heq : a = 1 := by omega
    simp [heq, pow2Ceil]
  · have ha1 : 1 < a := by omega
    have hc := Nat.clog_pos (by decide : 1 < 2) ha1
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) ha1
    change 2 ^ (Nat.clog 2 a - 1) < a at hp
    have he : Nat.clog 2 a = (Nat.clog 2 a - 1) + 1 := by omega
    unfold pow2Ceil
    rw [he, pow_succ]
    omega

theorem ell_rounding (L : ℕ) :
    L + 1 ≤ 2 ^ ell L ∧ 2 ^ ell L < 2 * (L + 1) := by
  exact ⟨Nat.le_pow_clog (by decide) (L + 1),
    pow2Ceil_lt_twice (L + 1) (by omega)⟩

theorem ell_le (L : ℕ) : ell L ≤ L := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  exact Nat.lt_pow_self (by decide : 1 < 2)

theorem quarterCeil_rounding (L : ℕ) :
    L ≤ 4 * quarterCeil L ∧ 4 * quarterCeil L < L + 4 := by
  unfold quarterCeil
  omega

theorem generatedS_fourth_rounding (L : ℕ) :
    generatedN L ≤ (generatedS L) ^ 4 ∧
      (generatedS L) ^ 4 < 16 * generatedN L := by
  have h := quarterCeil_rounding L
  have he : (generatedS L) ^ 4 = 2 ^ (4 * quarterCeil L) := by
    unfold generatedS
    rw [← pow_mul]
    congr 1
    omega
  rw [he]
  constructor
  · exact Nat.pow_le_pow_right (by decide) h.1
  · have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) h.2
    simpa [pow_add, generatedN, Nat.mul_comm] using hp

theorem fullS_rounding (L : ℕ) :
    2 ^ 16 * (L + 1) ≤ fullS L ∧ fullS L < 2 ^ 17 * (L + 1) := by
  have h := ell_rounding L
  unfold fullS
  rw [pow_add]
  constructor <;> nlinarith only [h.1, h.2]

theorem full_power_logs (L : ℕ) :
    Nat.clog 2 (fullS L) = 16 + ell L ∧
    Nat.clog 2 (fullQ₂ L) = L + 2 * (16 + ell L) ∧
    Nat.clog 2 (fullW L) = 8 * ell L ∧
    Nat.clog 2 (fullQ L) = 16 * ell L := by
  have hq₂ : fullQ₂ L = 2 ^ (L + 2 * (16 + ell L)) := by
    unfold fullQ₂ fullS
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hq₂, fullQ_pow]
  simp [fullS, fullW, fullQlog, Nat.clog_pow 2 _ (by decide)]

theorem generated_power_logs (L : ℕ) :
    Nat.clog 2 (generatedS L) = quarterCeil L ∧
    Nat.clog 2 (generatedQ₂ L) = 4 * L ∧
    Nat.clog 2 (generatedW L) = 2 * L ∧
    Nat.clog 2 (generatedQ L) = 6 * L := by
  have hq₂ : generatedQ₂ L = 2 ^ (4 * L) := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    congr 1
    omega
  have hw : generatedW L = 2 ^ (2 * L) := by
    unfold generatedW generatedN
    rw [← pow_mul]
    congr 1
    omega
  rw [hq₂, hw, generatedQ_pow]
  simp [generatedS, generatedQlog, Nat.clog_pow 2 _ (by decide)]

def seedWidth (L : ℕ) : ℕ := pow2Ceil (64 * (L + 1))
def seedCost (L : ℕ) : ℕ := ell L + 7
def fullOverhead (L : ℕ) : ℕ := L + 64 + 28 * ell L
def generatedOverhead (L : ℕ) : ℕ := 12 * L + 2 * quarterCeil L

theorem seedWidth_exact (L : ℕ) : seedWidth L = 2 ^ (6 + ell L) := by
  unfold seedWidth pow2Ceil ell
  have hlow := Nat.le_pow_clog (by decide : 1 < 2) (L + 1)
  have hhigh := pow2Ceil_lt_twice (L + 1) (by omega)
  unfold pow2Ceil at hhigh
  have hlog : Nat.clog 2 (64 * (L + 1)) = 6 + Nat.clog 2 (L + 1) := by
    apply le_antisymm
    · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
      rw [pow_add]
      norm_num
      omega
    · by_contra hn
      have hlt : Nat.clog 2 (64 * (L + 1)) ≤ 5 + Nat.clog 2 (L + 1) := by omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hlt
      have ht := Nat.le_pow_clog (by decide : 1 < 2) (64 * (L + 1))
      rw [pow_add] at hp
      norm_num at hp
      nlinarith only [hhigh, hp, ht]
  rw [hlog]

theorem seedCost_exact (L : ℕ) :
    Nat.clog 2 (seedWidth L) + 1 = seedCost L := by
  rw [seedWidth_exact, Nat.clog_pow 2 _ (by decide)]
  unfold seedCost
  omega

theorem fullOverhead_exact (L : ℕ) :
    2 * Nat.clog 2 (fullS L) + Nat.clog 2 (fullQ₂ L) +
      Nat.clog 2 (fullW L) + Nat.clog 2 (fullQ L) = fullOverhead L := by
  obtain ⟨hs, hq, hw, hQ⟩ := full_power_logs L
  rw [hs, hq, hw, hQ]
  exact full_overhead L

theorem generatedOverhead_exact (L : ℕ) :
    2 * Nat.clog 2 (generatedS L) + Nat.clog 2 (generatedQ₂ L) +
      Nat.clog 2 (generatedW L) + Nat.clog 2 (generatedQ L) =
        generatedOverhead L := by
  obtain ⟨hs, hq, hw, hQ⟩ := generated_power_logs L
  rw [hs, hq, hw, hQ]
  exact generated_overhead L

def B (L k : ℕ) : ℕ := seedCost L + k * fullOverhead L
def H (L k : ℕ) : ℕ := B L k + k
def rankBound (L k : ℕ) : ℕ := 2 ^ (B L k - 1)

theorem B_zero (L : ℕ) : B L 0 = seedCost L := by simp [B]
theorem B_succ (L k : ℕ) : B L (k + 1) = B L k + fullOverhead L := by
  unfold B
  ring
theorem H_succ (L k : ℕ) : H L (k + 1) = H L k + fullOverhead L + 1 := by
  unfold H
  rw [B_succ]
  omega
theorem B_ge_seven (L k : ℕ) : 7 ≤ B L k := by unfold B seedCost; omega
theorem rankBound_succ (L k : ℕ) :
    rankBound L (k + 1) = 2 ^ fullOverhead L * rankBound L k := by
  have hb := B_ge_seven L k
  unfold rankBound
  rw [B_succ, show B L k + fullOverhead L - 1 =
    fullOverhead L + (B L k - 1) by omega, pow_add]

def sampleSide (L k : ℕ) : ℕ :=
  pow2Ceil (16 * (rankBound L k + 1) *
    Nat.clog 2 (rankBound L k + 2) * 2 ^ H L k)
def sampleEntries (L k : ℕ) : ℕ := sampleSide L k ^ 2

theorem rankBound_add_one_le (L k : ℕ) : rankBound L k + 1 ≤ 2 ^ B L k := by
  have hb := B_ge_seven L k
  have hr : 1 ≤ rankBound L k := by
    have hp : 0 < rankBound L k := by unfold rankBound; positivity
    omega
  have he : 2 ^ B L k = 2 * rankBound L k := by
    unfold rankBound
    calc
      2 ^ B L k = 2 ^ ((B L k - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (B L k - 1) := by rw [pow_succ]; omega
  omega

theorem rankBound_clog_le (L k : ℕ) :
    Nat.clog 2 (rankBound L k + 2) ≤ B L k + 1 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  rw [pow_succ]
  have hr := rankBound_add_one_le L k
  have hp : 1 ≤ 2 ^ B L k := by
    have h : 0 < 2 ^ B L k := by positivity
    omega
  omega

theorem sampleSide_le_power (L k : ℕ) :
    sampleSide L k ≤
      2 ^ (4 + B L k + Nat.clog 2 (B L k + 2) + H L k) := by
  apply (pow2Ceil_le_iff _ _).2
  have hr := rankBound_add_one_le L k
  have hc : Nat.clog 2 (rankBound L k + 2) ≤ 2 ^ Nat.clog 2 (B L k + 2) := by
    exact (rankBound_clog_le L k).trans
      ((by omega : B L k + 1 ≤ B L k + 2).trans
        (Nat.le_pow_clog (by decide) (B L k + 2)))
  calc
    _ ≤ 16 * (2 ^ B L k) * (2 ^ Nat.clog 2 (B L k + 2)) * 2 ^ H L k := by
      gcongr
    _ = _ := by
      rw [pow_add, pow_add, pow_add]
      norm_num <;> ring

theorem sampleEntries_clog_upper (L k : ℕ) :
    Nat.clog 2 (sampleEntries L k) ≤
      4 * B L k + 2 * k + 2 * Nat.clog 2 (B L k + 2) + 8 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  have hm := sampleSide_le_power L k
  have hsq := Nat.pow_le_pow_left hm 2
  unfold sampleEntries
  calc
    sampleSide L k ^ 2 ≤
        (2 ^ (4 + B L k + Nat.clog 2 (B L k + 2) + H L k)) ^ 2 := hsq
    _ = _ := by
      rw [← pow_mul]
      congr 1
      unfold H
      omega

theorem sampleSide_lower (L k : ℕ) : 2 ^ H L k ≤ sampleSide L k := by
  have hr : 0 < rankBound L k := by unfold rankBound; positivity
  have hc : 0 < Nat.clog 2 (rankBound L k + 2) :=
    Nat.clog_pos (by decide) (by omega)
  have hf : 1 ≤ 16 * (rankBound L k + 1) * Nat.clog 2 (rankBound L k + 2) := by
    have hh : 0 < 16 * (rankBound L k + 1) * Nat.clog 2 (rankBound L k + 2) := by
      positivity
    omega
  calc
    2 ^ H L k ≤ 16 * (rankBound L k + 1) *
        Nat.clog 2 (rankBound L k + 2) * 2 ^ H L k := by
      exact Nat.le_mul_of_pos_left _ hf
    _ ≤ sampleSide L k := pow2Ceil_lower _

theorem sampleEntries_lower (L k : ℕ) : 2 ^ k ≤ sampleEntries L k := by
  have hm := sampleSide_lower L k
  have hp : 2 ^ k ≤ 2 ^ H L k :=
    Nat.pow_le_pow_right (by decide) (by unfold H; omega)
  have hs : 1 ≤ sampleSide L k := by
    have h : 1 ≤ 2 ^ H L k := by
      have hh : 0 < 2 ^ H L k := by positivity
      omega
    omega
  unfold sampleEntries
  nlinarith only [hm, hp, hs]

#print axioms pow2Ceil_le_iff
#print axioms pow2Ceil_lower
#print axioms pow2Ceil_lt_twice
#print axioms ell_rounding
#print axioms ell_le
#print axioms quarterCeil_rounding
#print axioms generatedS_fourth_rounding
#print axioms fullS_rounding
#print axioms full_power_logs
#print axioms generated_power_logs
#print axioms seedWidth_exact
#print axioms seedCost_exact
#print axioms fullOverhead_exact
#print axioms generatedOverhead_exact
#print axioms B_zero
#print axioms B_succ
#print axioms H_succ
#print axioms B_ge_seven
#print axioms rankBound_succ
#print axioms rankBound_add_one_le
#print axioms rankBound_clog_le
#print axioms sampleSide_le_power
#print axioms sampleEntries_clog_upper
#print axioms sampleSide_lower
#print axioms sampleEntries_lower

end V39PublicSchedule
