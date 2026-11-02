import CurrentAdditive.V39RoundedTable

set_option maxHeartbeats 2000000

namespace CurrentAdditive.V39RecursiveGenerator

open CurrentAdditive.V38OneStep

/-- E bounds the logarithms of n and all widths; it is not identified
with ceil(log n) here. The actual schedule must supply that later join. -/
theorem publicA_le_exp (n p₀ q₂ s w Q E : ℕ)
    (hn : n ≤ 2 ^ E) (hp₀ : p₀ ≤ 2 ^ E) (hq₂ : q₂ ≤ 2 ^ E)
    (hs : s ≤ 2 ^ E) (hw : w ≤ 2 ^ E) (hQ : Q ≤ 2 ^ E) :
    publicA n s q₂ w Q p₀ ≤ 2 ^ (2 * E + 9) := by
  let M := 2 ^ E
  change n ≤ M at hn
  change p₀ ≤ M at hp₀
  change q₂ ≤ M at hq₂
  change s ≤ M at hs
  change w ≤ M at hw
  change Q ≤ M at hQ
  have hM : 1 ≤ M := Nat.one_le_pow E 2 (by omega)
  have hprod : 4 * s * (n + s) ≤ 4 * M * (M + M) := by gcongr
  have hsq : M ≤ M ^ 2 := by nlinarith
  have hcap : 512 * M ^ 2 = 2 ^ (2 * E + 9) := by
    dsimp [M]
    rw [show (512 : ℕ) = 2 ^ 9 by decide, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [← hcap]
  unfold publicA
  apply max_le
  · nlinarith
  · apply max_le
    · nlinarith
    · apply max_le
      · nlinarith
      · apply max_le
        · nlinarith
        · exact max_le (by nlinarith) (by nlinarith)

def sampleExponent (E F k : ℕ) : ℕ := F + 1 + ((3 * E + 3) * k + E + 1)

theorem sampleDrawBudget_le_exp (p₀ q₁ q₂ s w Q E F k m : ℕ)
    (hp₀ : p₀ ≤ 2 ^ E) (hq₁ : q₁ ≤ 2 ^ E) (hq₂ : q₂ ≤ 2 ^ E)
    (hs : s ≤ 2 ^ E) (hw : w ≤ 2 ^ E) (hQ : Q ≤ 2 ^ E)
    (hm : m ≤ 2 ^ F) :
    sampleDrawBudget p₀ q₁ q₂ s w Q k m ≤ 2 ^ sampleExponent E F k := by
  unfold sampleDrawBudget
  apply max_le (Nat.one_le_pow _ _ (by omega))
  calc
    2 * m * drawBudget p₀ q₁ q₂ s w Q k
      ≤ 2 * 2 ^ F * 2 ^ ((3 * E + 3) * k + E + 1) := by
        gcongr
        exact drawBudget_le_exp p₀ q₁ q₂ s w Q E k hp₀ hq₁ hq₂ hs hw hQ
    _ = 2 ^ (F + 1) * 2 ^ ((3 * E + 3) * k + E + 1) := by rw [pow_succ]; ring
    _ = 2 ^ sampleExponent E F k := by rw [← pow_add]; rfl

theorem publicBits_le_expSum (A N E K : ℕ)
    (hA : A ≤ 2 ^ (2 * E + 9)) (hN : N ≤ 2 ^ K) :
    publicBits A N ≤ 2 * E + K + 17 := by
  apply Nat.clog_le_of_le_pow
  calc
    200 * A * N ≤ 2 ^ 8 * 2 ^ (2 * E + 9) * 2 ^ K := by gcongr; norm_num
    _ = 2 ^ (2 * E + K + 17) := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- An explicit integer bound on the reserved number of random bits.
Only scalar width/sample bounds are hypotheses, not generator-resource
or correctness certificates. -/
theorem randomBits_le_expSum (A N E K : ℕ)
    (hA : A ≤ 2 ^ (2 * E + 9)) (hN : N ≤ 2 ^ K) :
    publicBits A N * N ≤ 2 ^ (2 * E + 2 * K + 17) := by
  have hbits := publicBits_le_expSum A N E K hA hN
  have hnum : 2 * E + K + 17 ≤ 2 ^ (2 * E + K + 17) := by
    exact Nat.lt_two_pow_self.le
  calc
    publicBits A N * N ≤ 2 ^ (2 * E + K + 17) * 2 ^ K :=
      Nat.mul_le_mul (hbits.trans hnum) hN
    _ = 2 ^ (2 * E + 2 * K + 17) := by rw [← pow_add]; congr 1; omega

#print axioms publicA_le_exp
#print axioms sampleDrawBudget_le_exp
#print axioms publicBits_le_expSum
#print axioms randomBits_le_expSum

end CurrentAdditive.V39RecursiveGenerator
