import CurrentAdditive.V39IterationArithmetic

/-! Concrete scalar exponents for the selected full-product schedule.
These instantiate width and sample hypotheses in the recursive generator;
they are not a physical program or a whole-printer execution theorem.
The imported schedule packet is frozen and is not edited by this extension. -/

namespace V39PublicSchedule

open V38Schedule

def fullWidthExponent (L : ℕ) : ℕ := 16 * L
def fullSampleExponent (L k : ℕ) : ℕ := 32 * (k + 1) * L

/-- A single exponent covers every width used by the recursive generator,
including the restoration width Q and the lookup seed width. -/
theorem full_widths_le_pow (n L : ℕ) (hL : 16 ≤ L) (hn : n ≤ 2 ^ L) :
    n ≤ 2 ^ fullWidthExponent L ∧
    seedWidth L ≤ 2 ^ fullWidthExponent L ∧
    fullQ₁ L ≤ 2 ^ fullWidthExponent L ∧
    fullQ₂ L ≤ 2 ^ fullWidthExponent L ∧
    fullS L ≤ 2 ^ fullWidthExponent L ∧
    fullW L ≤ 2 ^ fullWidthExponent L ∧
    fullQ L ≤ 2 ^ fullWidthExponent L := by
  have he := ell_le L
  have hs : fullS L ≤ 2 ^ fullWidthExponent L := by
    unfold fullS fullWidthExponent
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hp₀ : seedWidth L ≤ 2 ^ fullWidthExponent L := by
    rw [seedWidth_exact]
    unfold fullWidthExponent
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hq₂ : fullQ₂ L ≤ 2 ^ fullWidthExponent L := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1
    rw [(full_power_logs L).2.1]
    unfold fullWidthExponent
    omega
  have hw : fullW L ≤ 2 ^ fullWidthExponent L := by
    unfold fullW fullWidthExponent
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hQ : fullQ L ≤ 2 ^ fullWidthExponent L := by
    rw [fullQ_pow]
    unfold fullQlog fullWidthExponent
    exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨hn.trans ?_, hp₀, ?_, hq₂, hs, hw, hQ⟩
  · unfold fullWidthExponent
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact (Nat.sub_le (fullS L) 2).trans hs

theorem full_widths_at_clog (n : ℕ) (hL : 16 ≤ Nat.clog 2 n) :
    let L := Nat.clog 2 n
    n ≤ 2 ^ fullWidthExponent L ∧
    seedWidth L ≤ 2 ^ fullWidthExponent L ∧
    fullQ₁ L ≤ 2 ^ fullWidthExponent L ∧
    fullQ₂ L ≤ 2 ^ fullWidthExponent L ∧
    fullS L ≤ 2 ^ fullWidthExponent L ∧
    fullW L ≤ 2 ^ fullWidthExponent L ∧
    fullQ L ≤ 2 ^ fullWidthExponent L := by
  exact full_widths_le_pow n (Nat.clog 2 n) hL (Nat.le_pow_clog (by decide) n)

/-- The actual direct-square sample side fits a fixed exponent times
`(k+1)*L`. Its only schedule premise is the literal full test predicate. -/
theorem full_sampleSide_le_pow (c : ℚ) (L m k : ℕ) (δv ζ : ℚ)
    (htest : FullTests c L m δv ζ) :
    sampleSide L k ≤ 2 ^ fullSampleExponent L k := by
  have hb := (fullTests_iteration_bounds c L m k δv ζ htest).1
  have hh := (fullTests_iteration_bounds c L m k δv ζ htest).2
  have hL : 16 ≤ L := htest.2.2.1
  have hc : Nat.clog 2 (B L k + 2) ≤ B L k + 1 := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
    exact Nat.lt_pow_self (by decide : 1 < 2)
  apply (sampleSide_le_power L k).trans
  apply Nat.pow_le_pow_right (by decide)
  unfold fullSampleExponent
  have hkL : 0 ≤ k * L := Nat.zero_le _
  nlinarith only [hb, hh, hc, hL, hkL]

theorem full_sampleEntries_le_pow (c : ℚ) (L m k : ℕ) (δv ζ : ℚ)
    (htest : FullTests c L m δv ζ) :
    sampleEntries L k ≤ 2 ^ (64 * (k + 1) * L) := by
  have hs := full_sampleSide_le_pow c L m k δv ζ htest
  unfold sampleEntries
  calc
    sampleSide L k ^ 2 ≤ (2 ^ fullSampleExponent L k) ^ 2 :=
      Nat.pow_le_pow_left hs 2
    _ = 2 ^ (64 * (k + 1) * L) := by
      rw [← pow_mul]
      congr 1
      unfold fullSampleExponent
      ring

theorem full_positive_widths (L : ℕ) :
    0 < seedWidth L ∧ 0 < fullQ₁ L ∧ 0 < fullQ₂ L ∧
    0 < fullS L ∧ 0 < 4 * fullS L ∧ 0 < fullS L - 3 ∧
    0 < fullW L ∧ 0 < fullQ L := by
  have hs := fullS_ge_256 L
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [seedWidth_exact]
    positivity
  · unfold fullQ₁
    omega
  · unfold fullQ₂ fullS
    positivity
  · omega
  · positivity
  · omega
  · unfold fullW
    positivity
  · unfold fullQ fullW
    positivity

#print axioms fullWidthExponent
#print axioms fullSampleExponent
#print axioms full_widths_le_pow
#print axioms full_widths_at_clog
#print axioms full_sampleSide_le_pow
#print axioms full_sampleEntries_le_pow
#print axioms full_positive_widths

end V39PublicSchedule
