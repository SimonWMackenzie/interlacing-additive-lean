import CurrentAdditive.V39BitGrowth
import CurrentAdditive.V39FullResourceBounds
import CurrentAdditive.V39FullCutoff

/-! Literal full-schedule resource bounds for the actual recursive sample.
No bound on a program's alphabet or draws is assumed. The program below
is the same recursive `sampleProgram` used by the fixed-bit sampler. -/

namespace V39FullSampleResources

open V38Schedule V39PublicSchedule
open CurrentAdditive.V39RecursiveGenerator CurrentAdditive.V38OneStep

private instance seedWidthNeZero (L : ℕ) : NeZero (seedWidth L) :=
  ⟨ne_of_gt (full_positive_widths L).1⟩
private instance fullQ₁NeZero (L : ℕ) : NeZero (fullQ₁ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.1⟩
private instance fullQ₂NeZero (L : ℕ) : NeZero (fullQ₂ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.1⟩
private instance fullSNeZero (L : ℕ) : NeZero (fullS L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.1⟩
private instance fourFullSNeZero (L : ℕ) : NeZero (4 * fullS L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.1⟩
private instance fullSMinusThreeNeZero (L : ℕ) : NeZero (fullS L - 3) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.1⟩
private instance fullWNeZero (L : ℕ) : NeZero (fullW L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.1⟩
private instance fullQNeZero (L : ℕ) : NeZero (fullQ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.2⟩

/-- Both ordered samples of complete labels, with the literal public m. -/
def fullSampleProgram (n L k : ℕ) [NeZero n] :=
  sampleProgram n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
    (fullW L) (fullQ L) k (sampleSide L k)

def fullAlphabet (n L : ℕ) : ℕ :=
  publicA n (fullS L) (fullQ₂ L) (fullW L) (fullQ L) (seedWidth L)

def fullDrawCap (L k : ℕ) : ℕ :=
  sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
    (fullW L) (fullQ L) k (sampleSide L k)

def fullDrawExponent (L k : ℕ) : ℕ :=
  sampleExponent (fullWidthExponent L) (fullSampleExponent L k) k

/-- Number of fair bits in one reserved block. -/
def fullBlockLength (n L k : ℕ) : ℕ :=
  publicBits (fullAlphabet n L) (fullDrawCap L k)

/-- Total number of reserved fair bits, across all draw blocks. -/
def fullReservedBits (n L k : ℕ) : ℕ :=
  fullBlockLength n L k * fullDrawCap L k

theorem fullAlphabet_le (n L : ℕ) (hL : 16 ≤ L) (hn : n ≤ 2 ^ L) :
    fullAlphabet n L ≤ 2 ^ (2 * fullWidthExponent L + 9) := by
  obtain ⟨hnE, hp₀, _, hq₂, hs, hw, hQ⟩ := full_widths_le_pow n L hL hn
  exact publicA_le_exp n (seedWidth L) (fullQ₂ L) (fullS L) (fullW L)
    (fullQ L) (fullWidthExponent L) hnE hp₀ hq₂ hs hw hQ

theorem fullDrawCap_le (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (htest : FullTests c L edgeCount δv ζ) :
    fullDrawCap L k ≤ 2 ^ fullDrawExponent L k := by
  have hL : 16 ≤ L := htest.2.2.1
  obtain ⟨_, hp₀, hq₁, hq₂, hs, hw, hQ⟩ :=
    full_widths_le_pow (2 ^ L) L hL le_rfl
  exact sampleDrawBudget_le_exp (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (fullWidthExponent L)
    (fullSampleExponent L k) k (sampleSide L k) hp₀ hq₁ hq₂ hs hw hQ
    (full_sampleSide_le_pow c L edgeCount k δv ζ htest)

theorem fullSampleProgram_maxAlphabet (n L k : ℕ) [NeZero n]
    (hL : 16 ≤ L) (hn : n ≤ 2 ^ L) :
    (fullSampleProgram n L k).maxAlphabet ≤
      2 ^ (2 * fullWidthExponent L + 9) := by
  exact (alphabet_sampleProgram_le n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (by have h := fullS_ge_256 L; omega)
    rfl k (sampleSide L k)).trans (fullAlphabet_le n L hL hn)

theorem fullSampleProgram_maxDraws (n : ℕ) [NeZero n]
    (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (htest : FullTests c L edgeCount δv ζ) :
    (fullSampleProgram n L k).maxDraws ≤ 2 ^ fullDrawExponent L k := by
  exact (draws_sampleProgram_le n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) k (sampleSide L k)).trans
      (fullDrawCap_le c L edgeCount k δv ζ htest)

theorem fullBlockLength_le (n : ℕ) (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2 ^ L) (htest : FullTests c L edgeCount δv ζ) :
    fullBlockLength n L k ≤
      2 * fullWidthExponent L + fullDrawExponent L k + 17 := by
  exact publicBits_le_expSum (fullAlphabet n L) (fullDrawCap L k)
    (fullWidthExponent L) (fullDrawExponent L k)
    (fullAlphabet_le n L htest.2.2.1 hn)
    (fullDrawCap_le c L edgeCount k δv ζ htest)

theorem fullReservedBits_le (n : ℕ) (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2 ^ L) (htest : FullTests c L edgeCount δv ζ) :
    fullReservedBits n L k ≤
      2 ^ (2 * fullWidthExponent L + 2 * fullDrawExponent L k + 17) := by
  exact randomBits_le_expSum (fullAlphabet n L) (fullDrawCap L k)
    (fullWidthExponent L) (fullDrawExponent L k)
    (fullAlphabet_le n L htest.2.2.1 hn)
    (fullDrawCap_le c L edgeCount k δv ζ htest)

theorem budget_exponents_linear (L k : ℕ) (hL : 16 ≤ L) :
    fullDrawExponent L k ≤ 96 * (k + 1) * L ∧
    2 * fullWidthExponent L + fullDrawExponent L k + 17 ≤ 144 * (k + 1) * L ∧
    2 * fullWidthExponent L + 2 * fullDrawExponent L k + 17 ≤
      240 * (k + 1) * L := by
  have hkL := Nat.mul_le_mul_left k hL
  have hkL0 : 0 ≤ k * L := Nat.zero_le _
  have hK : fullDrawExponent L k ≤ 96 * (k + 1) * L := by
    unfold fullDrawExponent sampleExponent fullWidthExponent fullSampleExponent
    nlinarith only [hkL, hkL0, hL]
  refine ⟨hK, ?_, ?_⟩
  · unfold fullWidthExponent
    nlinarith only [hK, hkL0, hL]
  · unfold fullWidthExponent
    nlinarith only [hK, hkL0, hL]

/-- Concrete absolute exponents for the same recursive sample program and
its actual public bit-block reservation. No program-resource cap is a premise. -/
theorem full_sample_resources (n : ℕ) [NeZero n]
    (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2 ^ L) (htest : FullTests c L edgeCount δv ζ) :
    (fullSampleProgram n L k).maxAlphabet ≤ 2 ^ (33 * L) ∧
    (fullSampleProgram n L k).maxDraws ≤ 2 ^ (96 * (k + 1) * L) ∧
    fullBlockLength n L k ≤ 144 * (k + 1) * L ∧
    fullReservedBits n L k ≤ 2 ^ (240 * (k + 1) * L) := by
  have hL : 16 ≤ L := htest.2.2.1
  obtain ⟨hK, hb, hbits⟩ := budget_exponents_linear L k hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (fullSampleProgram_maxAlphabet n L k hL hn).trans
      (Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega))
  · exact (fullSampleProgram_maxDraws n c L edgeCount k δv ζ htest).trans
      (Nat.pow_le_pow_right (by decide) hK)
  · exact (fullBlockLength_le n c L edgeCount k δv ζ hn htest).trans hb
  · exact (fullReservedBits_le n c L edgeCount k δv ζ hn htest).trans
      (Nat.pow_le_pow_right (by decide) hbits)

/-- The public source parameters and L=ceil(log2 n) are substituted literally.
The admissibility test remains visible for the separate all-large cutoff. -/
theorem full_public_sample_resources (n Δ edgeCount k : ℕ) [NeZero n] (γ : ℚ)
    (htest : FullPublicTests γ Δ n edgeCount (Nat.clog 2 n)) :
    let L := Nat.clog 2 n
    (fullSampleProgram n L k).maxAlphabet ≤ 2 ^ (33 * L) ∧
    (fullSampleProgram n L k).maxDraws ≤ 2 ^ (96 * (k + 1) * L) ∧
    fullBlockLength n L k ≤ 144 * (k + 1) * L ∧
    fullReservedBits n L k ≤ 2 ^ (240 * (k + 1) * L) := by
  exact full_sample_resources n (fullConstant γ Δ n edgeCount)
    (Nat.clog 2 n) edgeCount k (sourceDeltaV γ Δ n edgeCount) (sourceZeta γ)
    (Nat.le_pow_clog (by decide) n) htest

/-- Every sufficiently large promised source supplies the bounds without
an assumed test result or any assumed resource cap. -/
theorem full_promised_sample_resources (n Δ edgeCount k : ℕ) [NeZero n] (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hnm : n ≤ 2 * edgeCount) (hdeg : 2 * edgeCount ≤ Δ * n)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ n) :
    let L := Nat.clog 2 n
    (fullSampleProgram n L k).maxAlphabet ≤ 2 ^ (33 * L) ∧
    (fullSampleProgram n L k).maxDraws ≤ 2 ^ (96 * (k + 1) * L) ∧
    fullBlockLength n L k ≤ 144 * (k + 1) * L ∧
    fullReservedBits n L k ≤ 2 ^ (240 * (k + 1) * L) := by
  exact full_public_sample_resources n Δ edgeCount k γ
    (V39FullCutoff.fullPublicTests_all_large γ Δ n edgeCount hγ hΔ
      (Nat.pos_of_ne_zero (NeZero.ne n)) hnm hdeg hlarge)

#print axioms seedWidthNeZero
#print axioms fullQ₁NeZero
#print axioms fullQ₂NeZero
#print axioms fullSNeZero
#print axioms fourFullSNeZero
#print axioms fullSMinusThreeNeZero
#print axioms fullWNeZero
#print axioms fullQNeZero
#print axioms fullSampleProgram
#print axioms fullAlphabet
#print axioms fullDrawCap
#print axioms fullDrawExponent
#print axioms fullBlockLength
#print axioms fullReservedBits
#print axioms fullAlphabet_le
#print axioms fullDrawCap_le
#print axioms fullSampleProgram_maxAlphabet
#print axioms fullSampleProgram_maxDraws
#print axioms fullBlockLength_le
#print axioms fullReservedBits_le
#print axioms budget_exponents_linear
#print axioms full_sample_resources
#print axioms full_public_sample_resources
#print axioms full_promised_sample_resources

end V39FullSampleResources
