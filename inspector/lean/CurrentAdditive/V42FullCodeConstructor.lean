import CurrentAdditive.V39CurrentCodeConstructorBounds
import CurrentAdditive.V42RuntimeSchedule


/-! Literal current public-schedule specialization of the actual constructor.
The accepted all-large source cutoff supplies every width and sample bound. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V42CodeConstructor

open V42RuntimeSchedule
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open V39DeadTaggedCompiler V39CurrentCodeConstructor

def fullSampleCode (n L k : Nat) : Code :=
  deadSampleCode n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
    (fullW L) (fullQ L) k (sampleSide L k)

noncomputable def fullCompilerClock (n L k : Nat) : Nat :=
  V39DeadSampleJoin.clock n (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
    (fullW L) (fullQ L) k (sampleSide L k) (sampleSide L k)

def fullConstructorExponent : Nat :=
  26*(V39DeadCodeExponent.exponentConstant+18)+93

theorem full_clock_le_pow (n : Nat) (c : ℚ) (L edgeCount k : Nat) (δv ζ : ℚ)
    (hn : n ≤ 2^L) (htest : FullTests c L edgeCount δv ζ) :
    fullCompilerClock n L k ≤ 2^(fullConstructorExponent*(k+1)*L) := by
  have hL : 16 ≤ L := htest.1.2.2.1
  obtain ⟨hnE,hp,hq₁,hq₂,hs,hw,hQ⟩ := full_widths_le_pow n L hn htest.2
  have hm := full_sampleSide_le_pow L k htest.2
  have hs3 : 3 ≤ fullS L := by have := fullS_ge_256 L; omega
  have hc := sampleClock_le_two_pow n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (fullWidthExponent L) (fullSampleExponent L k)
    k (sampleSide L k) hs3 hnE hp hq₁ hq₂ hs hw hQ hm
  apply hc.trans
  apply pow_le_pow_right₀ (by decide)
  unfold fullWidthExponent fullSampleExponent fullConstructorExponent
  have h10 : 16*L+10 ≤ 26*L := by omega
  have hmul := Nat.mul_le_mul_left
    ((V39DeadCodeExponent.exponentConstant+18)*(k+1)) h10
  have hunit : 1 ≤ (k+1)*L := by nlinarith
  nlinarith

#print axioms full_clock_le_pow
end CurrentAdditive.V42CodeConstructor
