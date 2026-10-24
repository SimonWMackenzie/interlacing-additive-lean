import CurrentAdditive.V39PhysicalSampleBudget
import CurrentAdditive.V39FullCodeConstructor

/-! A single closed exponent bounds the actual constructor/interpreter
composition on every reserved tape under the manuscript's literal schedule. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39PhysicalSample
noncomputable section

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open EthInapproximability.CurrentPaper
open V38Schedule V39PublicSchedule V39FullSampleResources
open V39DeadTaggedCompiler V39RecursiveGenerator V38OneStep

def fullPhysicalExponent : ℕ := V39CurrentCodeConstructor.fullConstructorExponent +
  Nat.clog 2 RoundedCodeOutput.publishedCoefficient + 635

theorem full_code_size_le (n : ℕ) (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2^L) (htest : FullTests c L edgeCount δv ζ) :
    codeSize (V39CurrentCodeConstructor.fullSampleCode n L k) ≤ 2^(267*((k+1)*L)) := by
  have hL : 16 ≤ L := htest.2.2.1
  obtain ⟨hnE,hp,hq₁,hq₂,hs,hw,hQ⟩ := full_widths_le_pow n L hL hn
  have hR := V39CurrentCodeConstructor.sampleCode_size_le_exp n (seedWidth L)
    (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L)
    (fullWidthExponent L) (fullSampleExponent L k) k (sampleSide L k)
    hnE hp hq₁ hq₂ hs hw hQ (full_sampleSide_le_pow c L edgeCount k δv ζ htest)
  apply hR.trans
  apply Nat.pow_le_pow_right (by decide)
  have hT : 5 ≤ (k+1)*L := by nlinarith
  have h10 : 16*L+10 ≤ 26*L := by omega
  have hm := Nat.mul_le_mul_left (9*(k+1)) h10
  unfold fullWidthExponent fullSampleExponent
  nlinarith

theorem dyadic_blockLength_le (n : ℕ) (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2^L) (htest : FullTests c L edgeCount δv ζ) :
    publicBits (fullAlphabet n L) (2^fullDrawExponent L k) ≤ 144*((k+1)*L) := by
  exact (publicBits_le_expSum (fullAlphabet n L) (2^fullDrawExponent L k)
    (fullWidthExponent L) (fullDrawExponent L k)
    (fullAlphabet_le n L htest.2.2.1 hn) le_rfl).trans
    (by simpa only [Nat.mul_assoc] using (budget_exponents_linear L k htest.2.2.1).2.1)

theorem full_physical_clock_le (n : ℕ) (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2^L) (htest : FullTests c L edgeCount δv ζ) :
    clock n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L)
      k (sampleSide L k) (publicBits (fullAlphabet n L) (2^fullDrawExponent L k))
      (2^fullDrawExponent L k) ≤ 2^(fullPhysicalExponent*((k+1)*L)) := by
  let T := (k+1)*L
  let R := codeSize (V39CurrentCodeConstructor.fullSampleCode n L k)
  let b := publicBits (fullAlphabet n L) (2^fullDrawExponent L k)
  let N := 2^fullDrawExponent L k
  let C := Nat.clog 2 RoundedCodeOutput.publishedCoefficient
  have hL : 16 ≤ L := htest.2.2.1
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hctor := V39CurrentCodeConstructor.full_clock_le_pow n c L edgeCount k δv ζ hn htest
  have hR : R ≤ 2^(267*T) := full_code_size_le n c L edgeCount k δv ζ hn htest
  have hb : b ≤ 144*T := dyadic_blockLength_le n c L edgeCount k δv ζ hn htest
  have hb3 : b+3 ≤ 2^(267*T) := by
    have hsmall : b+3 ≤ 147*T := by omega
    have hexp : 147*T ≤ 2^(147*T) := Nat.lt_two_pow_self.le
    exact hsmall.trans (hexp.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsum : R+b+3 ≤ 2^(268*T) := by
    have hsum' : R+(b+3) ≤ 2^(267*T)+2^(267*T) := Nat.add_le_add hR hb3
    have hdouble : 2^(267*T)+2^(267*T) = 2^(267*T+1) := by rw [pow_succ]; omega
    rw [hdouble] at hsum'
    have hsum'' : R+b+3 ≤ 2^(267*T+1) := by simpa only [Nat.add_assoc] using hsum'
    exact hsum''.trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hN : N ≤ 2^(96*T) :=
    Nat.pow_le_pow_right (by decide) (by simpa only [T,Nat.mul_assoc] using (budget_exponents_linear L k hL).1)
  have hN1 : N+1 ≤ 2^(97*T) := by
    have hone : 1 ≤ 2^(96*T) := Nat.one_le_two_pow
    have hdouble : 2^(96*T)+2^(96*T) = 2^(96*T+1) := by rw [pow_succ]; omega
    have hs : N+1 ≤ 2^(96*T)+2^(96*T) := Nat.add_le_add hN hone
    rw [hdouble] at hs
    exact hs.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hcoef : RoundedCodeOutput.publishedCoefficient ≤ 2^(C*T) := by
    exact (Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide) (by have := Nat.mul_le_mul_left C hT; omega))
  have hrun : RoundedCodeOutput.publishedCoefficient*(N+1)*(R+b+3)^2 ≤ 2^((C+633)*T) := by
    calc
      RoundedCodeOutput.publishedCoefficient*(N+1)*(R+b+3)^2 ≤
          2^(C*T)*2^(97*T)*(2^(268*T))^2 := by gcongr
      _ = 2^((C+633)*T) := by rw [← pow_mul,← pow_add,← pow_add]; congr 1; ring
  let D := V39CurrentCodeConstructor.fullConstructorExponent+C+633
  have hctor' : V39CurrentCodeConstructor.fullCompilerClock n L k ≤ 2^(D*T) := by
    apply hctor.trans
    apply Nat.pow_le_pow_right (by decide)
    have hm := Nat.mul_le_mul_right T
      (show V39CurrentCodeConstructor.fullConstructorExponent ≤ D by dsimp [D]; omega)
    simpa only [T,Nat.mul_assoc] using hm
  have hrun' : RoundedCodeOutput.publishedCoefficient*(N+1)*(R+b+3)^2 ≤ 2^(D*T) :=
    hrun.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right T (by dsimp [D]; omega)))
  have hone : 1 ≤ 2^(D*T) := Nat.one_le_two_pow
  have hclock : clock n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L)
      k (sampleSide L k) b N ≤ 2^(D*T)+2^(D*T)+2^(D*T) := by
    change V39CurrentCodeConstructor.fullCompilerClock n L k +
      RoundedCodeOutput.publishedCoefficient*(N+1)*(R+b+3)^2+1 ≤ _
    omega
  apply hclock.trans
  calc
    2^(D*T)+2^(D*T)+2^(D*T) ≤ 2^(D*T+2) := by rw [pow_add]; norm_num; omega
    _ ≤ 2^(fullPhysicalExponent*T) := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp [fullPhysicalExponent,D,C]
      nlinarith

#print axioms full_code_size_le
#print axioms dyadic_blockLength_le
#print axioms full_physical_clock_le

end
end CurrentAdditive.V39PhysicalSample
