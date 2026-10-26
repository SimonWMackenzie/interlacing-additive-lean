import Paper2.CodeGeneratorSampleResult
import Paper2.CodeGeneratorExponentScheduled
import Paper2.GeneratorPublicCap
import Paper2.FairBitCap

/-! Public clock for the actual compiler followed by the sample-code assembler.
The sample counts are exactly the prescribed source counts, not free inputs.
This does not claim the sampler, table evaluator, or reduction is complete. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeSampleCompilerExponent

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource
open Paper2.SourceRecursiveNoSampling

theorem transfer_assembly_le (mX mY A : Nat) (row col : Code)
    (hA : 1 ≤ A) (hx : mX ≤ A) (hy : mY ≤ A)
    (hr : codeSize row ≤ A) (hc : codeSize col ≤ A) :
    CodeGeneratorSampleTransfer.transferClock mX mY row col +
      64*(mX+mY+codeSize row+codeSize col+2)^2 + 2 ≤ 4096*A^2 := by
  have ht : CodeGeneratorSampleTransfer.transferClock mX mY row col ≤
      8*A+13 := by
    simp only [CodeGeneratorSampleTransfer.transferClock, encodeCode_length]
    omega
  have hs : mX+mY+codeSize row+codeSize col+2 ≤ 6*A := by omega
  have hs2 := Nat.pow_le_pow_left hs 2
  have ha2 : A ≤ A^2 := by nlinarith
  nlinarith only [ht, hs2, ha2, hA]

theorem absorb_overhead (C T : Nat) (hT : 1 ≤ T) :
    2^(C*T) + 4096*(2^(144*T))^2 ≤ 2^((C+301)*T) := by
  have hfirst : 2^(C*T) ≤ (2:Nat)^((C+300)*T) :=
    pow_le_pow_right₀ (by omega) (by nlinarith)
  have hsecond : 4096*(2^(144*T))^2 ≤ (2:Nat)^((C+300)*T) := by
    calc
      4096*(2^(144*T))^2 = (2:Nat)^(12+288*T) := by
        rw [← pow_mul]
        change (2:Nat)^12 * 2^(144*T*2) = 2^(12+288*T)
        rw [← pow_add]
        congr 1
        ring
      _ ≤ 2^((C+300)*T) := pow_le_pow_right₀ (by omega) (by nlinarith)
  calc
    2^(C*T) + 4096*(2^(144*T))^2 ≤
        2^((C+300)*T) + 2^((C+300)*T) := Nat.add_le_add hfirst hsecond
    _ = 2^((C+300)*T+1) := by rw [pow_succ]; omega
    _ ≤ 2^((C+301)*T) := pow_le_pow_right₀ (by omega) (by nlinarith)

theorem scheduled_clock_le_two_pow {n m : Nat} [NeZero n]
    (L Δ k : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    CodeGeneratorSampleJoin.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k
      (sourceRows L (ParameterizedCanonicalSource.restorationDepth L)
        (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k)
      (sourceCols L (ParameterizedCanonicalSource.restorationDepth L)
        (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k) ≤
    2^((CodeGeneratorExponentPublic.exponentConstant+301)*(k+1)*L) := by
  let T := (k+1)*L
  let A := 2^(144*T)
  have hL : 1 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    omega
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by decide)
  have hd := FairBitCap.scheduled_each_dimension_le L Δ γ hc k
  have hd' : 2^(29*(k+1)*L) ≤ A := by
    apply pow_le_pow_right₀ (by omega)
    dsimp [T]
    nlinarith
  have hsize := GeneratorPublicCap.scheduled_serialized_length_le_two_pow L Δ γ k hc
  simp only [encodeCode_length] at hsize
  have hexp : 2^(144*(k+1)*L) = A := by dsimp [A,T]; congr 1; ring
  rw [hexp] at hsize
  have hover := transfer_assembly_le _ _ A
    (scheduledCodes n m L Δ γ k).1 (scheduledCodes n m L Δ γ k).2
    hA (hd.1.trans hd') (hd.2.trans hd') (by omega) (by omega)
  have hraw := CodeGeneratorSampleResult.clock_output_sensitive n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k
      (sourceRows L (ParameterizedCanonicalSource.restorationDepth L)
        (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k)
      (sourceCols L (ParameterizedCanonicalSource.restorationDepth L)
        (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k)
  have hcompiler := CodeGeneratorExponentScheduled.scheduled_clock_le_two_pow L Δ k γ hc
  have habs := absorb_overhead CodeGeneratorExponentPublic.exponentConstant T hT
  dsimp only [scheduledCodes] at hover
  dsimp only at hraw
  have he1 : CodeGeneratorExponentPublic.exponentConstant*(k+1)*L =
      CodeGeneratorExponentPublic.exponentConstant*T := by dsimp [T]; ring
  have he2 : (CodeGeneratorExponentPublic.exponentConstant+301)*(k+1)*L =
      (CodeGeneratorExponentPublic.exponentConstant+301)*T := by dsimp [T]; ring
  rw [he1] at hcompiler
  rw [he2]
  exact (show _ ≤ 2^(CodeGeneratorExponentPublic.exponentConstant*T) + 4096*A^2 by
    omega).trans habs

#print axioms transfer_assembly_le
#print axioms absorb_overhead
#print axioms scheduled_clock_le_two_pow

end Paper2.CodeSampleCompilerExponent
