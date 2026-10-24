import Paper2.CodePreparationSize
import Paper2.CodeFallbackEntryJoin

/-! Scheduled clock of the actual compiler, sample assembly, interpreter-code
copy and fallback-dimension copies, including the handoff into interpretation.
Tape and the two interpreter cap words remain separate input obligations. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodePreparationExponent

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.SourceRecursiveNoSampling

theorem scheduled_clock_le_two_pow {n m : Nat} [NeZero n]
    (L Δ k : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    CodeFallbackEntryJoin.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k
      (sourceRows L (ParameterizedCanonicalSource.restorationDepth L)
        (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k)
      (sourceCols L (ParameterizedCanonicalSource.restorationDepth L)
        (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k) + 1 ≤
    2^((CodeGeneratorExponentPublic.exponentConstant+602)*(k+1)*L) := by
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
  have hover := CodePreparationSize.preparation_overhead_le _ _ A
    (scheduledCodes n m L Δ γ k).1 (scheduledCodes n m L Δ γ k).2
    hA (hd.1.trans hd') (hd.2.trans hd') (by omega) (by omega)
  have hcompiler := CodeSampleCompilerExponent.scheduled_clock_le_two_pow L Δ k γ hc
  have habs := CodeSampleCompilerExponent.absorb_overhead
    (CodeGeneratorExponentPublic.exponentConstant+301) T hT
  have he1 : (CodeGeneratorExponentPublic.exponentConstant+301)*(k+1)*L =
      (CodeGeneratorExponentPublic.exponentConstant+301)*T := by dsimp [T]; ring
  have he2 : (CodeGeneratorExponentPublic.exponentConstant+602)*(k+1)*L =
      ((CodeGeneratorExponentPublic.exponentConstant+301)+301)*T := by dsimp [T]; ring
  rw [he1] at hcompiler
  rw [he2]
  dsimp only [scheduledCodes] at hover
  dsimp only [CodeFallbackEntryJoin.clock, CodeSampleInterpreterJoin.clock]
  exact (show _ ≤ 2^((CodeGeneratorExponentPublic.exponentConstant+301)*T) +
      4096*A^2 by omega).trans habs

#print axioms scheduled_clock_le_two_pow

end Paper2.CodePreparationExponent
