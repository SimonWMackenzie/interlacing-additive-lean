import CurrentAdditive.QuarticCompilerClock
import Paper2.CodeSampleCompilerExponent

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticAssemblyClock

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.SourceRecursiveNoSampling
open Paper2.CodeSampleCompilerExponent
open CurrentAdditive.RandomizedSchedule

theorem assembly_clock27 {n m : Nat} [NeZero n]
    (L Δ k : Nat) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    CodeGeneratorSampleJoin.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k) ≤
    2^((CodeGeneratorExponentPublic.exponentConstant+301)*(k+1)*L) := by
  let T := (k+1)*L
  let A := 2^(144*T)
  have hL : 1 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    omega
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (by decide)
  have hd := QuarticClockCaps.dims_cap27 L Δ γ hc k
  have hd' : 2^(29*(k+1)*L) ≤ A := by
    apply pow_le_pow_right₀ (by omega)
    dsimp [T]
    nlinarith
  have hsize := QuarticClockCaps.code_size27 L Δ γ hc k

  have hexp : 2^(144*(k+1)*L) = A := by dsimp [A,T]; congr 1; ring
  rw [hexp] at hsize
  have hover := transfer_assembly_le _ _ A
    (seedRecursiveCodes n (LookupSeed.width L) (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L) (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k).1 (seedRecursiveCodes n (LookupSeed.width L) (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L) (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k).2
    hA (hd.1.trans hd') (hd.2.trans hd') (by omega) (by omega)
  have hraw := CodeGeneratorSampleResult.clock_output_sensitive n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
  have hcompiler := QuarticCompilerClock.compiler_clock_pow27 L Δ k γ hc
  have habs := absorb_overhead CodeGeneratorExponentPublic.exponentConstant T hT
  dsimp only at hraw
  have he1 : CodeGeneratorExponentPublic.exponentConstant*(k+1)*L =
      CodeGeneratorExponentPublic.exponentConstant*T := by dsimp [T]; ring
  have he2 : (CodeGeneratorExponentPublic.exponentConstant+301)*(k+1)*L =
      (CodeGeneratorExponentPublic.exponentConstant+301)*T := by dsimp [T]; ring
  rw [he1] at hcompiler
  rw [he2]
  exact (show _ ≤ 2^(CodeGeneratorExponentPublic.exponentConstant*T) + 4096*A^2 by
    omega).trans habs


end Paper2.CurrentAdditive.QuarticAssemblyClock

#print axioms Paper2.CurrentAdditive.QuarticAssemblyClock.assembly_clock27
