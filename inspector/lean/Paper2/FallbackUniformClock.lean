import Paper2.CodeFallbackScheduledClock
import Paper2.CodeFallbackAllOutcomes
import Paper2.CodePreparationExponent
import Paper2.CodeSamplerScheduledClock

/-! Unit 3, map item 6 (private): one public all-tape clock for the admitted
fixed program `CodeFallbackFullJoin.program` (compiler, sample assembly,
interpreter-code copy, fallback-dimension copies, capped interpreter, and on
exhaustion the fallback zero-table writer), instantiated at the exact checked
public schedule of frozen v12 Appendix D (`eq:generator-bound`, the
exhausted-cap paragraph). Same run objects as the admitted
`CodeFallbackAllOutcomes.every_tape_halts_with_source_outcome`; only its clock
expression is bounded here, by the admitted scheduled exponents. The success
branch here ends at the interpreter's observed sample word; the successful
table writer is not part of this program. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Paper2.FallbackUniformClock

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource

/-- The fixed uniform exponent. Every summand is a fixed constant of the
admitted finite machines: the compiler exponent, the interpreter exponent
and the interpreter's per-step output push bound. -/
noncomputable def uniformExponent : Nat :=
  CodeGeneratorExponentPublic.exponentConstant +
    CodeSamplerScheduledClock.exponentConstant +
    CodeTableFallback.interpreterPushBound + 852

theorem absorb (a b c d P T : Nat) (hT : 1 ≤ T) :
    2 ^ (a * T) + (P + 2) * 2 ^ (b * T) + 2 ^ (c * T) + 2 ^ (d * T) + 5 ≤
      2 ^ ((a + b + c + d + P + 6) * T) := by
  let K := a + b + c + d + P + 2
  let Y := 2 ^ (K * T)
  have hY : 1 ≤ Y := Nat.one_le_two_pow
  have mono : ∀ e, e ≤ K → 2 ^ (e * T) ≤ Y := fun e he =>
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (Nat.mul_le_mul_right T he)
  have ha := mono a (by dsimp [K]; omega)
  have hc := mono c (by dsimp [K]; omega)
  have hd := mono d (by dsimp [K]; omega)
  have hP : P + 2 ≤ 2 ^ ((P + 2) * T) := by
    have h1 : P + 2 < 2 ^ (P + 2) := Nat.lt_two_pow_self
    have h2 : 2 ^ (P + 2) ≤ 2 ^ ((P + 2) * T) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by nlinarith)
    omega
  have hb : (P + 2) * 2 ^ (b * T) ≤ Y := by
    calc
      (P + 2) * 2 ^ (b * T) ≤ 2 ^ ((P + 2) * T) * 2 ^ (b * T) :=
        Nat.mul_le_mul_right _ hP
      _ = 2 ^ ((P + 2 + b) * T) := by rw [← pow_add]; congr 1; ring
      _ ≤ Y := mono _ (by dsimp [K]; omega)
  have h16 : 16 * Y ≤ 2 ^ ((a + b + c + d + P + 6) * T) := by
    have hexp : 4 + K * T ≤ (a + b + c + d + P + 6) * T := by
      dsimp [K]; nlinarith
    calc
      16 * Y = 2 ^ (4 + K * T) := by
        dsimp [Y]; rw [pow_add]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) hexp
  omega

/-- The interpreter core is part of the interpreter clock. -/
theorem core_le_actualClock (root : Code) (B R N : Nat) :
    (codeSize root + 1) * CodeFullRepeatPublic.repeatStepCap root B R ≤
      CodeSamplerInterpreterPolynomial.actualClock root B R N := by
  unfold CodeSamplerInterpreterPolynomial.actualClock
  omega

/-- Pure arithmetic shape of the admitted all-outcomes clock. -/
theorem outcome_clock_le (prep A cs core P W : Nat) (hcore : core ≤ A) :
    prep + max (A + 2) (core + cs + P * core + W + 3 + 1) ≤
      (prep + 1) + (P + 2) * A + cs + W + 5 := by
  have hPc : P * core ≤ P * A := Nat.mul_le_mul_left P hcore
  have hexp : (P + 2) * A = P * A + 2 * A := by ring
  rw [hexp]
  omega

/-- The exact scheduled alphabet bound for the scheduled sample root, from
the admitted `CodeFullRunConsumer.scheduled_sample_code_alphabet_cap` at the
fixed public default activity/tails (the bound does not depend on them). -/
theorem scheduled_alphabet_bound {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ) (k : Nat) :
    (meaning (CodeFallbackSourceResult.sampleRoot n (LookupSeed.width L)
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L) (restorationWidth L)
      (coverWidth n m L Δ γ) k
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k))).maxAlphabet ≤
      CodeFullRunConsumer.scheduledM n m L Δ γ := by
  have hp : 0 < LookupSeed.width L := by unfold LookupSeed.width; positivity
  have hs : 4 ≤ SourceProfileParameters.width L := SourceProfiles.width_ge_four L
  have hq₂ : 0 < SourceProfileParameters.outerWidth L := by
    unfold SourceProfileParameters.outerWidth; positivity
  have hw : 0 < restorationWidth L := by
    unfold ParameterizedCanonicalSource.restorationWidth
      RestorationWidthScheduleScratch.width
    positivity
  have hQ : 0 < coverWidth n m L Δ γ := by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  exact CodeFullRunConsumer.scheduled_sample_code_alphabet_cap L Δ γ
    (fun _ _ => none)
    (RecursiveEntries.defaultTails (fun _ : Fin (LookupSeed.width L) => false)
      (⟨0, hp⟩ : Fin (LookupSeed.width L))
      ((⟨0, by omega⟩, .inl ⟨0, hn⟩) :
        SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      hq₂ hw hQ)
    k _ _

/-- The admitted all-outcomes clock expression at the exact checked
schedule is at most `2^(uniformExponent*(k+1)*L)`. -/
theorem scheduled_outcome_clock_le {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : Nat) :
    let p := LookupSeed.width L
    let s := SourceProfileParameters.width L
    let q₁ := SourceProfileParameters.width L - 2
    let q₂ := SourceProfileParameters.outerWidth L
    let w := restorationWidth L
    let Q := coverWidth n m L Δ γ
    let mX := sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k
    let mY := sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k
    let root := CodeFallbackSourceResult.sampleRoot n p s q₁ q₂ w Q k mX mY
    let B := Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ)
    let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
    let R := Paper2.rejectionAttemptCap N
    CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY +
      max ((codeSize root + 1) *
          CodeFullRepeatPublic.repeatStepCap root B R + N * (R * B) + 4)
        (CodeTableFallback.sourceFailureCap root B R mX mY + 1) ≤
      2 ^ (uniformExponent * (k + 1) * L) := by
  intro p s q₁ q₂ w Q mX mY root B N R
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  -- preparation (compiler + sample assembly + copies + handoff)
  have hprep := CodePreparationExponent.scheduled_clock_le_two_pow L Δ k γ hc
  -- capped interpreter, including the exact tape work N*(R*B)
  have hint := CodeSamplerScheduledClock.scheduled_clock_le_two_pow L Δ γ k hc
  dsimp only at hint
  -- root size
  have hroot := (CodeSamplerScheduledBounds.scheduled_parameters_le L Δ γ k hc).1
  -- fallback writer at the scheduled dimensions
  have hW := CodeFallbackScheduledClock.scheduled_writerBound_le L Δ γ hc k
  have hcore := core_le_actualClock root B R N
  have hshape := outcome_clock_le
    (CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY)
    (CodeSamplerInterpreterPolynomial.actualClock root B R N)
    (codeSize root)
    ((codeSize root + 1) * CodeFullRepeatPublic.repeatStepCap root B R)
    CodeTableFallback.interpreterPushBound
    (EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound mX mY 1)
    hcore
  have hab := absorb (CodeGeneratorExponentPublic.exponentConstant + 602)
    CodeSamplerScheduledClock.exponentConstant 180 64
    CodeTableFallback.interpreterPushBound T hT
  have e1 : (CodeGeneratorExponentPublic.exponentConstant + 602) * (k + 1) * L =
      (CodeGeneratorExponentPublic.exponentConstant + 602) * T := by
    dsimp [T]; ring
  have e2 : CodeSamplerScheduledClock.exponentConstant * (k + 1) * L =
      CodeSamplerScheduledClock.exponentConstant * T := by dsimp [T]; ring
  have e3 : 180 * (k + 1) * L = 180 * T := by dsimp [T]; ring
  have e4 : 64 * (k + 1) * L = 64 * T := by dsimp [T]; ring
  have e5 : uniformExponent * (k + 1) * L =
      ((CodeGeneratorExponentPublic.exponentConstant + 602) +
        CodeSamplerScheduledClock.exponentConstant + 180 + 64 +
        CodeTableFallback.interpreterPushBound + 6) * T := by
    dsimp [T, uniformExponent]; ring
  rw [e1] at hprep
  rw [e2] at hint
  rw [e3] at hroot
  rw [e4] at hW
  rw [e5]
  have hint' : CodeSamplerInterpreterPolynomial.actualClock root B R N ≤
      2 ^ (CodeSamplerScheduledClock.exponentConstant * T) := hint
  have hroot' : codeSize root ≤ 2 ^ (180 * T) := hroot
  have hmulA := Nat.mul_le_mul_left (CodeTableFallback.interpreterPushBound + 2) hint'
  have hunfold : CodeTableFallback.sourceFailureCap root B R mX mY =
      (codeSize root + 1) * CodeFullRepeatPublic.repeatStepCap root B R +
        codeSize root +
        CodeTableFallback.interpreterPushBound *
          ((codeSize root + 1) * CodeFullRepeatPublic.repeatStepCap root B R) +
        EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound mX mY 1 + 3 := rfl
  have hact : (codeSize root + 1) * CodeFullRepeatPublic.repeatStepCap root B R +
      N * (R * B) + 4 = CodeSamplerInterpreterPolynomial.actualClock root B R N + 2 := by
    unfold CodeSamplerInterpreterPolynomial.actualClock; omega
  rw [hunfold, hact]
  calc
    _ ≤ (CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY + 1) +
        (CodeTableFallback.interpreterPushBound + 2) *
          CodeSamplerInterpreterPolynomial.actualClock root B R N +
        codeSize root +
        EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound mX mY 1 + 5 := hshape
    _ ≤ 2 ^ ((CodeGeneratorExponentPublic.exponentConstant + 602) * T) +
        (CodeTableFallback.interpreterPushBound + 2) *
          2 ^ (CodeSamplerScheduledClock.exponentConstant * T) +
        2 ^ (180 * T) + 2 ^ (64 * T) + 5 := by
      have h1 : CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY + 1 ≤
          2 ^ ((CodeGeneratorExponentPublic.exponentConstant + 602) * T) := hprep
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add h1 hmulA) hroot') hW) le_rfl
    _ ≤ _ := hab

#print axioms absorb
#print axioms core_le_actualClock
#print axioms outcome_clock_le
#print axioms scheduled_alphabet_bound
#print axioms scheduled_outcome_clock_le

end Paper2.FallbackUniformClock
