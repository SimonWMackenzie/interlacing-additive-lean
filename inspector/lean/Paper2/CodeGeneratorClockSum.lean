import Paper2.CodeGeneratorStepGrowth
import Paper2.CodeGeneratorComplete
import Paper2.GeneratorPublicCap

/-! Sum the *actual* fixed-controller round clocks, with no runtime
recurrence hidden in the induction. The uniform per-round cap is a separate
arithmetic premise, later discharged from the scheduled source-size cap. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

namespace Paper2.CodeGeneratorClockSum

open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.GeneratorSerialization
open Paper2.CodeRecursiveLoop Paper2.CodeRecursiveRound
open Paper2.GeneratorSize

theorem roundPoly_mono (n s q₁ q₂ w Q r r' c c' : Nat)
    (hr : r ≤ r') (hc : c ≤ c') :
    CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q r c ≤
      CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q r' c' := by
  dsimp [CodeGeneratorStepGrowth.roundPoly,
    CodeRecursiveStepClock.polynomialClock,
    CodeRecursiveStepClock.graphCap,
    CodeRecursiveStepClock.taggedCap,
    TaggedCompiler.polynomialClock]
  gcongr

theorem totalClock_le_uniform (n s q₁ q₂ w Q : Nat)
    (row col : Code) (k P : Nat)
    (hround : ∀ j < k,
      let pair := recursiveCodes n s q₁ q₂ w Q row col j
      CodeRecursiveRound.clock n s q₁ q₂ w Q pair.1 pair.2 ≤ P) :
    totalClock n s q₁ q₂ w Q row col k ≤ 1 + k*(P+1) := by
  induction k generalizing row col with
  | zero => simp [totalClock]
  | succ k ih =>
      let row₁ := CodeRecursiveRow.rowCode q₁ q₂ s w Q col
      let col₁ := CodeRecursiveColumn.columnCode n s q₁ q₂ w Q row
      have h0 : CodeRecursiveRound.clock n s q₁ q₂ w Q row col ≤ P := by
        simpa only [recursiveCodes] using hround 0 (by omega)
      have htail : ∀ j < k,
          let pair := recursiveCodes n s q₁ q₂ w Q row₁ col₁ j
          CodeRecursiveRound.clock n s q₁ q₂ w Q pair.1 pair.2 ≤ P := by
        intro j hj
        have h := hround (j+1) (by omega)
        simpa only [row₁, col₁, CodeRecursiveLoop.recursiveCodes_shift]
          using h
      have ht := ih row₁ col₁ htail
      dsimp [totalClock]
      dsimp [row₁, col₁] at ht
      rw [Nat.succ_mul]
      omega

theorem totalClock_le_code_cap (n s q₁ q₂ w Q : Nat)
    (row col : Code) (k A : Nat) (hs : 3 ≤ s)
    (hcap : ∀ j < k,
      let pair := recursiveCodes n s q₁ q₂ w Q row col j
      codeSize pair.1 + codeSize pair.2 + 1 ≤ A) :
    totalClock n s q₁ q₂ w Q row col k ≤
      1 + k*(CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q A A + 1) := by
  apply totalClock_le_uniform
  intro j hj
  let pair := recursiveCodes n s q₁ q₂ w Q row col j
  have hc := hcap j hj
  have hr : codeSize pair.1 ≤ A := by dsimp [pair] at *; omega
  have hc' : codeSize pair.2 ≤ A := by dsimp [pair] at *; omega
  exact (CodeGeneratorStepGrowth.round_clock_le_poly
    n s q₁ q₂ w Q pair.1 pair.2 hs).trans
    (roundPoly_mono n s q₁ q₂ w Q
      (codeSize pair.1) A (codeSize pair.2) A hr hc')

theorem totalClock_seed_le_cap (M n p s q₁ q₂ w Q k : Nat)
    (hM : 512 ≤ M) (hn : n ≤ M) (hp : p ≤ M)
    (hs : 3 ≤ s) (hsM : s ≤ M) (hq₁ : q₁ ≤ M)
    (hq₂ : q₂ ≤ M) (hw : w ≤ M) (hQ : Q ≤ M) :
    totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k ≤
      1 + k*(CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q
        ((M+1)^(18*(k+1))) ((M+1)^(18*(k+1))) + 1) := by
  apply totalClock_le_code_cap n s q₁ q₂ w Q
    (copies p .bit) (.ticket p) k ((M+1)^(18*(k+1))) hs
  intro j hj
  have hsize := seed_total_le_cap M n p s q₁ q₂ w Q j
    hM hn hp hsM hq₁ hq₂ hw hQ
  have hpow : (M+1)^(18*(j+1)) ≤ (M+1)^(18*(k+1)) :=
    pow_le_pow_right₀ (by omega) (by omega)
  exact hsize.trans hpow

def publicCompilerClock (L k : Nat) : Nat :=
  let M := GeneratorPublicCap.publicCap L
  let A := (M+1)^(18*(k+1))
  6*M+18 + 1 + k*(CodeGeneratorStepGrowth.roundPoly
    M M M M M M A A + 1)

theorem scheduled_compiler_clock_le_public
    {n m : Nat} [NeZero n] (L Δ k : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    CodeGeneratorComplete.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k ≤
    publicCompilerClock L k := by
  let M := GeneratorPublicCap.publicCap L
  let p := LookupSeed.width L
  let s := SourceProfileParameters.width L
  let q₁ := SourceProfileParameters.width L - 2
  let q₂ := SourceProfileParameters.outerWidth L
  let w := ParameterizedCanonicalSource.restorationWidth L
  let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
  let A := (M+1)^(18*(k+1))
  obtain ⟨hM, hn, hp, hsM, hq₁, hq₂, hw, hQ⟩ :=
    GeneratorPublicCap.scheduled_scalars_le_publicCap L Δ γ hc
  have hs : 3 ≤ s := by
    dsimp [s]
    have h := SourceProfileParameters.width_admissible L
    omega
  have hloop := totalClock_seed_le_cap M n p s q₁ q₂ w Q k
    hM hn hp hs hsM hq₁ hq₂ hw hQ
  change totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k ≤
    1+k*(CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q A A + 1)
    at hloop
  have hpolyAll : CodeGeneratorStepGrowth.roundPoly
      n s q₁ q₂ w Q A A ≤
      CodeGeneratorStepGrowth.roundPoly M M M M M M A A := by
    dsimp [CodeGeneratorStepGrowth.roundPoly,
      CodeRecursiveStepClock.polynomialClock,
      CodeRecursiveStepClock.graphCap,
      CodeRecursiveStepClock.taggedCap,
      TaggedCompiler.polynomialClock]
    gcongr
  have hmul := Nat.mul_le_mul_left k
    (Nat.add_le_add_right hpolyAll 1)
  have hseed : CodeRecursiveSeedJoin.clock p ≤ 6*M+17 := by
    dsimp [CodeRecursiveSeedJoin.clock, CodeRecursiveSeedJoin.b₁]
    omega
  change CodeRecursiveSeedJoin.clock p +
      totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k + 1 ≤
    6*M+18+1+k*(CodeGeneratorStepGrowth.roundPoly M M M M M M A A + 1)
  omega

#print axioms totalClock_le_uniform
#print axioms totalClock_le_code_cap
#print axioms totalClock_seed_le_cap
#print axioms scheduled_compiler_clock_le_public

end Paper2.CodeGeneratorClockSum
